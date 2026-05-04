/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Mathlib.Lean.Elab.Options
public meta import Mathlib.Lean.Name
public meta import Lean.Elab.BuiltinCommand

/-!
# Scope manipulation tools

This module provides utilities for fully capturing the effectful parts of the current scope
(namespaces, open declarations, options, etc.) and transporting it between modules. Specifically,
it provides `#scope`, which reifies the semantically-relevant parts of the current scope into
portable syntax capturing the current scope that may be moved between files.

This is not intended to capture `section` behavior, nor is it intended to be used for user-friendly
visibility into the current scope structure. The reified scope specification is primarily intended
to be easy to act on with metaprogramming automation. In this sense it is not trying to replace
`#where`.

## TODO

- `#scope! (<scope specification>)` for effecting the given scope specification
- `#scope? (<scope specification>)` for producing appropriate Lean commands to integrate the given
  full scope specification with the current scope
-/

/- Note: some declarations are marked `private` despite already living in private sections. These
should stay private or be carefully considered even if the API becomes public. -/

open Lean Meta Elab Command

meta section

namespace Mathlib.Tactic.Scope

public section parsers

/-! The "inlinable" parsers in this section exist to enable syntax quotations, which help with
constructing and processing these later. -/

/-- An unambiguous rendering of the result of `open ns renaming from → to, ...` and
`open ns (id₁ id₂ ...)`, which both do not record `ns`, but only the mapping from unresolved
identifier to fully resolved name(s). -/
syntax reifiedExplicitOpenStx := ident " → " ident
syntax reifiedSimpleOpenIdent := &"@" noWs ident
syntax reifiedSimpleOpenHidingStx := &"@" noWs ident " hiding " ident*
syntax reifiedOpenDecl := ppSpace colGt
  (reifiedSimpleOpenIdent <|> ("(" reifiedSimpleOpenHidingStx <|> reifiedExplicitOpenStx ")"))
/-- Renders the result of `open` by prefixing identifiers with `@` to indicate that this syntax
only renders fully-resolved namespaces. Surrounded by `()` when `hiding` is present. Uses `→` to
render the mappings produced by `open ns renaming from → to, ...` and
`open ns (id₁ id₂ ...)`. -/
syntax reifiedOpenStx := withPosition(
  atomic("open" notFollowedBy("scoped")) ppIndent(reifiedOpenDecl*))

/-- Renders the open scopes that are not accounted for by generic `open`s. Prefixes identifiers
with `@` to show the fully-resolved name. -/
syntax reifiedOpenScopedStx := withPosition("open " "scoped"
  ppIndent((ppSpace colGt reifiedSimpleOpenIdent)*))

-- Parser of convenience, since we handle these together.
-- TODO: technically this may be influenced by open scopes.
-- It needs to incorporate that in the parser.
syntax reifiedVarStx := Parser.Command.variable
  (ppLine Parser.Command.include)?
  (ppLine Parser.Command.omit)?

syntax reifiedOptionKeyValue := ppSpace colGt ident ppSpace optionValue
/-- `set_options key₁ val₁, key₂ val₂, ...` renders the options set in a single line. -/
syntax reifiedSetOptionsStx := withPosition("set_options " ppIndent(reifiedOptionKeyValue,*))

/--
A scope specification of the form
```
(@[expose])? (public)? (noncomputable)? (section)? (scope)?
  (universe ...)?
  (namespace ...)?
  (open @id₁ @id₂ ...)?
  (open scoped @id₁ @id₂ ...)?
  (set_options key₁ val₁, key₂ val₂ ...)?
  (variable ...)?
  (include ...)?
  (omit ...)?
```
Notice the differences from typical scope-related syntax, especially in the usage of `@` in
identifiers for `open` and the use of `set_options` instead of `set_option`.

Note also that this is intended to reify semantic and instantaneous aspects of a given scope for
transportation purposes, and is *not* intended to reify the entire scope stack. This means that
the effects of `section`s and local scopes are not accounted for here.

This syntax is not a command itself, but is used within other commands, such as `#scope`.
-/
syntax scopeStx := Parser.Command.sectionHeader &"scope"
  (ppLine colGt Parser.Command.universe)?
  (ppLine colGt Parser.Command.namespace)?
  atomic((ppLine colGt reifiedOpenStx)?)
  (ppLine colGt reifiedOpenScopedStx)?
  (ppLine colGt reifiedSetOptionsStx)?
  (ppLine colGt reifiedVarStx)?

end parsers

section header

open Parser.Command

/-- Isolates the part of a `Scope` that contains `SectionHeader` information. -/
@[inline] def reifySectionHeader {m} [Monad m] [MonadQuotation m] :
    Scope → m (TSyntax ``sectionHeader)
  | { isPublic, isMeta, isNoncomputable, attrs .. } => do
    -- Currently `attrs` holds at most `expose`, but we match for future-proofing.
    let exposeTk? := attrs.find? fun stx => match stx.raw with
      | `(Parser.Term.attrInstance| expose) => true
      | _ => false
    -- This is a hack to exploit antiquotations. `$[$foo%$tk]?` yields `foo` iff `tk.isSome`.
    let r ← getRef
    letI toDummyOptional? (b : Bool) : Option Syntax :=
      if b then some r else none
    let pubTk    := toDummyOptional? isPublic
    let metaTk   := toDummyOptional? isMeta
    let ncTk     := toDummyOptional? isNoncomputable
    `(sectionHeader|
      $[@[expose%$exposeTk?]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?)

/-- Applies a `sectionHeader` syntax of the form `(@[expose])? (public)? (noncomputable)? (meta)?`
to the current scope, overwriting the values (rather than merging them). For instance, if `public`
is absent, the resulting scope now has `isPublic := false`, even if it was `true` before. -/
def unreifySectionHeader : TSyntax ``Parser.Command.sectionHeader → CommandElabM Unit
  | `(Parser.Command.sectionHeader|
      $[@[expose%$exposeTk]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?) => do
      let isPublic := pubTk.isSome
      let isMeta := metaTk.isSome
      -- `sectionHeader` parses `expose` directly, not as an `attrInstance`.
      let attrs : List (TSyntax ``Parser.Term.attrInstance) ←
        if let some exposeTk := exposeTk then
          pure [← withRef exposeTk `(Parser.Term.attrInstance| expose)] else pure []
      let isNoncomputable := ncTk.isSome
      modifyScope fun s => { s with isPublic, isMeta, isNoncomputable, attrs }
  | _ => throwUnsupportedSyntax

end header

section openDecls

/-- Lean may duplicate open declarations occasionally due to leanprover/lean4#13353. This function
deduplicates exactly-duplicated `OpenDecl`s by removing the later occurrences. -/
@[inline] private def deduplicateOpenDecls (openDecls : List OpenDecl) : List OpenDecl :=
  /- Note that the innermost openDecls come first and affect name resolution first due to
  `eraseDups` affecting resolved ids by first occurrence (corresponding to later occurrences in
  openDecls) -/
  -- TODO: find something more efficient, which means basically just about anything else.
  openDecls.reverse.eraseDups.reverse

/-- Convert `OpenDecl`s into reified `open @id₁ @id₂ ...` syntax. -/
def reifyOpenDecls {m} [Monad m] [MonadQuotation m] (openDecls : List OpenDecl) (dedup := true) :
    m (Option (TSyntax ``reifiedOpenStx)) := do
  let openDecls := if dedup then deduplicateOpenDecls openDecls else openDecls
  -- Note that the last element of `openDecls` becomes the first element of `reifiedOpens`,
  -- since the outermost `OpenDecl` is the most recent.
  let mut reifiedOpens := []
  for openDecl in openDecls do
    let reified ← match openDecl with
      | .explicit id declName =>
        `(reifiedOpenDecl| ($(mkIdent id) → $(mkIdent declName)))
      | .simple ns except =>
        if except.isEmpty then `(reifiedOpenDecl| @$(mkIdent ns)) else
          let except := except.toArray.map mkIdent
          `(reifiedOpenDecl| (@$(mkIdent ns) hiding $except*))
    reifiedOpens := reified :: reifiedOpens
  if reifiedOpens.isEmpty then return none else
    `(reifiedOpenStx| open $reifiedOpens.toArray*)

/-- Activates scopes associated with an `OpenDecl` as `open` would when creating that `OpenDecl`. -/
def _root_.Lean.OpenDecl.activate {m : Type → Type}
    [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] :
    OpenDecl → m Unit
  | .simple ns _  => activateScoped ns
  | .explicit _ _ => pure () -- `open` never activates scopes when creating these

-- TODO: it's possible we should register namespaces if they don't exist.
/-- Turns reified syntax for a single `open` such as `@foo.bar` into an `OpenDecl`, activating
scopes as `open` would if `activateScopes := true` (the default). -/
def unreifyOpenDecl (openDecl : TSyntax ``reifiedOpenDecl) (activateScopes := true) :
    CommandElabM OpenDecl :=
  match openDecl with
  | `(reifiedOpenDecl| @$id) => do
    if activateScopes then activateScoped id.getId
    return .simple id.getId []
  | `(reifiedOpenDecl| (@$id hiding $hidden*)) => do
    if activateScopes then activateScoped id.getId
    return .simple id.getId <| (hidden.map (·.getId)).toList
  | `(reifiedOpenDecl| ($id → $decl)) =>
    -- `open` never activates scopes in these cases. See `elabOpenDecl`.
    return .explicit id.getId decl.getId
  | _ => throwUnsupportedSyntax

/-- Turns reified syntax for `open @id ...` such as `open @foo.bar ...` into `OpenDecl`s
(activating scopes as appropriate) and modifies the current scope to use exactly those open
declarations (erasing whatever open declarations were present before). Note that the resulting
`openDecls` do not depend on the original `openDecls` or original scope in any way. -/
def unreifyOpenDecls (openDeclsStx : TSyntaxArray ``reifiedOpenDecl) : CommandElabM Unit := do
  let openDecls ← openDeclsStx.foldlM (init := []) fun openDecls openDeclStx =>
    return (← unreifyOpenDecl openDeclStx) :: openDecls
  modifyScope fun s => { s with openDecls }

section openScoped

/-- `current.minus without` yields a `NameSet` containing the elements of `current` not present in
`without`. -/
@[inline] private def _root_.Lean.NameSet.minus (current without : NameSet) : NameSet :=
  if without.isEmpty then current else current.filter (!without.contains ·)

/-- An extension we can trust to always be present, whose active scopes reflect the result of
`open`s and are likely not altered separately from the rest of the scoped environment extensions by
some metaprogram. -/
@[inline] private def referenceScopedExt := Parser.parserExtension.ext

/-- The active scopes in scoped environment extensions, as determined by a reference
extension. Does not account for alterations to individual environment extensions that may
be performed by some metaprograms. -/
def _root_.Lean.Environment.activeScopes (env : Environment) : NameSet :=
  match referenceScopedExt.getState (asyncMode := .local) env |>.stateStack with
  | s :: _ => s.activeScopes
  | _ => {}

/-- The active scopes in scoped env extensions that are *not* implied by the
given namespace and open decls (as determined by the active scopes in a reference environment
extension). These extra active scopes are typically produced by `open scoped`. See also
`Lean.Elab.Command.extraScoped : CommandElabM NameSet`. -/
protected def _root_.Lean.Environment.extraActiveScopes (env : Environment)
    (currNamespace : Name) (openDecls : List OpenDecl) : NameSet := Id.run do
  -- Note that each `open` that adds `.simple` activates the corresponding scopes.
  let impliedScopes : NameSet := openDecls.foldl (init := {}) fun
    | acc, .simple ns _ => if ns.isAnonymous then acc else acc.insert ns
    | acc, _ => acc
  -- When `namespace ns` happened (or whatever sequence of `namespace`s), `addScopes` traversed all
  -- prefixes of `ns`. So we expect those to be there.
  -- Note that `addScope` in `elabNamespace` does not add to the open decls, so this is necessary.
  let impliedScopes := currNamespace.foldrPrefix (init := impliedScopes) fun n acc =>
    if n.isAnonymous then acc else acc.insert n
  return env.activeScopes.minus impliedScopes

/-- The active scopes in scoped env extensions that are *not* implied by the current namespace and
open decls (as determined by the active scopes in a reference environment extension). These extra
active scopes are typically produced by `open scoped`. -/
def _root_.Lean.Elab.Command.extraActiveScopes : CommandElabM NameSet :=
  return (← getEnv).extraActiveScopes (← getCurrNamespace) (← getOpenDecls)

/-- Converts the extra active scopes into reified `open scoped` syntax. -/
def reifyExtraOpenScopes : CommandElabM (Option (TSyntax ``reifiedOpenScopedStx)) := do
  let extra ← extraActiveScopes
  if extra.isEmpty then return none
  let extraScoped ← extra.toArray.mapM fun n => `(reifiedSimpleOpenIdent| @$(mkIdent n))
  `(reifiedOpenScopedStx| open scoped $extraScoped*)

/-- Directly activates the scopes in reified `open scoped @id₁ @id₂ ...` syntax. -/
def unreifyOpenScopedDecls : TSyntax ``reifiedOpenScopedStx → CommandElabM Unit
  | `(reifiedOpenScopedStx| open scoped $[@$openScopedDecls:ident]*) => do
    for openScoped in openScopedDecls do
      activateScoped openScoped.getId.eraseMacroScopes
  | _ => throwUnsupportedSyntax

end openScoped

end openDecls

section setOption

/- Note: lakefile options are commingled in the base scope with options set in the module, so it is
not easy to split them up. Further, including the lakefile options is arguably better for
transportation between libraries. -/
/-- Gets the current options after erasing the options set by Lean itself, including `Elab.async`
if it has not been changed by the user from the default of `true`. Note that this includes the
options set in the lakefile.

The result should be the same in both the language server and `lake build`. -/
def getUserOptions : CommandElabM Options := do
  let opts := (← getOptions).erase `internal.cmdlineSnapshots |>.erase `Elab.inServer
  if opts.get? `Elab.async |>.isEqSome true then return opts.erase `Elab.async else return opts

/-- Reifies the given `Options` into `set_options ...` syntax if there are any. -/
def reifySetOptions? (opts : Options) : CommandElabM (Option (TSyntax ``reifiedSetOptionsStx)) := do
  let mut kvs := #[]
  for (key, val) in opts do
    let some val := val.toSetOptionValueSyntax? | continue
    kvs := kvs.push <|← `(reifiedOptionKeyValue| $(mkIdent key) $val)
  if kvs.isEmpty then pure none else some <$> `(reifiedSetOptionsStx| set_options $kvs,*)

end setOption

section universes

/-- Reifies the current level names into `universe ...` syntax if there are any. -/
def reifyLevelNames? : CommandElabM (Option (TSyntax ``Parser.Command.universe)) := do
  let levelNames ← getLevelNames
  if levelNames.isEmpty then pure none else
    some <$> `(Parser.Command.universe| universe $(levelNames.toArray.reverse.map mkIdent)*)

end universes

section namespaces

/-- Reifies the current namespace into `namespace ...` syntax if not in the root namespace. -/
def reifyCurrNamespace? : CommandElabM (Option (TSyntax ``Parser.Command.namespace)) := do
  let ns ← getCurrNamespace
  if ns.isAnonymous then pure none else `(Parser.Command.namespace| namespace $(mkIdent ns))

end namespaces

section variables

/-- Reifies current section variables into `variable ...` syntax if there are any. -/
def reifyVariables? : CommandElabM (Option (TSyntax ``Parser.Command.variable)) := do
  let { varDecls .. } ← getScope
  if varDecls.isEmpty then return none
  let varDecls := varDecls.map (⟨·.raw.unsetTrailing⟩)
  `(Parser.Command.variable| variable $varDecls*)

/-- Reifies current `include`d section variables into `include ...` syntax if there are any. -/
def reifyInclude? : CommandElabM (Option (TSyntax ``Parser.Command.include)) := do
  let { includedVars .. } ← getScope
  if includedVars.isEmpty then return none
  `(Parser.Command.include| include $(includedVars.toArray.map (mkIdent ·.eraseMacroScopes))*)

/-- Reifies current `omit`ted section variables into `omit ...` syntax if there are any. -/
def reifyOmit? : CommandElabM (Option (TSyntax ``Parser.Command.omit)) := do
  let { omittedVars, varUIds, varDecls .. } ← getScope
  if omittedVars.isEmpty then return none
  let mut omittedIdentOrBinder : TSyntaxArray [`ident, `Lean.Parser.Term.instBinder] := #[]
  for var in omittedVars do
    for uid in varUIds, stx in varDecls do
      if uid = var then
        if stx.raw.isOfKind ``Parser.Term.instBinder then
          omittedIdentOrBinder := omittedIdentOrBinder.push ⟨stx.raw.unsetTrailing⟩
        else
          omittedIdentOrBinder := omittedIdentOrBinder.push (mkIdent uid.eraseMacroScopes)
        break
  `(Parser.Command.omit| omit $(omittedIdentOrBinder)*)

end variables

section reset

/-- Pops all but the base scope from the `stateStack`. Note that the base scope may still be
modified. -/
def _root_.Lean.ScopedEnvExtension.popAllScopes {α β σ} (ext : ScopedEnvExtension α β σ)
    (env : Environment) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    { s with stateStack := s.stateStack.getLast?.toList }

@[inherit_doc ScopedEnvExtension.popAllScopes]
def popAllScopes {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] :
    m Unit :=
  for ext in ← scopedEnvExtensionsRef.get do
    modifyEnv ext.popAllScopes

/-- Reconstructs the initial state stack of the given `ScopedEnvExtension` from the imported
entries. -/
def _root_.Lean.ScopedEnvExtension.reconstructInitialStateStack {α β σ}
    (ext : ScopedEnvExtension α β σ) (env : Environment) (opts : Options) :
    IO (ScopedEnvExtension.StateStack α β σ) :=
  ReaderT.run (m := IO) (r := { env, opts }) <|
    ext.ext.addImportedFn (ext.ext.toEnvExtension.getState env .sync).importedEntries

/-- Resets the full state of all scoped env extensions by rebuilding it from the imported entries.

Note that this means that scoped entries added earlier in the current file will no longer be
activatable.

If `clearNewEntries := true` (the default), resets all the to-be-exported entries as well. -/
def resetScopedEnvExtensions {m : Type → Type} [Monad m] [MonadEnv m]
    [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m]
    (opts : Options) (clearNewEntries := true) : m Unit := do
  for ext in ← scopedEnvExtensionsRef.get do
    let env ← getEnv
    let init ← ext.reconstructInitialStateStack env opts
    let init := if clearNewEntries then init else
      { init with newEntries := (ext.ext.getState env .sync).newEntries }
    modifyEnv fun env => ext.ext.setState env init

/-- Creates a base scope with the same header and options as the base scope. (Discards other fields
of the base scope.) -/
def mkFreshBaseScope (scopes : List Scope) : Scope := Id.run do
  let some { header, opts .. } := scopes.getLast? | pure { header := "", opts := {} }
  { header, opts }

/-- A setting determining how far to reset `ScopedEnvExtension`s. -/
inductive _root_.Lean.ScopedEnvExtension.ResetTo where
| /-- Does not reset at all. -/ current
| /-- Resets to the base scope in the `StateStack`, which may be polluted. -/ baseScope
| /-- Reconstructs the initial state from the imported entries. If `clearNewEntries := false` (the
  default), preserves the new entries that will be exported at the end of the file. Otherwise,
  clears them. -/ initialState (clearNewEntries := false)

/-- Resets the scopes. Preserves the options and header in the base scope. Note, however, that this
may include user-set options at the top of the file in addition to the lakefile options.

If `resetEnvExtensions : Option Bool` is `some false` (the default), resets scoped environment
extensions but does not clear the entries that will be exported at the end of the file. If
`some true`, these new entries are cleared as well. If `none`, all scopes are popped, but the base
scope is not reconstructed from imports and therefore may be polluted. -/
def resetScopes (resetEnvExtensionsTo : ScopedEnvExtension.ResetTo := .initialState) :
    CommandElabM Unit := do
  modify fun s => { s with scopes := [mkFreshBaseScope s.scopes] }
  match resetEnvExtensionsTo with
  | .current => pure ()
  | .baseScope => popAllScopes
  | .initialState clearNewEntries => resetScopedEnvExtensions (← getOptions) clearNewEntries

end reset

/-- Resets the scopes, then creates the scope described in the syntactic scope specification. By
default, this resets scoped environment extensions by reconstructing their initial state from
imported entries, but does *not* clear the exported entries. See `ScopedEnvExtension.ResetTo` for
other possibilities. -/
def unreifyScope (stx : TSyntax ``scopeStx)
    (resetEnvExtensionsTo : ScopedEnvExtension.ResetTo := .initialState) :
    CommandElabM Unit :=
  match stx with
  | `(scopeStx| $sectionHeader scope
      $[$universeStx:universe]?
      $[$namespaceStx:namespace]?
      $[open $openDecls:reifiedOpenDecl*]?
      $[$openScoped:reifiedOpenScopedStx]?
      $[set_options $keyVals:reifiedOptionKeyValue,*]?
      $[$vars]?) => do
    resetScopes resetEnvExtensionsTo
    unreifySectionHeader sectionHeader
    universeStx.forM (elabUniverse ·)
    namespaceStx.forM (elabNamespace ·)
    openDecls.forM unreifyOpenDecls
    openScoped.forM unreifyOpenScopedDecls
    keyVals.forM fun keyVals => do
      for keyVal in keyVals.getElems do
        let `(reifiedOptionKeyValue| $id $val) := keyVal | throwUnsupportedSyntax
        -- Gets us info.
        let opts ← Elab.elabSetOption id val
        modifyScope fun s => { s with opts }
    vars.forM fun vars => do
      let `(reifiedVarStx| $vars $[$included]? $[$omitted]?) := vars | throwUnsupportedSyntax
      elabVariable vars
      -- Note: we assume these are disjoint, and order of elaboration is irrelevant.
      included.forM (elabInclude ·)
      omitted.forM (elabOmit ·)
  | _ => throwUnsupportedSyntax

/-- Reifies aspects of the current scope into a `scopeStx` scope specification. See `scopeStx`. -/
def reifyScope : CommandElabM (TSyntax ``scopeStx) := do
  let sectionHeader ← reifySectionHeader (← getScope)
  let universes ← reifyLevelNames?
  let namespaceStx ← reifyCurrNamespace?
  let opens ← reifyOpenDecls (← getOpenDecls)
  let extraOpenScoped ← reifyExtraOpenScopes
  let setOptions ← reifySetOptions? (← getUserOptions)
  let variables ← (← reifyVariables?).mapM fun vars => do
    `(reifiedVarStx| $vars $(← reifyInclude?)? $(← reifyOmit?)?)
  `(scopeStx| $sectionHeader scope
    $[$universes]?
    $[$namespaceStx]?
    $[$opens]?
    $[$extraOpenScoped]?
    $[$setOptions]?
    $[$variables]?)
    /- TODO: technically the variable parsing could change if a scope is opened earlier. This is
    probably important...it'll mean (1) detecting if any variable syntax is scoped (2) writing a
    more detailed parser for `scopeStx` that opens the named scopes! -/

    -- We also could account for `open (scoped) ... in variable` but it would have to be ad-hoc.

public section

/--
`#scope` reifies the current scope into syntax so that it can be transported into another file,
e.g. along with a following declaration that depends on this scope. (No use of `in` is needed.)

`#scope` will log a try-this suggestion suggesting reified syntax that matches the current scope,
or else remain silent. If the reified scope syntax no longer matches the current scope, `#scope`
suggests an updated replacement.

NOTE: `#scope` is currently in development. Soon, `#scope!` and `#scope?` will provide more
features for (1) replacing the current scope with the recorded scope (2) suggesting new ordinary
scope syntax to merge the two scopes.
-/
syntax "#scope" (ppLine scopeStx)? : command

elab_rules : command
| `(#scope%$tk) => do
  let stx ← `(command| #scope%$tk $(← reifyScope))
  -- Note: we use `getRef` to expand the range on which the code action works.
  liftCoreM <| Meta.Tactic.TryThis.addSuggestion (← getRef) stx
| `(#scope%$tk $scopeStx) => do
  let scopeStx' ← withRef scopeStx reifyScope
  unless scopeStx.raw.structEq scopeStx' do
    let stx ← `(command| #scope%$tk $scopeStx')
    liftCoreM <| Meta.Tactic.TryThis.addSuggestion (← getRef) (origSpan? := (← getRef)) stx
      (diffGranularity := .word)

/-- -/
syntax "#scope!" ppLine scopeStx : command

end

end Mathlib.Tactic.Scope

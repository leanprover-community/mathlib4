module

public import Lean
public meta import Mathlib.Lean.Elab.Options
public meta import Mathlib.Lean.Name
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.PrettyPrinter.Delaborator
import Batteries
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Aesop.Util.Basic -- Name.ofComponents...

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

open Lean Meta Elab Command

public meta section

namespace Mathlib.Tactic.Scope

section parsers

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

section openScoped

@[inline] def _root_.Lean.NameSet.minus (current minus : NameSet) : NameSet := Id.run do
  if minus.isEmpty then current else current.filter (!minus.contains ·)

/-- An extension we can trust to always be present, whose active scopes reflect the result of
`open`s. -/
@[inline] def scopeTestExt := Parser.parserExtension.ext

def _root_.Lean.Environment.activeScopes (env : Environment) : NameSet :=
  match scopeTestExt.getState (asyncMode := .local) env |>.stateStack with
  | s :: _ => s.activeScopes
  | _ => {}

/-- Gets the activated scopes in a (standard) scoped env extension that are *not* implied by the
current namespace and open decls. I.e., the extra `open scoped` that exist somewhere. -/
protected def _root_.Lean.Environment.extraScoped (env : Environment)
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

def extraScoped : CommandElabM NameSet := do
  return (← getEnv).extraScoped (← getCurrNamespace) (← getScope).openDecls

end openScoped

end openDecls

-- TODO: `reify*` instead of `mk*Stx`

section setOption

/- Note: Ideally we would like to not include all the lake build options. But these are commingled
with any `set_option`s in the base scope, so without doing something like "checking the lakefile"
or "recording the options at the top of the file via linter" we can't distinguish between options
set by lake and options set in the file. -/
/-- Erases the options set by Lean itself, and `Elab.async` if it has not been changed by the user.
However, still includes the options set in the lakefile. -/
def getUserOptions : CommandElabM Options := do
  let opts := (← getOptions).erase `internal.cmdlineSnapshots |>.erase `Elab.inServer
  if opts.get? `Elab.async |>.isEqSome true then return opts.erase `Elab.async else return opts

def reifySetOptions? (opts : Options) : CommandElabM (Option (TSyntax ``reifiedSetOptionsStx)) := do
  let mut kvs := #[]
  for (key, val) in opts do
    let some val := val.toSetOptionValueSyntax? | continue
    kvs := kvs.push <|← `(reifiedOptionKeyValue| $(mkIdent key) $val)
  if kvs.isEmpty then pure none else some <$> `(reifiedSetOptionsStx| set_options $kvs,*)

end setOption

section universes

def reifyUniverses? : CommandElabM (Option <| TSyntax ``Parser.Command.universe) := do
  let levelNames := (← getScope).levelNames
  if levelNames.isEmpty then pure none else
    some <$> `(Parser.Command.universe| universe $(levelNames.toArray.map mkIdent)*)

end universes

section namespaces

def reifyCurrNamespace? : CommandElabM (Option (TSyntax ``Parser.Command.namespace)) := do
  let ns ← getCurrNamespace
  if ns.isAnonymous then pure none else `(Parser.Command.namespace| namespace $(mkIdent ns))

end namespaces

section variables

def reifyVariables? : CommandElabM (Option (TSyntax ``Parser.Command.variable)) := do
  let { varDecls .. } ← getScope
  if varDecls.isEmpty then return none
  `(Parser.Command.variable| variable $varDecls*)

def reifyInclude? : CommandElabM (Option (TSyntax ``Parser.Command.include)) := do
  let { includedVars .. } ← getScope
  if includedVars.isEmpty then return none
  -- TODO: the `Name`s are `varUIDs` with hygiene, but should we strip that in making the idents?
  `(Parser.Command.include| include $(includedVars.toArray.map mkIdent)*)

def reifyOmit? : CommandElabM (Option (TSyntax ``Parser.Command.omit)) := do
  let { omittedVars, varUIds, varDecls .. } ← getScope
  if omittedVars.isEmpty then return none
  let mut omittedIdentOrBinder : TSyntaxArray [`ident, `Lean.Parser.Term.instBinder] := #[]
  for var in omittedVars do
    for uid in varUIds, stx in varDecls do
      if uid = var then
        if stx.raw.isOfKind ``Parser.Term.instBinder then
          omittedIdentOrBinder := omittedIdentOrBinder.push ⟨stx.raw⟩
        else
          -- TODO: remove scopes?
          omittedIdentOrBinder := omittedIdentOrBinder.push (mkIdent uid)
        break
  -- TODO: the `Name`s are `varUIDs` with hygiene, but should we strip that in making the idents?
  `(Parser.Command.omit| omit $(omittedIdentOrBinder)*)

end variables

def reifyScope : CommandElabM (TSyntax ``scopeStx) := do
  let sectionHeader ← (← getScope).toSectionHeader.toSyntax
  let universes ← reifyUniverses?
  let namespaceStx ← reifyCurrNamespace?
  let opens ← reifyOpenDecls (← getScope).openDecls

  let variables ← (← reifyVariables?).mapM fun vars => do
    `(reifiedVarStx| $vars $(← reifyInclude?)? $(← reifyOmit?)?)

  let extraScopedNames ← extraScoped
  let extraScoped ← if extraScopedNames.isEmpty then pure none else
    let extraScoped ← extraScopedNames.toArray.mapM fun n =>
      `(reifiedSimpleOpenIdent| @$(mkIdent n))
    some <$> `(reifiedOpenScopedStx| open scoped $extraScoped*)

  let setOptions ← reifySetOptions? (← getUserOptions)

  `(scopeStx| $sectionHeader scope
    $[$universes]?
    $[$namespaceStx]?
    $[$opens]?
    $[$extraScoped]?
    $[$setOptions]?
    $[$variables]?)
    /- TODO: technically the variable parsing could change if a scope is opened earlier. This is
    probably important...it'll mean (1) detecting if any variable syntax is scoped (2) writing a
    more detailed parser for `scopeStx` that opens the named scopes! -/

    -- We also could account for `open (scoped) ... in variable` but it would have to be ad-hoc.

syntax "#scope" (ppLine scopeStx)? : command

elab_rules : command
| `(#scope%$tk) => do
  let stx ← `(command|#scope%$tk $(← reifyScope))
  liftCoreM <| Meta.Tactic.TryThis.addSuggestion tk stx
| `(#scope%$tk $scopeStx) => do
  let scopeStx' ← withRef scopeStx reifyScope
  unless scopeStx.raw.structEq scopeStx' do
    let stx ← `(command|#scope%$tk $scopeStx')
    liftCoreM <| Meta.Tactic.TryThis.addSuggestion tk (origSpan? := (← getRef)) stx
      (diffGranularity := .word)

end Mathlib.Tactic.Scope

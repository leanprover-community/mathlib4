module

public import Lean
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.PrettyPrinter.Delaborator
import Batteries
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Aesop.Util.Basic -- Name.ofComponents...


open Lean Meta Elab Command

public section

namespace Mathlib.Tactic.Scope

-- The "inlinable" parsers in this section exist to enable syntax quotations.

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
syntax reifiedOpenStx := withPosition(atomic("open" notFollowedBy("scoped")) ppIndent(reifiedOpenDecl*))

/-- Renders the open scopes that are not accounted for by generic `open`s. Prefixes identifiers with `@` to show the fully-resolved name. -/
syntax reifiedOpenScopedStx := withPosition("open " "scoped"
  ppIndent((ppSpace colGt reifiedSimpleOpenIdent)*))

-- Parser of convenience, since we handle these together.
syntax reifiedVarStx := Parser.Command.variable (ppLine Parser.Command.include)? (ppLine Parser.Command.omit)?

syntax reifiedOptionKeyValue := ppSpace colGt ident ppSpace optionValue
/-- `set_options key₁ val₁, key₂ val₂, ...` renders the options set in a single line. -/
syntax reifiedSetOptionsStx := withPosition("set_options " ppIndent(reifiedOptionKeyValue,*))

/--
A scope specification of the form
```
(@[expose])? (public)? (noncomputable)? (section)? scope
  (universe ...)?
  (namespace ...)?
  (open @id₁ @id₂ ...)?
  (open scoped @id₁ @id₂ ...)?
  (set_options key₁ val₁, key₂ val₂ ...)?
  (variable ...)?
  (include ...)?
  (omit ...)?
```
Notice the differences from typical scope syntax.

Note also that this is intended to reify semantic and instantaneous aspects of a given scope,
and not the entire scope stack. This means that `section`s and local scopes are not
accounted for here.
-/
syntax scopeStx := Parser.Command.sectionHeader &"scope"
  (ppLine colGt Parser.Command.universe)?
  (ppLine colGt Parser.Command.namespace)?
  atomic((ppLine colGt reifiedOpenStx)?)
  (ppLine colGt reifiedOpenScopedStx)? -- TODO: local?
  (ppLine colGt reifiedSetOptionsStx)?
  (ppLine colGt reifiedVarStx)?

section header

open Parser.Command

/--
Encodes scope section headers: `(@[expose])? (public)? (noncomputable)? (meta)?`.
-/
structure SectionHeader where
  /-- Whether the scope uses `@[expose]`. -/
  expose : Bool := false -- TODO: `Option Syntax`?
  /-- Whether the scope uses `public`. -/
  isPublic : Bool := false
  /-- Whether the scope uses `noncomputable`. -/
  isNoncomputable : Bool := false
  /-- Whether the scope uses `meta`. -/
  isMeta : Bool := false
deriving BEq, Inhabited, Repr

/-- Encodes scope section headers, and associates syntax position information to them. -/
structure SectionHeaderRef where
  /-- The full ref of the whole section header. -/
  ref : Syntax := .missing
  /-- The token `expose`. Does not include brackets. -/
  exposeTk : Option Syntax := none
  /-- The token `public`. -/
  publicTk : Option Syntax := none
  /-- The token `noncomputable`. -/
  noncomputableTk : Option Syntax := none
  /-- The token `meta`. -/
  metaTk : Option Syntax := none

/-- Converts syntax representing a section header ref to a `SectionHeader`. -/
@[inline] def SectionHeaderRef.toSectionHeader : SectionHeaderRef → SectionHeader
  | { exposeTk, publicTk, noncomputableTk, metaTk, .. } => {
    expose := exposeTk.isSome
    isPublic := publicTk.isSome
    isNoncomputable := noncomputableTk.isSome
    isMeta := metaTk.isSome
  }

/-- Recreates `(@[expose])? (public)? (noncomputable)? (meta)?` syntax from the given
`SectionHeaderRef`. -/
def SectionHeaderRef.toSyntax {m} [Monad m] [MonadQuotation m] :
    SectionHeaderRef → m (TSyntax ``sectionHeader)
  | { exposeTk, publicTk, noncomputableTk, metaTk, ref } => withRef ref `(sectionHeader|
      $[@[expose%$exposeTk]]?
      $[public%$publicTk]?
      $[noncomputable%$noncomputableTk]?
      $[meta%$metaTk]?)

/-- Organizes `sectionHeader` syntax into a `SectionHeaderRef`. -/
def SectionHeaderRef.ofSyntax? : TSyntax ``sectionHeader → Option SectionHeaderRef
  | ref@`(sectionHeader|
      $[@[expose%$exposeTk]]?
      $[public%$publicTk]?
      $[noncomputable%$noncomputableTk]?
      $[meta%$metaTk]?) =>
    some { ref, exposeTk, publicTk, noncomputableTk, metaTk }
  | _ => none

/-- Creates `(@[expose])? (public)? (noncomputable)? (meta)?` syntax from the given
`SectionHeader`. Uses the current ref for position information on each token. -/
def SectionHeader.toSyntax {m} [Monad m] [MonadQuotation m] :
    SectionHeader → m (TSyntax ``sectionHeader)
  | { expose, isPublic, isNoncomputable, isMeta } => do
    -- This is a hack to exploit antiquotations. `$[$foo%$tk]?` yields `foo` iff `tk.isSome`.
    let r ← getRef
    letI toDummyOptional? (b : Bool) : Option Syntax :=
      if b then some r else none
    let pubTk    := toDummyOptional? isPublic
    let metaTk   := toDummyOptional? isMeta
    let exposeTk := toDummyOptional? expose
    let ncTk     := toDummyOptional? isNoncomputable
    `(sectionHeader|
      $[@[expose%$exposeTk]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?)

/-- Extracts a `SectionHeader` structure from `(@[expose])? (public)? (noncomputable)? (meta)?`
syntax. -/
@[inline] def SectionHeader.ofSyntax? : TSyntax ``sectionHeader → Option SectionHeader
  | `(sectionHeader|
      $[@[expose%$exposeTk]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?) =>
    some {
      expose := exposeTk.isSome
      isPublic := pubTk.isSome
      isNoncomputable := ncTk.isSome
      isMeta := metaTk.isSome
    }
  | _ => none

/-- Isolates the part of a `Scope` that contains `SectionHeader` information. -/
@[inline] def _root_.Lean.Elab.Command.Scope.toSectionHeader : Scope → SectionHeader
  | { isPublic, isMeta, isNoncomputable, attrs .. } =>
    -- Currently, `attrs` only ever holds `@[expose]`.
    { isPublic, isMeta, isNoncomputable, expose := !attrs.isEmpty }

/-- Applies a `sectionHeader` syntax of the form `(@[expose])? (public)? (noncomputable)? (meta)?`
to the current scope, overwriting the values (rather than merging them). For instance, if `public`
is absent, the resulting scope now has `isPublic := false`, even if it was `true` before. -/
def unreifySectionHeaderStx : TSyntax ``Parser.Command.sectionHeader → CommandElabM Unit
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
deduplicates exactly-duplicated `OpenDecl`s. -/
@[inline] private def deduplicateOpenDecls (openDecls : List OpenDecl) : List OpenDecl :=
  -- Note that the innermost openDecls come first and affect name resolution first due to `eraseDups` affecting resolved ids by first occurrence (corresponding to later occurrences in openDecls)
  -- TODO: find something more efficient, which means basically just about anything else.
  openDecls.reverse.eraseDups.reverse

/-- Convert `OpenDecl`s into reified `open @id₁ @id₂ ...` syntax for portability. -/
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

end openScoped

end openDecls

section universes



end universes

def reifyScope : CommandElabM (TSyntax ``scopeStx) := do
  let sectionHeader ← (← getScope).toSectionHeader.toSyntax
  let universes ← getUniverseStx
  let namespaceStx ← getCurrNamespaceSyntax
  let opens ← reifyOpenDecls (← getScope).openDecls

  let variables ← (← getVariableSyntax?).mapM fun vars => do
    `(reifiedVarStx| $vars $(← getIncludeSyntax?)? $(← getOmitSyntax?)?)

  let extraScopedNames ← extraScoped
  let extraScoped ← if extraScopedNames.isEmpty then pure none else
    let extraScoped ← extraScopedNames.toArray.mapM fun n =>
      `(reifiedSimpleOpenIdent| @$(mkIdent n))
    some <$> `(reifiedOpenScopedStx| open scoped $extraScoped*)

  let newOpts ← getNewOptions -- TODO: actually, the base scope may be polluted, right? So maybe just list all of them.
  let setOptions ← do
    let mut kvs := #[]
    for (key, val) in newOpts do
      let some val := val.toSetOptionValueSyntax? | continue
      kvs := kvs.push <|← `(reifiedOptionKeyValue| $(mkIdent key) $(⟨val⟩))
    if kvs.isEmpty then pure none else some <$> `(reifiedSetOptionsStx| set_options $kvs,*)

  `(scopeStx| $sectionHeader scope
    $[$universes]?
    $[$namespaceStx]?
    $[$opens]?
    $[$extraScoped]?
    $[$setOptions]?
    $[$variables]?) -- TODO: technically the variable parsing could change if a scope is opened earlier. This is probably important...it'll mean (1) detecting if any variable syntax is scoped (2) writing a parser for `scope` that opens the named scopes!

    -- We also could account for `open (scoped) ... in variable` but it would have to be ad-hoc.

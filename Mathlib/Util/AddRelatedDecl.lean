/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Init
public meta import Lean.Elab.DeclarationRange

/-!
# `addRelatedDecl`

-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic

/-- An `(attr := ...)` argument for applying the same attributes to multiple declarations. -/
syntax optAttrArg := atomic(" (" &"attr" " := " Parser.Term.attrInstance,* ")")?

/-- Elaborate an `(attr := ...)` argument. -/
def elabOptAttrArg : TSyntax ``optAttrArg → TermElabM (Array Attribute)
  | `(optAttrArg| (attr := $[$attrs],*)) => elabAttrs attrs
  | _ => pure #[]

/-- A helper function for constructing a related declaration from an existing one.

This is currently used by the attributes `reassoc` and `elementwise`,
and has been factored out to avoid code duplication.
Feel free to add features as needed for other applications.

This helper:
* throws an error if a declaration named `tgt` already exists
  (in the current module or in an imported one),
* calls `addDeclarationRangesFromSyntax`, so jump-to-definition works,
* copies the `protected` status of the existing declaration, and
* supports copying attributes.

Arguments:
* `src : Name` is the existing declaration that we are modifying.
* `prefix_ : String` will be prepended and `suffix : String` will be appended to `src`
  to form the name of the new declaration.
* `ref : Syntax` is the syntax where the user requested the related declaration.
* `construct value levels : MetaM (Expr × List Name)`
  given an `Expr.const` referring to the original declaration, and its universe variables,
  should construct the value of the new declaration,
  along with the names of its universe variables.
* `attrs` is the attributes that should be applied to both the new and the original declaration,
  e.g. in the usage `@[reassoc (attr := simp)]`.
  We apply it to both declarations, to have the same behavior as `to_additive`, and to shorten some
  attribute commands. Note that `@[elementwise (attr := simp), reassoc (attr := simp)]` will try
  to apply `simp` twice to the current declaration, but that causes no issues.
* `docstringPrefix?` is prepended to the doc-string of `src` to form the doc-string of `tgt`.
  If it is `none`, only the doc-string of `src` is used.
* When `hoverInfo := true`, the generated constant will be shown as the hover information on `ref`.
  Warning: As a result, the original doc-string of `ref` will not be visible,
  and go-to-def on `ref` will not go to the definition of `ref`.
-/
def addRelatedDecl (src tgt : Name) (ref : Syntax)
    (attrs : TSyntax ``optAttrArg)
    (construct : Expr → List Name → MetaM (Expr × List Name))
    (docstringPrefix? : Option String := none)
    (hoverInfo : Bool := false) :
    MetaM Unit := do
  -- If `tgt` already exists in an imported module, the `addDeclarationRangesFromSyntax` call
  -- below panics (and if it exists in the current module, `addDecl` would fail with a less
  -- helpful message), so we check for a pre-existing declaration up front.
  let env := (← getEnv).setExporting false
  if env.contains tgt then
    match env.getModuleIdxFor? tgt with
    | some idx =>
      throwError "cannot create related declaration `{tgt}`: \
        it has already been declared in the imported module \
        `{env.header.moduleNames[idx.toNat]!}`"
    | none =>
      throwError "cannot create related declaration `{tgt}`: \
        it has already been declared in the current module"
  addDeclarationRangesFromSyntax tgt (← getRef) ref
  let info ← withoutExporting <| getConstInfo src
  let value := .const src (info.levelParams.map mkLevelParam)
  let (newValue, newLevels) ← construct value info.levelParams
  let newValue ← instantiateMVars newValue
  let newType ← instantiateMVars (← inferType newValue)
  unless ← isProp newType do throwError "Related declaration is not a proposition: {newType}"
  addDecl <| ← mkThmOrUnsafeDef
    { levelParams := newLevels, type := newType, name := tgt, value := newValue }
  if isProtected (← getEnv) src then
    setEnv <| addProtected (← getEnv) tgt
  match docstringPrefix?, ← findDocString? (← getEnv) src with
  | none, none => pure ()
  | some doc, none | none, some doc => addDocStringCore tgt doc
  | some docPre, some docPost => addDocStringCore tgt s!"{docPre}\n\n---\n\n{docPost}"
  inferDefEqAttr tgt
  Term.TermElabM.run' do
    let attrs ← elabOptAttrArg attrs
    Term.applyAttributes src attrs
    Term.applyAttributes tgt attrs
    if hoverInfo then
      Term.addTermInfo' ref (← mkConstWithLevelParams tgt) (isBinder := true)

end Mathlib.Tactic

/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Init
public meta import Lean.Elab.DeclarationRange
public meta import Lean.Linter.TacticTypeCheck

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

/-- Re-implementation of the inner loop of `Lean.Linter.tacticCheckInstances` for use on
declarations synthesized by Mathlib attributes (`@[simps]`, `@[reassoc]`, `@[elementwise]`, ...).
Returns the list of semireducible non-instance definitions that `Meta.check declType .default`
had to unfold but `Meta.check declType .implicit` would not, or `none` if `declType` already
passes the `.implicit` check. -/
private def checkImplicitTransparency (declType : Expr) : MetaM (Option (List Name)) := do
  let origDiag := (← get).diag
  let result : Option (List Name) ← withOptions (diagnostics.set · true) do
    try Meta.check declType .default catch _ => return none
    let counterDefault := (← get).diag.unfoldCounter
    modify ({ · with diag := origDiag })
    try
      Meta.check declType .implicit
      return none
    catch _ =>
      let counterInst := (← get).diag.unfoldCounter
      let diff := Meta.subCounters counterDefault counterInst
      let env ← getEnv
      return some <| diff.toList.filterMap fun (n, count) => do
        guard <| count > 0
        guard <| getReducibilityStatusCore env n matches .semireducible
        guard <| !Meta.isInstanceCore env n
        return n
  -- Always restore the original diagnostics snapshot, mirroring `tacticCheckInstances`.
  modify ({ · with diag := origDiag })
  return result

/-- Extension of `linter.tacticCheckInstances` to lemmas produced by Mathlib attributes such as
`@[simps]`, `@[reassoc]`, and `@[elementwise]`. Call sites pass the syntax of the user's
attribute (`ref`), the name of the generated lemma (`declName`), and the lemma's type
(`declType`); a warning is emitted at `ref` if `declType` is type-correct at `.default` but
not at `.implicit`, listing the semireducible definitions that would need to be
marked `@[implicit_reducible]` to fix the mismatch.

The check is gated by the existing core option `linter.tacticCheckInstances` and is silent
otherwise; following the convention of the core linter, it does *not* participate in
`linter.all`. -/
def warnIfImplicitIllTyped (ref : Syntax) (declName : Name) (declType : Expr) : MetaM Unit := do
  let lintOpt : Lean.Option Bool :=
    { name := `linter.tacticCheckInstances, defValue := false }
  unless lintOpt.get (← getOptions) do return
  let some candidates ← checkImplicitTransparency declType | return
  if candidates.isEmpty then return
  let bullets := MessageData.joinSep (candidates.map (m!"{MessageData.ofConstName ·}")) Format.line
  Lean.Linter.logLint lintOpt ref
    m!"generated lemma {MessageData.ofConstName declName} is not type-correct at \
      `.implicit` transparency; consider marking some of the following as \
      `@[implicit_reducible]`:{indentD bullets}"

/-- A helper function for constructing a related declaration from an existing one.

This is currently used by the attributes `reassoc` and `elementwise`,
and has been factored out to avoid code duplication.
Feel free to add features as needed for other applications.

This helper:
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
  addDeclarationRangesFromSyntax tgt (← getRef) ref
  let info ← withoutExporting <| getConstInfo src
  let value := .const src (info.levelParams.map mkLevelParam)
  let (newValue, newLevels) ← construct value info.levelParams
  let newValue ← instantiateMVars newValue
  let newType ← instantiateMVars (← inferType newValue)
  unless ← isProp newType do throwError "Related declaration is not a proposition: {newType}"
  warnIfImplicitIllTyped ref tgt newType
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

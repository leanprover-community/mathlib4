/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Translate.Core

/-!
# Tagging of unfold boundaries for translation attributes

The file `Mathlib.Tactic.Translate.UnfoldBoundary` defines how to add unfold boundaries in terms.
In this file, we define the infrastructure for tagging declaration to be used for that.
This is in a separate file, because we needs to import `Mathlib.Tactic.Translate.Core` here.
-/

meta section

namespace Mathlib.Tactic.Translate

open Lean Meta Elab Command Term UnfoldBoundary

inductive CastKind where
  | eq | unfoldFun | refoldFun

def CastKind.mkRel (lhs body : Expr) : CastKind → MetaM Expr
  | .eq => mkEq lhs body
  | .unfoldFun => return .forallE `_ lhs body .default
  | .refoldFun => return .forallE `_ body lhs .default

def CastKind.mkProof (lhs : Expr) : CastKind → MetaM Expr
  | .eq => mkEqRefl lhs
  | _ => return .lam `_ lhs (.bvar 0) .default

def elabInsertCastAux (declName : Name) (castKind : CastKind) (stx : Term) (t : TranslateData) :
    CommandElabM (Name × Name) :=
  Command.liftTermElabM do withDeclNameForAuxNaming declName do withExporting do
  let info ← getConstInfoDefn declName
  lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let addDecl name type value : MetaM Unit := do
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs value
      addDecl <| ←
        if castKind matches .eq then
          mkThmOrUnsafeDef { name, type, value, levelParams := info.levelParams }
        else
          .defnDecl <$> mkDefinitionValInferringUnsafe name info.levelParams type value .opaque
    let lhs := mkAppN (.const info.name <| info.levelParams.map mkLevelParam) xs
    let name ← mkAuxDeclName ((t.attrName.appendBefore "_").appendAfter "_cast")
    addDecl name (← castKind.mkRel lhs body) (← castKind.mkProof lhs)

    let newLhs ← applyReplacementFun t lhs
    let newBody ← applyReplacementFun t body
    let newType ← castKind.mkRel newLhs newBody
    -- Make the goal easier to prove by unfolding the new lhs
    let newType' ← castKind.mkRel ((← unfoldDefinition? newLhs).getD newLhs) newBody
    let newValue ← elabTermEnsuringType stx newType' <* synthesizeSyntheticMVarsNoPostponing
    let newName ← mkAuxDeclName ((t.attrName.appendBefore "_").appendAfter "_cast")
    addDecl newName newType (← instantiateMVars newValue)

    let relevantArg? := (t.argInfoAttr.find? (← getEnv) declName).map (·.relevantArg)
    _ ← addTranslationAttr t name
      { tgt := newName, existing := true, ref := .missing, relevantArg? }
    return (name, newName)

/-- The `insert_cast foo := ...` command should be used when the translation of some
definition `foo` is not definitionally equal to the translation of its value.
It requires a proof that these two are equal, which `by grind` can usually prove.

The command internally generates an unfolding theorem for `foo`, and a dual of this theorem.
When type checking a term requires the definition `foo` to be unfolded, then in order to translate
that term, a `cast` is first inserted into the term using this unfolding theorem.
As a result, type checking the term won't anymore require unfolding `foo`, so the term
can be safely translated. -/
public def elabInsertCast (declName : Ident) (valStx : Term) (t : TranslateData) :
    CommandElabM Unit := do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo declName
  let (name, _) ← elabInsertCastAux declName .eq valStx t
  let some { unfolds, .. } := t.unfoldBoundaries?
    | throwError "{t.attrName} doesn't support unfold boundaries"
  unfolds.add declName { origin := .decl name, proof := mkConst name, rfl := true }

/-- The `insert_cast_fun foo := ..., ...` command should be used when the translation of some
type `foo` is not definitionally equal to the translation of its value.
It requires a dual of the function that unfolds `foo` and of the function that refolds `foo`.

The command internally generates these unfold/refold functions for `foo`, and their duals.
If type checking a term requires the definition `foo` to be unfolded, then before translating
that term, the unfold/refold function is inserted into the term.
As a result, type checking the term won't anymore require unfolding `foo`, so the term
can be safely translated. After translating, the unfold/refold functions are again unfolded. -/
public def elabInsertCastFun (declName : Ident) (valStx₁ valStx₂ : Term) (t : TranslateData) :
    CommandElabM Unit := do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo declName
  let (name₁, dualName₁) ← elabInsertCastAux declName .unfoldFun valStx₁ t
  let (name₂, dualName₂) ← elabInsertCastAux declName .refoldFun valStx₂ t
  let some { casts, insertionFuns, .. } := t.unfoldBoundaries?
    | throwError "{t.attrName} doesn't support unfold boundaries"
  casts.add declName (name₁, name₂)
  insertionFuns.add name₁ (); insertionFuns.add dualName₁ ()
  insertionFuns.add name₂ (); insertionFuns.add dualName₂ ()

end Mathlib.Tactic.Translate

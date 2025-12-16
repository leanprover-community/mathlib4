/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Mathlib.Lean.PrettyPrinter.Delaborator

/-!
# Set Notation

This file allows the `⊆` notation to be shorthand for `≤`.

If a type is tagged with `@[use_set_notation]`, then `a ≤ b` on that type will be printed as
`a ⊆ b`.
-/

@[expose] public section

namespace Mathlib.Meta

open Lean Elab Term PrettyPrinter.Delaborator SubExpr

/-! ## Elaboration -/

private meta def mkSubsetStx (a b : Term) : CoreM Term := `($a ⊆ $b)
private meta def mkSsubsetStx (a b : Term) : CoreM Term := `($a ⊂ $b)
private meta def mkSupsetStx (a b : Term) : CoreM Term := `($a ⊇ $b)
private meta def mkSsupsetStx (a b : Term) : CoreM Term := `($a ⊃ $b)

/-- Subset relation: `a ⊆ b`, but overwritten  -/
syntax:50 (name := subsetStx') (priority := high) term:51 " ⊆ " term:51 : term
/-- Strict subset relation: `a ⊂ b`  -/
syntax:50 (name := ssubsetStx') (priority := high) term:51 " ⊂ " term:51 : term
/-- Superset relation: `a ⊇ b`  -/
syntax:50 (name := supsetStx') (priority := high) term:51 " ⊇ " term:51 : term
/-- Strict superset relation: `a ⊃ b`  -/
syntax:50 (name := ssupsetStx') (priority := high) term:51 " ⊃ " term:51 : term

private meta def elabTermOrTerm (stx₁ stx₂ : Term) (expectedType? : Option Expr) : TermElabM Expr :=
  try
    withoutErrToSorry do elabTermAndSynthesize stx₁ expectedType?
  catch _ =>
    elabTerm stx₂ expectedType?

@[term_elab subsetStx']
meta def elabSubsetStx' : TermElab := fun
  | `($x ⊆ $y), expectedType? => do elabTermOrTerm (← mkSubsetStx x y) (← `($x ≤ $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

@[term_elab ssubsetStx']
meta def elabSsubsetStx' : TermElab := fun
  | `($x ⊂ $y), expectedType? => do elabTermOrTerm (← mkSsubsetStx x y) (← `($x < $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

@[term_elab supsetStx']
meta def elabSupsetStx' : TermElab := fun
  | `($x ⊇ $y), expectedType? => do elabTermOrTerm (← mkSupsetStx x y) (← `($x ≥ $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

@[term_elab ssupsetStx']
meta def elabSsupsetStx' : TermElab := fun
  | `($x ⊃ $y), expectedType? => do elabTermOrTerm (← mkSsupsetStx x y) (← `($x > $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Declare `∀ x ⊆ y, ...` as syntax for `∀ x, x ⊆ y → ...` and `∃ x ⊆ y, ...` as syntax for
`∃ x, x ⊆ y ∧ ...` -/
binder_predicate (priority := high) x " ⊆ " y:term => `($x ⊆ $y)

/-- Declare `∀ x ⊂ y, ...` as syntax for `∀ x, x ⊂ y → ...` and `∃ x ⊂ y, ...` as syntax for
`∃ x, x ⊂ y ∧ ...` -/
binder_predicate (priority := high) x " ⊂ " y:term => `($x ⊂ $y)

/-- Declare `∀ x ⊇ y, ...` as syntax for `∀ x, x ⊇ y → ...` and `∃ x ⊇ y, ...` as syntax for
`∃ x, x ⊇ y ∧ ...` -/
binder_predicate (priority := high) x " ⊇ " y:term => `($x ⊇ $y)

/-- Declare `∀ x ⊃ y, ...` as syntax for `∀ x, x ⊃ y → ...` and `∃ x ⊃ y, ...` as syntax for
`∃ x, x ⊃ y ∧ ...` -/
binder_predicate (priority := high) x " ⊃ " y:term => `($x ⊃ $y)


/-! ## Delaboration -/

meta initialize setNotationAttr : TagDeclarationExtension ← mkTagDeclarationExtension

meta initialize
  registerBuiltinAttribute {
    name  := `use_set_notation
    descr := "use set notation for this type"
    add   := fun declName _stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `coe kind
      modifyEnv (setNotationAttr.tag · declName) }

/-- Delaborate `x ≤ y` into `x ⊆ y` if the type is tagged with `use_set_notation`. -/
@[delab app.LE.le]
meta def delabLe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LE.le α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationAttr.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊆ $y)
  annotateGoToDef stx `Mathlib.Meta.delabLe

/-- Delaborate `x < y` into `x ⊂ y` if the type is tagged with `use_set_notation`. -/
@[delab app.LT.lt]
meta def delabLt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LT.lt α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationAttr.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊂ $y)
  annotateGoToDef stx `Mathlib.Meta.delabLt

/-- Delaborate `x ≤ y` into `x ⊆ y` if the type is tagged with `use_set_notation`. -/
@[delab app.GE.ge]
meta def delabGe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GE.ge α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationAttr.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊇ $y)
  annotateGoToDef stx `Mathlib.Meta.delabGe

/-- Delaborate `x < y` into `x ⊂ y` if the type is tagged with `use_set_notation`. -/
@[delab app.GT.gt]
meta def delabGt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GT.gt α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationAttr.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊃ $y)
  annotateGoToDef stx `Mathlib.Meta.delabGt

end Mathlib.Meta

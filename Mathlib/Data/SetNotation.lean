/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Mathlib.Lean.PrettyPrinter.Delaborator

/-!
# Set Notation

This file allows the use of `⊆` notation while the underlying constant is `≤`.
Similarly for `⊂`/`<`, `⊇`/`≥` and `⊃`/`>`.

A new copy of the `a ⊆ b` syntax is declared, which overwrites the original one. It tries to
elaborate to the original `a ⊆ b` notation, and if that doesn't work, then it elaborates to `a ≤ b`.

A new delaborator for `LE.le` is added so that `a ≤ b` prints as `a ⊆ b` whenever the type is
tagged with `@[use_set_notation]`. This tag is used for `Set`, `Finset`, `PSet` and `ZFSet`.

`Multiset` has both `≤` and `⊆` defined on it, with different meanings. This still works and is
unaffected.

Some types in Lean core have instances of `HasSubset`, such as `List`. This also still works.

TODO: The same trick should allow us to make `∪`/`⊔` and `∩`/`⊓` refer to the same constant.
-/

public meta section

namespace Mathlib.Meta

open Lean Elab Term PrettyPrinter.Delaborator SubExpr

/-! ## Elaboration -/

private def mkSubsetStx (a b : Term) : CoreM Term := `($a ⊆ $b)
private def mkSsubsetStx (a b : Term) : CoreM Term := `($a ⊂ $b)
private def mkSupsetStx (a b : Term) : CoreM Term := `($a ⊇ $b)
private def mkSsupsetStx (a b : Term) : CoreM Term := `($a ⊃ $b)

/-- Subset relation: `a ⊆ b`, but overwritten  -/
syntax:50 (name := subsetStx') (priority := high) term:51 " ⊆ " term:51 : term
/-- Strict subset relation: `a ⊂ b`  -/
syntax:50 (name := ssubsetStx') (priority := high) term:51 " ⊂ " term:51 : term
/-- Superset relation: `a ⊇ b`  -/
syntax:50 (name := supsetStx') (priority := high) term:51 " ⊇ " term:51 : term
/-- Strict superset relation: `a ⊃ b`  -/
syntax:50 (name := ssupsetStx') (priority := high) term:51 " ⊃ " term:51 : term

/-- First try to elaborate `stx₁`, and if that doesn't succeed immediately, fall back on
elaborating `stx₂`.

Note that we call `elabTermAndSynthesize` on `stx₁`, so if there are any stuck type class
constraints due to not (yet) filled in metavariables, we will discard the `stx₁` option. -/
private def elabTermOrTerm (stx₁ stx₂ : Term) (expectedType? : Option Expr) : TermElabM Expr :=
  try
    withoutErrToSorry do elabTermAndSynthesize stx₁ expectedType?
  catch _ =>
    elabTerm stx₂ expectedType?

/-- Elaborator for `x ⊆ y` notation. -/
@[term_elab subsetStx']
def elabSubsetStx' : TermElab := fun
  | `($x ⊆ $y), expectedType? => do elabTermOrTerm (← mkSubsetStx x y) (← `($x ≤ $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊂ y` notation. -/
@[term_elab ssubsetStx']
def elabSsubsetStx' : TermElab := fun
  | `($x ⊂ $y), expectedType? => do elabTermOrTerm (← mkSsubsetStx x y) (← `($x < $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊇ y` notation. -/
@[term_elab supsetStx']
def elabSupsetStx' : TermElab := fun
  | `($x ⊇ $y), expectedType? => do elabTermOrTerm (← mkSupsetStx x y) (← `($x ≥ $y)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊃ y` notation. -/
@[term_elab ssupsetStx']
def elabSsupsetStx' : TermElab := fun
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

/-- The `@[use_set_notation]` attribute marks that order notation on the given type should be
pretty printed using set-style notation, i.e. `⊆` instead of `≤`. -/
initialize setNotationExt : TagDeclarationExtension ← mkTagDeclarationExtension

@[inherit_doc setNotationExt]
initialize
  registerBuiltinAttribute {
    name  := `use_set_notation
    descr := "use set notation for this type"
    add   := fun declName _stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `coe kind
      modifyEnv (setNotationExt.tag · declName) }

/-- Delaborate `x ≤ y` into `x ⊆ y` if the type is tagged with `@[use_set_notation]`. -/
@[delab app.LE.le]
def delabLe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LE.le α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationExt.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊆ $y)
  annotateGoToDef stx `Mathlib.Meta.delabLe

/-- Delaborate `x < y` into `x ⊂ y` if the type is tagged with `@[use_set_notation]`. -/
@[delab app.LT.lt]
def delabLt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LT.lt α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationExt.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊂ $y)
  annotateGoToDef stx `Mathlib.Meta.delabLt

/-- Delaborate `x ≥ y` into `x ⊇ y` if the type is tagged with `@[use_set_notation]`. -/
@[delab app.GE.ge]
def delabGe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GE.ge α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationExt.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊇ $y)
  annotateGoToDef stx `Mathlib.Meta.delabGe

/-- Delaborate `x > y` into `x ⊃ y` if the type is tagged with `@[use_set_notation]`. -/
@[delab app.GT.gt]
def delabGt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GT.gt α _ _ _ := ← getExpr | failure
  let .const t _ := (← instantiateMVars α).getAppFn' | failure
  unless setNotationExt.isTagged (← getEnv) t do failure
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊃ $y)
  annotateGoToDef stx `Mathlib.Meta.delabGt

end Mathlib.Meta

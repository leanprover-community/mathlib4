/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Mathlib.Tactic.Push
public import Mathlib.CategoryTheory.Iso

public meta section
open Lean Meta CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.CancelIso

/-- Version of `IsIso.hom_inv_id` for internal use of the `cancelIso` simproc. Do not use. -/
lemma hom_inv_id_of_eq {C : Type*} [Category* C] {x y : C}
    (f : x ⟶ y) [IsIso f] (g : y ⟶ x) (h : inv f = g) : f ≫ g = 𝟙 _ := by
  rw [← h]
  exact IsIso.hom_inv_id f

/-- Version of `IsIso.hom_inv_id_assoc` for internal use of the `cancelIso` simproc. Do not use. -/
lemma hom_inv_id_of_eq_assoc {C : Type*} [Category* C] {x y : C}
    (f : x ⟶ y) [IsIso f] (g : y ⟶ x) (h : inv f = g) {z : C} (k : x ⟶ z) : f ≫ g ≫ k = k := by
  rw [← h]
  exact IsIso.hom_inv_id_assoc f k

def cancelIsoSimproc : Simp.Simproc := fun e => withReducible do -- is withReducible necessary here?
  let e_whnf ← whnf e
  let_expr CategoryStruct.comp C instCat x y t f g := e_whnf |
    return .continue
  match_expr g with
  -- Right_associated expressions needs their own logic.
  | CategoryStruct.comp _ _ _ z _ g h =>
    -- Can’t expect a cancelation if the objects don’t match
    unless z == x do
      return .continue
    -- Can’t expect a cancellation if `f` is not an iso.
    let some inst ← synthInstance? <| ← mkAppM ``IsIso #[f] |
      return .continue
    let inv_f ← mkAppOptM ``CategoryTheory.inv #[none, none, none, none, f, inst]
    let pushed_inv ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none inv_f
    let pushed_g ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none <| g
    unless ← isDefEq pushed_inv.expr pushed_g.expr do
      return .continue
    -- Builds the proof inv f = g first:
    let p₀ ← mkEqTrans (pushed_inv.proof?.getD (← mkEqRefl inv_f))
      (← mkEqSymm <| pushed_g.proof?.getD (← mkEqRefl g))
    -- Builds the proof that `f ≫ g ≫ h = h.
    let P ← mkAppOptM ``hom_inv_id_of_eq_assoc #[C, none, x, y, f, inst, g, p₀, none, h]
    return .done (.mk h (.some P) false)
  -- Otherwise, same logic but with hom_inv_id_of_eq instead of hom_inv_id_of_eq_assoc
  | _ =>
    unless t == x do
      return .continue
    let some inst ← synthInstance? <| ← mkAppM ``IsIso #[f] |
      return .continue
    let inv_f ← mkAppOptM ``CategoryTheory.inv #[none, none, none, none, f, inst]
    let pushed_inv ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none inv_f
    let pushed_g ← Mathlib.Tactic.Push.pushCore (.const ``CategoryTheory.inv) {} none <| g
    unless ← isDefEq pushed_inv.expr pushed_g.expr do
      return .continue
    let p₀ ← mkEqTrans (pushed_inv.proof?.getD (← mkEqRefl inv_f))
      (← mkEqSymm <| pushed_g.proof?.getD (← mkEqRefl g))
    let P ← mkAppOptM ``hom_inv_id_of_eq #[C, none, x, y, f, inst, g, p₀]
    return .done (.mk (← mkAppOptM ``CategoryStruct.id #[C, instCat, x]) (.some P) false)

end Mathlib.Tactic.CategoryTheory.CancelIso

simproc_decl cancel_iso (CategoryStruct.comp (self := ?x) _ _) :=
  Mathlib.Tactic.CategoryTheory.CancelIso.cancelIsoSimproc

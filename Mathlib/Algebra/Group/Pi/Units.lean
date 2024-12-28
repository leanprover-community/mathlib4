/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Util.Delaborators

/-! # Units in pi types -/

variable {ι} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i}

/-- The units of a product is isomorpic to the product of the units. -/
@[to_additive (attr := simps)
  "The (additive) units of a product is isomorpic to the product of the (additive) units."]
def Units.piEquiv : (Π i, M i)ˣ ≃* Π i, (M i)ˣ where
  toFun f i := ⟨f.val i, f.inv i, congr_fun f.val_inv i, congr_fun f.inv_val i⟩
  invFun f := ⟨(val <| f ·), (inv <| f ·), funext (val_inv <| f ·), funext (inv_val <| f ·)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[to_additive]
lemma IsUnit.pi_iff :
    IsUnit x ↔ ∀ i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y ↦ x i * y = 1 ∧ y * x i = 1).symm

@[to_additive]
alias ⟨IsUnit.apply, _⟩ := IsUnit.pi_iff

@[to_additive]
lemma IsUnit.val_inv_apply (hx : IsUnit x) (i) : (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹ := by
  rw [← Units.inv_eq_val_inv, ← Units.val_inv_piEquiv_apply]; congr; ext; rfl

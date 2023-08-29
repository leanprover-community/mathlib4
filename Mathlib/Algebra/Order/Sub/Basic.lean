/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Sub.Defs

#align_import algebra.order.sub.basic from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# Additional results about ordered Subtraction

-/


variable {α β : Type*}

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b c d : α}

theorem AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) := by
  rw [tsub_le_iff_right, ← f.map_add]
  -- ⊢ ↑f a ≤ ↑f (a - b + b)
  exact hf le_tsub_add
  -- 🎉 no goals
#align add_hom.le_map_tsub AddHom.le_map_tsub

theorem le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * b - a * c ≤ a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _
#align le_mul_tsub le_mul_tsub

theorem le_tsub_mul {R : Type*} [CommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub
  -- 🎉 no goals
#align le_tsub_mul le_tsub_mul

end Add

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
theorem OrderIso.map_tsub {M N : Type*} [Preorder M] [Add M] [Sub M] [OrderedSub M]
    [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N)
    (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b := by
  let e_add : M ≃+ N := { e with map_add' := h_add }
  -- ⊢ ↑e (a - b) = ↑e a - ↑e b
  refine' le_antisymm _ (e_add.toAddHom.le_map_tsub e.monotone a b)
  -- ⊢ ↑e (a - b) ≤ ↑e a - ↑e b
  suffices e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)) by simpa
  -- ⊢ ↑e (↑(symm e) (↑e a) - ↑(symm e) (↑e b)) ≤ ↑e (↑(symm e) (↑e a - ↑e b))
  exact e.monotone (e_add.symm.toAddHom.le_map_tsub e.symm.monotone _ _)
  -- 🎉 no goals
#align order_iso.map_tsub OrderIso.map_tsub

/-! ### Preorder -/


section Preorder

variable [Preorder α]

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem AddMonoidHom.le_map_tsub [Preorder β] [AddCommMonoid β] [Sub β] [OrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  f.toAddHom.le_map_tsub hf a b
#align add_monoid_hom.le_map_tsub AddMonoidHom.le_map_tsub

end Preorder

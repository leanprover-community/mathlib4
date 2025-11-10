/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Order.Hom.Basic
/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/


variable {α β : Type*}

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α]

theorem AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) := by
  rw [tsub_le_iff_right, ← f.map_add]
  exact hf le_tsub_add

theorem le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * b - a * c ≤ a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _

theorem le_tsub_mul {R : Type*} [NonUnitalCommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub

end Add

theorem map_tsub_of_le {F : Type*} [PartialOrder α] [AddCommSemigroup α] [ExistsAddOfLE α]
    [AddLeftMono α] [Sub α] [OrderedSub α] [PartialOrder β] [AddCommSemigroup β] [Sub β]
    [OrderedSub β] [AddLeftReflectLE β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : α) (h : b ≤ a) : f a - f b = f (a - b) := by
  conv => lhs; rw [← tsub_add_cancel_of_le h]
  rw [map_add, add_tsub_cancel_right]

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
theorem OrderIso.map_tsub {M N : Type*} [Preorder M] [Add M] [Sub M] [OrderedSub M]
    [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N)
    (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b := by
  let e_add : M ≃+ N := { e with map_add' := h_add }
  refine le_antisymm ?_ (e_add.toAddHom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.toAddHom.le_map_tsub e.symm.monotone _ _)

/-! ### Preorder -/


section Preorder

variable [Preorder α]
variable [AddCommMonoid α] [Sub α] [OrderedSub α]

theorem AddMonoidHom.le_map_tsub [Preorder β] [AddZeroClass β] [Sub β] [OrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  f.toAddHom.le_map_tsub hf a b

end Preorder

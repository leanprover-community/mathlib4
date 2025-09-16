/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Daniel Weber
-/
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.RingTheory.FreeCommRing
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinalities of free constructions

This file shows that all the free constructions over `α` have cardinality `max #α ℵ₀`,
and are thus infinite, and specifically countable over countable generators.

Combined with the ring `Fin n` for the finite cases, this lets us show that there is a `CommRing` of
any cardinality.
-/

universe u
variable (α : Type u)

section Infinite

@[to_additive]
instance [Nonempty α] : Infinite (FreeMonoid α) := inferInstanceAs <| Infinite (List α)

@[to_additive]
instance [Nonempty α] : Infinite (FreeGroup α) := by
  classical
  exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective

instance [Nonempty α] : Infinite (FreeAbelianGroup α) :=
  (FreeAbelianGroup.equivFinsupp α).toEquiv.infinite_iff.2 inferInstance

instance : Infinite (FreeRing α) := by unfold FreeRing; infer_instance

instance : Infinite (FreeCommRing α) := by unfold FreeCommRing; infer_instance

end Infinite

section Countable

variable [Countable α]

@[to_additive]
instance : Countable (FreeMonoid α) := by unfold FreeMonoid; infer_instance

@[to_additive]
instance : Countable (FreeGroup α) := Quotient.countable

instance : Countable (FreeAbelianGroup α) := Quotient.countable

instance : Countable (FreeRing α) := Quotient.countable

instance : Countable (FreeCommRing α) := by
  unfold FreeCommRing Multiplicative
  infer_instance

end Countable

namespace Cardinal

theorem mk_abelianization_le (G : Type u) [Group G] :
    #(Abelianization G) ≤ #G := Cardinal.mk_le_of_surjective Quotient.mk_surjective

@[to_additive (attr := simp)]
theorem mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = max #α ℵ₀ :=
    Cardinal.mk_list_eq_max_mk_aleph0 _

@[to_additive (attr := simp)]
theorem mk_freeGroup [Nonempty α] : #(FreeGroup α) = max #α ℵ₀ := by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    simp [Cardinal.mk_list_eq_max_mk_aleph0]
    obtain hα | hα := lt_or_ge #α ℵ₀
    · simp only [hα.le, max_eq_right, max_eq_right_iff]
      exact (mul_lt_aleph0 hα (nat_lt_aleph0 2)).le
    · rw [max_eq_left hα, max_eq_left (hα.trans <| Cardinal.le_mul_right two_ne_zero),
        Cardinal.mul_eq_left hα _ (by simp)]
      exact (nat_lt_aleph0 2).le.trans hα
  · apply max_le
    · exact mk_le_of_injective FreeGroup.of_injective
    · simp

@[simp]
theorem mk_freeAbelianGroup [Nonempty α] : #(FreeAbelianGroup α) = max #α ℵ₀ := by
  rw [Cardinal.mk_congr (FreeAbelianGroup.equivFinsupp α).toEquiv]
  simp

@[simp]
theorem mk_freeRing : #(FreeRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeRing]

@[simp]
theorem mk_freeCommRing : #(FreeCommRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeCommRing]

end Cardinal

section Nonempty

/-- A commutative ring can be constructed on any non-empty type.

See also `Infinite.nonempty_field`. -/
instance nonempty_commRing [Nonempty α] : Nonempty (CommRing α) := by
  obtain hR | hR := finite_or_infinite α
  · obtain ⟨x⟩ := nonempty_fintype α
    have : NeZero (Fintype.card α) := ⟨by simp⟩
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFin α
    exact ⟨open scoped Fin.CommRing in e.commRing⟩
  · have ⟨e⟩ : Nonempty (α ≃ FreeCommRing α) := by simp [← Cardinal.eq]
    exact ⟨e.commRing⟩

@[simp]
theorem nonempty_commRing_iff : Nonempty (CommRing α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => nonempty_commRing _⟩

@[simp]
theorem nonempty_ring_iff : Nonempty (Ring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toRing)⟩

@[simp]
theorem nonempty_commSemiring_iff : Nonempty (CommSemiring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toCommSemiring)⟩

@[simp]
theorem nonempty_semiring_iff : Nonempty (Semiring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toSemiring)⟩

end Nonempty

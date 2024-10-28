/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Daniel Weber
-/
import Mathlib.RingTheory.FreeCommRing
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Finsupp
import Mathlib.GroupTheory.FreeAbelianGroupFinsupp

/-! # Cardinalities of free constructions -/

universe u
variable (α : Type u)

instance [Nonempty α] : Infinite (FreeMonoid α) := inferInstanceAs <| Infinite (List α)

instance [Infinite α] : Infinite (FreeGroup α) := by
  classical
  exact Infinite.of_surjective FreeGroup.norm _

namespace Cardinal

@[simp] theorem mk_additive : #(Additive α) = #α := rfl
@[simp] theorem mk_multiplicative : #(Multiplicative α) = #α := rfl

theorem mk_abelianization_le (G : Type u) [Group G] :
    #(Abelianization G) ≤ #G := Cardinal.mk_le_of_surjective <| surjective_quotient_mk _

@[to_additive]
theorem mk_freeMonoid [Nonempty α] :
    #(FreeMonoid α) = max #α ℵ₀ := Cardinal.mk_list_eq_max_mk_aleph0 _

@[to_additive (attr := simp)]
theorem mk_freeMonoid_of_infinite [Infinite α] :
    #(FreeMonoid α) = #α := Cardinal.mk_list_eq_mk _

theorem mk_freeGroup_of_infinite [Nonempty α]:
    #(FreeGroup α) = max #α ℵ₀ := by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    rw [mk_list_eq_max_mk_aleph0]
    simp only [mk_list_eq_mk, mk_prod, lift_id', mk_fintype, Fintype.card_bool, Nat.cast_ofNat,
      lift_ofNat]
    rw [Cardinal.mul_eq_left (by simp) _ (by simp)]
    exact (nat_lt_aleph0 2).le.trans (by simp)
  · exact mk_le_of_injective FreeGroup.of_injective


@[to_additive (attr := simp)]
theorem mk_freeGroup_of_infinite [Infinite α] :
    #(FreeGroup α) = #α := by
  classical
  apply le_antisymm
  · apply (mk_le_of_injective (FreeGroup.toWord_injective (α := α))).trans_eq
    simp only [mk_list_eq_mk, mk_prod, lift_id', mk_fintype, Fintype.card_bool, Nat.cast_ofNat,
      lift_ofNat]
    rw [Cardinal.mul_eq_left (by simp) _ (by simp)]
    exact (nat_lt_aleph0 2).le.trans (by simp)
  · exact mk_le_of_injective FreeGroup.of_injective


@[simp]
theorem mk_freeAbelianGroup_of_infinite [Infinite α] : #(FreeAbelianGroup α) = #α := by
  rw [Cardinal.mk_congr (FreeAbelianGroup.equivFinsupp α).toEquiv]
  simp

@[simp]
theorem mk_freeRing_of_infinite [Infinite α] : #(FreeRing α) = #α := by simp [FreeRing]

@[simp]
theorem mk_freeCommRing_of_infinite [Infinite α] : #(FreeCommRing α) = #α := by
  simp [FreeCommRing]

end Cardinal

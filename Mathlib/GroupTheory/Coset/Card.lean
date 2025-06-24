/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lagrange's theorem: the order of a subgroup divides the order of the group.

* `Subgroup.card_subgroup_dvd_card`: Lagrange's theorem (for multiplicative groups);
  there is an analogous version for additive groups

-/

assert_not_exists Field

open scoped Pointwise

namespace Subgroup

variable {α : Type*} [Group α]

@[to_additive AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
theorem card_eq_card_quotient_mul_card_subgroup (s : Subgroup α) :
    Nat.card α = Nat.card (α ⧸ s) * Nat.card s := by
  rw [← Nat.card_prod]; exact Nat.card_congr Subgroup.groupEquivQuotientProdSubgroup

@[to_additive]
lemma card_mul_eq_card_subgroup_mul_card_quotient (s : Subgroup α) (t : Set α) :
    Nat.card (t * s : Set α) = Nat.card s * Nat.card (t.image (↑) : Set (α ⧸ s)) := by
  rw [← Nat.card_prod, Nat.card_congr]
  apply Equiv.trans _ (QuotientGroup.preimageMkEquivSubgroupProdSet _ _)
  rw [QuotientGroup.preimage_image_mk]
  convert Equiv.refl ↑(t * s)
  aesop (add simp [Set.mem_mul])

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive "**Lagrange's Theorem**: The order of an additive subgroup divides the order of its
ambient additive group."]
theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α := by
  classical simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]

@[to_additive]
theorem card_quotient_dvd_card (s : Subgroup α) : Nat.card (α ⧸ s) ∣ Nat.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right ℕ]

variable {H : Type*} [Group H]

@[to_additive]
theorem card_dvd_of_injective (f : α →* H) (hf : Function.Injective f) :
    Nat.card α ∣ Nat.card H := by
  classical calc
      Nat.card α = Nat.card (f.range : Subgroup H) := Nat.card_congr (Equiv.ofInjective f hf)
      _ ∣ Nat.card H := card_subgroup_dvd_card _

@[to_additive]
theorem card_dvd_of_le {H K : Subgroup α} (hHK : H ≤ K) : Nat.card H ∣ Nat.card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]
theorem card_comap_dvd_of_injective (K : Subgroup H) (f : α →* H)
    (hf : Function.Injective f) : Nat.card (K.comap f) ∣ Nat.card K :=
  calc Nat.card (K.comap f) = Nat.card ((K.comap f).map f) :=
      Nat.card_congr (equivMapOfInjective _ _ hf).toEquiv
    _ ∣ Nat.card K := card_dvd_of_le (map_comap_le _ _)

end Subgroup

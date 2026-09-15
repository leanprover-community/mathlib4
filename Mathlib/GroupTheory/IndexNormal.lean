/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.GroupTheory.Index

/-! # Subgroups of small index are normal

* `Subgroup.normal_of_index_eq_smallest_prime_factor`: in a finite group `G`,
  a subgroup of index equal to the smallest prime factor of `Nat.card G` is normal.

* `Subgroup.normal_of_index_two`: in a group `G`, a subgroup of index 2 is normal
  (This does not require `G` to be finite.)

-/

public section

assert_not_exists Field

open MulAction MonoidHom Nat

variable {G : Type*} [Group G] {H : Subgroup G}

namespace Subgroup

/-- A subgroup of index 1 is normal (does not require finiteness of G) -/
@[to_additive]
theorem normal_of_index_eq_one (hH : H.index = 1) : H.Normal := by
  rw [index_eq_one] at hH
  rw [hH]
  infer_instance

/-- A subgroup of index 2 is normal (does not require finiteness of G) -/
@[to_additive]
theorem normal_of_index_eq_two (hH : H.index = 2) : H.Normal where
  conj_mem x hxH g := by simp_rw [mul_mem_iff_of_index_two hH, hxH, iff_true, inv_mem_iff]

/-- A subgroup of a finite group whose index is the smallest prime factor is normal.

Note : if `G` is infinite, then `Nat.card G = 0` and `(Nat.card G).minFac = 2` -/
theorem normal_of_index_eq_minFac_card (hHp : H.index = (Nat.card G).minFac) :
    H.Normal := by
  by_cases hG0 : Nat.card G = 0
  · rw [hG0, minFac_zero] at hHp
    exact normal_of_index_eq_two hHp
  by_cases hG1 : Nat.card G = 1
  · rw [hG1, minFac_one] at hHp
    exact normal_of_index_eq_one hHp
  suffices H.normalCore.relIndex H = 1 by
    convert! H.normalCore_normal
    exact le_antisymm (relIndex_eq_one.mp this) (normalCore_le H)
  have : Finite G := finite_of_card_ne_zero hG0
  have index_ne_zero : H.index ≠ 0 := index_ne_zero_of_finite
  rw [← mul_left_inj' index_ne_zero, one_mul, relIndex_mul_index H.normalCore_le]
  have hp : Nat.Prime H.index := hHp ▸ minFac_prime hG1
  have h : H.normalCore.index ∣ H.index ! := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (toPermHom G (G ⧸ H)).range
  apply dvd_antisymm _ (index_dvd_of_le H.normalCore_le)
  rwa [← Coprime.dvd_mul_right, mul_factorial_pred hp.ne_zero]
  have hr1 : H.normalCore.index ≠ 1 := fun hr1 ↦ hp.ne_one <|
    Nat.eq_one_of_dvd_one (hr1 ▸ H.normalCore.index_dvd_of_le H.normalCore_le)
  rw [Nat.coprime_factorial_iff hr1]
  exact lt_of_lt_of_le (Nat.sub_one_lt hp.ne_zero) <|
    hHp ▸ minFac_le_of_dvd (Nat.minFac_prime hr1).two_le
      (dvd_trans (minFac_dvd H.normalCore.index) (H.normalCore.index_dvd_card))

theorem _root_.AddSubgroup.index_normalCore_dvd_factorial_index {G : Type*} [AddGroup G]
    (H : AddSubgroup G) [H.FiniteIndex] : H.normalCore.index ∣ H.index.factorial := by
  have := QuotientAddGroup.quotientKerEquivRange (AddAction.toPermHom G (G ⧸ H))
  rw [AddSubgroup.index, H.normalCore_eq_ker, Nat.card_congr this.toEquiv, AddSubgroup.index,
    ← Nat.card_perm]
  apply AddSubgroup.card_addSubgroup_dvd_card

variable (H) in
@[to_additive existing]
theorem index_normalCore_dvd_factorial_index [H.FiniteIndex] :
    H.normalCore.index ∣ H.index.factorial := by
  have := QuotientGroup.quotientKerEquivRange <| toPermHom G (G ⧸ H)
  rw [index, H.normalCore_eq_ker, Nat.card_congr this.toEquiv, index, ← Nat.card_perm]
  apply card_subgroup_dvd_card

variable (H) in
@[to_additive]
theorem index_normalCore_le_factorial_index : H.normalCore.index ≤ H.index.factorial := by
  by_cases h : H.FiniteIndex
  · exact Nat.le_of_dvd H.index.factorial_pos H.index_normalCore_dvd_factorial_index
  have := H.normalCore.not_finiteIndex_iff.mp fun _ ↦ h <| finiteIndex_of_le H.normalCore_le
  simp [this]

end Subgroup

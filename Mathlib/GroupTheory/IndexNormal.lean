/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Finite

/-! # Subgroups of small index are normal

* `Subgroup.normal_of_index_eq_smallest_prime_factor`: in a finite group `G`,
a subgroup of index equal to the smallest prime factor of `Nat.card G` is normal.

* `Subgroup.normal_of_index_two`: in a group `G`, a subgroup of index 2 is normal
(This does not require `G` to be finite.)

-/

variable {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}

namespace Subgroup

open MulAction MonoidHom Nat

private theorem dvd_prime {r p : ℕ} (hp : p.Prime) (h : r ∣ p !)
    (hr : ∀ {l : ℕ} (_ : l.Prime) (_ : l ∣ r), p ≤ l) : r ∣ p := by
  rwa [← Coprime.dvd_mul_right, mul_factorial_pred hp.pos]
  contrapose! hr
  obtain ⟨l, hl, hl'⟩ := exists_prime_and_dvd hr
  rw [dvd_gcd_iff, hl.dvd_factorial, Nat.le_sub_one_iff_lt hp.pos] at hl'
  exact ⟨l, hl, hl'⟩

/-- A subgroup of index 1 is normal (does not require finiteness of G) -/
theorem normal_of_index_eq_one (hH : H.index = 1) : H.Normal := by
  rw [index_eq_one] at hH
  rw [hH]
  infer_instance

/-- A subgroup of index 2 is normal (does not require finiteness of G) -/
theorem normal_of_index_eq_two (hH : H.index = 2) : H.Normal where
  conj_mem x hxH g := by simp_rw [mul_mem_iff_of_index_two hH, hxH, iff_true, inv_mem_iff]

/-- A subgroup of a finite group whose index is the smallest prime factor is normal

Note : if `G` is infinite, then `Nat.card G = 0` and `(Nat.card G).minFac = 2` -/
theorem normal_of_index_eq_smallest_prime_factor (hHp : H.index = (Nat.card G).minFac) :
    H.Normal := by
  by_cases hG0 : Nat.card G = 0
  · rw [hG0, minFac_zero] at hHp
    exact normal_of_index_eq_two hHp
  by_cases hG1 : Nat.card G = 1
  · rw [hG1, minFac_one] at hHp
    exact normal_of_index_eq_one hHp
  suffices H.normalCore.relindex H = 1 by
    convert H.normalCore_normal
    exact le_antisymm (relindex_eq_one.mp this) (normalCore_le H)
  have : Finite G := finite_of_card_ne_zero hG0
  have index_ne_zero : H.index ≠ 0 := index_ne_zero_of_finite
  rw [← mul_left_inj' index_ne_zero, one_mul, relindex_mul_index H.normalCore_le]
  have hp : Nat.Prime H.index := hHp ▸ minFac_prime hG1
  have hp' {l : ℕ} (h1 : l.Prime) (h2 : l ∣ H.normalCore.index) : H.index ≤ l :=
    hHp ▸ minFac_le_of_dvd h1.two_le (h2.trans H.normalCore.index_dvd_card)
  have h : H.normalCore.index ∣ H.index ! := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (toPermHom G (G ⧸ H)).range
  exact dvd_antisymm (dvd_prime hp h hp') (index_dvd_of_le H.normalCore_le)


end Subgroup

/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Lattice
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent elements

This file develops the basic theory of nilpotent elements. In particular it shows that the
nilpotent elements are closed under many operations.

For the definition of `nilradical`, see `Mathlib/RingTheory/Nilpotent/Lemmas.lean`.


## Main definitions

  * `isNilpotent_neg_iff`
  * `Commute.isNilpotent_add`
  * `Commute.isNilpotent_sub`

-/

universe u v

open Function Set

variable {R S : Type*} {x y : R}

theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, mul_zero]

@[simp]
theorem isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩

lemma IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha : IsNilpotent a) (t : R) :
    IsNilpotent (t • a) := by
  obtain ⟨k, ha⟩ := ha
  use k
  rw [smul_pow, ha, smul_zero]

theorem IsNilpotent.isUnit_sub_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨⟨r - 1, -∑ i ∈ Finset.range n, r ^ i, ?_, ?_⟩, rfl⟩
  · simp [mul_geom_sum, hn]
  · simp [geom_sum_mul, hn]

theorem IsNilpotent.isUnit_one_sub [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (1 - r) := by
  rw [← IsUnit.neg_iff, neg_sub]
  exact isUnit_sub_one hnil

theorem IsNilpotent.isUnit_add_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r + 1) := by
  rw [← IsUnit.neg_iff, neg_add']
  exact isUnit_sub_one hnil.neg

theorem IsNilpotent.isUnit_one_add [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (1 + r) :=
  add_comm r 1 ▸ isUnit_add_one hnil

theorem IsNilpotent.isUnit_add_left_of_commute [Ring R] {r u : R}
    (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commute r u) :
    IsUnit (u + r) := by
  rw [← Units.isUnit_mul_units _ hu.unit⁻¹, add_mul, IsUnit.mul_val_inv]
  replace h_comm : Commute r (↑hu.unit⁻¹) := Commute.units_inv_right h_comm
  refine IsNilpotent.isUnit_one_add ?_
  exact (hu.unit⁻¹.isUnit.isNilpotent_mul_unit_of_commute_iff h_comm).mpr hnil

theorem IsNilpotent.isUnit_add_right_of_commute [Ring R] {r u : R}
    (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commute r u) :
    IsUnit (r + u) :=
  add_comm r u ▸ hnil.isUnit_add_left_of_commute hu h_comm

lemma IsUnit.not_isNilpotent [Ring R] [Nontrivial R] {x : R} (hx : IsUnit x) :
    ¬ IsNilpotent x := by
  intro H
  simpa using H.isUnit_add_right_of_commute hx.neg (by simp)

lemma IsNilpotent.not_isUnit [Ring R] [Nontrivial R] {x : R} (hx : IsNilpotent x) :
    ¬ IsUnit x :=
  mt IsUnit.not_isNilpotent (by simpa only [not_not] using hx)

lemma IsIdempotentElem.eq_zero_of_isNilpotent [MonoidWithZero R] {e : R}
    (idem : IsIdempotentElem e) (nilp : IsNilpotent e) : e = 0 := by
  obtain ⟨rfl | n, hn⟩ := nilp
  · rw [pow_zero] at hn; rw [← one_mul e, hn, zero_mul]
  · rw [← hn, idem.pow_succ_eq]

alias IsNilpotent.eq_zero_of_isIdempotentElem := IsIdempotentElem.eq_zero_of_isNilpotent

instance [Zero R] [Pow R ℕ] [Zero S] [Pow S ℕ] [IsReduced R] [IsReduced S] : IsReduced (R × S) where
  eq_zero _ := fun ⟨n, hn⟩ ↦ have hn := Prod.ext_iff.1 hn
    Prod.ext (IsReduced.eq_zero _ ⟨n, hn.1⟩) (IsReduced.eq_zero _ ⟨n, hn.2⟩)

theorem Prime.isRadical [CommMonoidWithZero R] {y : R} (hy : Prime y) : IsRadical y :=
  fun _ _ ↦ hy.dvd_of_dvd_pow

theorem zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R := by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_swap

theorem isReduced_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsReduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 := by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]

theorem IsRadical.of_dvd [CancelCommMonoidWithZero R] {x y : R} (hy : IsRadical y) (h0 : y ≠ 0)
    (hxy : x ∣ y) : IsRadical x := (isRadical_iff_pow_one_lt 2 one_lt_two).2 <| by
  obtain ⟨z, rfl⟩ := hxy
  refine fun w dvd ↦ ((mul_dvd_mul_iff_right <| right_ne_zero_of_mul h0).mp <| hy 2 _ ?_)
  rw [mul_pow]
  gcongr
  exact dvd_pow_self _ two_ne_zero

namespace Commute

section Semiring

variable [Semiring R]

theorem add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (h_comm : Commute x y) {m n k : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) (h : m + n ≤ k + 1) :
    (x + y) ^ k = 0 := by
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  by_cases hi : m ≤ i
  · rw [pow_eq_zero_of_le hi hx, zero_mul]
  rw [pow_eq_zero_of_le ?_ hy, mul_zero]
  linarith [Finset.mem_antidiagonal.mp hij]

theorem add_pow_add_eq_zero_of_pow_eq_zero (h_comm : Commute x y) {m n : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) :
    (x + y) ^ (m + n - 1) = 0 :=
  h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hy <| by rw [← Nat.sub_le_iff_le_add]

theorem isNilpotent_add (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  exact ⟨_, add_pow_add_eq_zero_of_pow_eq_zero h_comm hn hm⟩

protected lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) (h_comm : ∀ i j, i ∈ s → j ∈ s → Commute (f i) (f j)) :
    IsNilpotent (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi ↦ h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi ↦ hnp i (by simp [hi]))
      (fun i j hi hj ↦ h_comm i j (by simp [hi]) (by simp [hj]))

theorem isNilpotent_finsum {ι : Type*} {f : ι → R}
    (hf : ∀ b, IsNilpotent (f b)) (h_comm : ∀ i j, Commute (f i) (f j)) :
    IsNilpotent (finsum f) := by
  classical
  by_cases h : Set.Finite f.support
  · rw [finsum_def, dif_pos h]
    exact Commute.isNilpotent_sum (fun b _ ↦ hf b) (fun _ _ _ _ ↦ h_comm _ _)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]

protected lemma isNilpotent_mul_right_iff (h_comm : Commute x y) (hy : y ∈ nonZeroDivisorsRight R) :
    IsNilpotent (x * y) ↔ IsNilpotent x := by
  refine ⟨?_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hy k _ hk⟩

protected lemma isNilpotent_mul_left_iff (h_comm : Commute x y) (hx : x ∈ nonZeroDivisorsLeft R) :
    IsNilpotent (x * y) ↔ IsNilpotent y := by
  refine ⟨?_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hx k _ hk⟩

end Semiring

section Ring

variable [Ring R]

theorem isNilpotent_sub (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x - y) := by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy

end Ring

end Commute

section CommSemiring

variable [CommSemiring R] {x y : R}

lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) :
    IsNilpotent (∑ i ∈ s, f i) :=
  Commute.isNilpotent_sum hnp fun _ _ _ _ ↦ Commute.all _ _

theorem isNilpotent_finsum {ι : Type*} {f : ι → R}
    (hf : ∀ b, IsNilpotent (f b)) :
    IsNilpotent (finsum f) :=
  Commute.isNilpotent_finsum hf fun _ _ ↦ Commute.all _ _

end CommSemiring

lemma NoZeroSMulDivisors.isReduced (R M : Type*)
    [MonoidWithZero R] [Zero M] [MulActionWithZero R M] [Nontrivial M] [NoZeroSMulDivisors R M] :
    IsReduced R := by
  refine ⟨fun x ⟨k, hk⟩ ↦ ?_⟩
  induction k with
  | zero =>
    rw [pow_zero] at hk
    exact eq_zero_of_zero_eq_one hk.symm x
  | succ k ih =>
    obtain ⟨m : M, hm : m ≠ 0⟩ := exists_ne (0 : M)
    have : x ^ (k + 1) • m = 0 := by simp only [hk, zero_smul]
    rw [pow_succ', mul_smul] at this
    rcases eq_zero_or_eq_zero_of_smul_eq_zero this with rfl | hx
    · rfl
    · exact ih <| (eq_zero_or_eq_zero_of_smul_eq_zero hx).resolve_right hm

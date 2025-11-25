/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2024 Q2

Determine all pairs $(a,b)$ of positive integers for which there exist positive integers
$g$ and $N$ such that
\[ \gcd(a^n + b, b^n + a) = g \]
holds for all integers $n \ge N$.

We consider the sequence modulo `ab+1`; if the exponent is `-1` modulo `φ(ab+1)`, the terms
are zero modulo `ab+1`, so `ab+1` divides `g`, and all sufficiently large terms, so all terms,
from which we conclude that `a=b=1`.
-/


namespace Imo2024Q2

open scoped Nat

/-- The condition of the problem. -/
def Condition (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ ∃ g N : ℕ, 0 < g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = g

lemma dvd_pow_iff_of_dvd_sub {a b d n : ℕ} {z : ℤ} (ha : a.Coprime d)
    (hd : (φ d : ℤ) ∣ (n : ℤ) - z) :
    d ∣ a ^ n + b ↔ (((ZMod.unitOfCoprime _ ha) ^ z : (ZMod d)ˣ) : ZMod d) + b = 0 := by
  rcases hd with ⟨k, hk⟩
  rw [← ZMod.natCast_eq_zero_iff]
  convert Iff.rfl
  push_cast
  congr
  suffices (((ZMod.unitOfCoprime _ ha) ^ z : (ZMod d)ˣ) : ZMod d) =
      (((ZMod.unitOfCoprime _ ha) ^ (n : ℤ) : (ZMod d)ˣ) : ZMod d) by
    convert this
  rw [sub_eq_iff_eq_add] at hk
  rw [hk, zpow_add, zpow_mul]
  norm_cast
  rw [ZMod.pow_totient, one_zpow, one_mul]

namespace Condition

variable {a b : ℕ} (h : Condition a b)

section
include h

lemma a_pos : 0 < a := h.1

lemma b_pos : 0 < b := h.2.1

/-- The value of `g` in the problem (determined by `a` and `b`). -/
noncomputable def g : ℕ := h.2.2.choose

lemma g_spec : ∃ N : ℕ, 0 < h.g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = h.g :=
  h.2.2.choose_spec

/-- The value of `N` in the problem (any sufficiently large value). -/
noncomputable def N : ℕ := h.g_spec.choose

lemma N_spec : 0 < h.g ∧ 0 < h.N ∧ ∀ n : ℕ, h.N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = h.g :=
  h.g_spec.choose_spec

lemma g_pos : 0 < h.g := h.N_spec.1

lemma N_pos : 0 < h.N := h.N_spec.2.1

lemma gcd_eq_g {n : ℕ} (hn : h.N ≤ n) : Nat.gcd (a ^ n + b) (b ^ n + a) = h.g := h.N_spec.2.2 n hn

protected lemma symm : Condition b a := by
  refine ⟨h.b_pos, h.a_pos, h.g, h.N, h.g_pos, h.N_pos, fun n hn ↦ ?_⟩
  rw [Nat.gcd_comm]
  exact h.gcd_eq_g hn

lemma dvd_g_of_le_N_of_dvd {n : ℕ} (hn : h.N ≤ n) {d : ℕ} (hab : d ∣ a ^ n + b)
    (hba : d ∣ b ^ n + a) : d ∣ h.g := by
  rw [← h.gcd_eq_g hn, Nat.dvd_gcd_iff]
  exact ⟨hab, hba⟩

end

lemma a_coprime_ab_add_one : a.Coprime (a * b + 1) := by
  simp

/-- A sufficiently large value of n, congruent to `-1` mod `φ (a * b + 1)`. -/
noncomputable def large_n : ℕ := (max h.N h.symm.N + 1) * φ (a * b + 1) - 1

lemma symm_large_n : h.symm.large_n = h.large_n := by
  simp_rw [large_n]
  congr 2
  · rw [max_comm]
  · rw [mul_comm]

lemma N_le_large_n : h.N ≤ h.large_n := by
  have hp : 0 < φ (a * b + 1) := Nat.totient_pos.2 (Nat.add_pos_right _ zero_lt_one)
  rw [large_n, add_mul, one_mul, Nat.add_sub_assoc (Nat.one_le_of_lt hp)]
  suffices h.N ≤ h.N * φ (a * b + 1) + (φ (a * b + 1) - 1) by
    refine this.trans ?_
    gcongr
    simp
  exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right _ hp)

lemma dvd_large_n_sub_neg_one : (φ (a * b + 1) : ℤ) ∣ (h.large_n : ℤ) - (-1 : ℤ) := by
  simp [large_n]

/-- A sufficiently large value of n, congruent to `0` mod `φ (a * b + 1)`. -/
noncomputable def large_n_0 : ℕ := (max h.N h.symm.N) * φ (a * b + 1)

lemma symm_large_n_0 : h.symm.large_n_0 = h.large_n_0 := by
  simp_rw [large_n_0]
  congr 1
  · rw [max_comm]
  · rw [mul_comm]

lemma N_le_large_n_0 : h.N ≤ h.large_n_0 := by
  have hp : 0 < φ (a * b + 1) := Nat.totient_pos.2 (Nat.add_pos_right _ zero_lt_one)
  rw [large_n_0]
  suffices h.N ≤ h.N * φ (a * b + 1) by
    refine this.trans ?_
    gcongr
    simp
  exact Nat.le_mul_of_pos_right _ hp

lemma dvd_large_n_0_sub_zero : (φ (a * b + 1) : ℤ) ∣ (h.large_n_0 : ℤ) - (0 : ℤ) := by
  simp [large_n_0]

lemma ab_add_one_dvd_a_pow_large_n_add_b : a * b + 1 ∣ a ^ h.large_n + b := by
  rw [dvd_pow_iff_of_dvd_sub a_coprime_ab_add_one h.dvd_large_n_sub_neg_one, zpow_neg, zpow_one]
  suffices ((ZMod.unitOfCoprime _ a_coprime_ab_add_one : (ZMod (a * b + 1))ˣ) : ZMod (a * b + 1)) *
    ((((ZMod.unitOfCoprime _ a_coprime_ab_add_one)⁻¹ : (ZMod (a * b + 1))ˣ) :
      ZMod (a * b + 1)) + (b : ZMod (a * b + 1))) = 0 from
      (IsUnit.mul_right_eq_zero (ZMod.unitOfCoprime _ a_coprime_ab_add_one).isUnit).1 this
  rw [mul_add]
  norm_cast
  simp only [mul_inv_cancel, Units.val_one, ZMod.coe_unitOfCoprime]
  norm_cast
  convert ZMod.natCast_self (a * b + 1) using 2
  exact add_comm _ _

lemma ab_add_one_dvd_b_pow_large_n_add_a : a * b + 1 ∣ b ^ h.large_n + a := by
  convert h.symm.ab_add_one_dvd_a_pow_large_n_add_b using 1
  · rw [mul_comm]
  · rw [h.symm_large_n]

lemma ab_add_one_dvd_g : a * b + 1 ∣ h.g :=
  h.dvd_g_of_le_N_of_dvd h.N_le_large_n h.ab_add_one_dvd_a_pow_large_n_add_b
    h.ab_add_one_dvd_b_pow_large_n_add_a

lemma ab_add_one_dvd_a_pow_large_n_0_add_b : a * b + 1 ∣ a ^ h.large_n_0 + b := by
  refine h.ab_add_one_dvd_g.trans ?_
  rw [← h.gcd_eq_g h.N_le_large_n_0]
  exact Nat.gcd_dvd_left _ _

include h

lemma ab_add_one_dvd_b_add_one : a * b + 1 ∣ b + 1 := by
  rw [add_comm b]
  suffices a * b + 1 ∣ a ^ h.large_n_0 + b by
    rw [dvd_pow_iff_of_dvd_sub a_coprime_ab_add_one h.dvd_large_n_0_sub_zero, zpow_zero] at this
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    norm_cast at this
  exact h.ab_add_one_dvd_a_pow_large_n_0_add_b

lemma a_eq_one : a = 1 := by
  have hle : a * b + 1 ≤ b + 1 := Nat.le_of_dvd (by omega) h.ab_add_one_dvd_b_add_one
  rw [add_le_add_iff_right] at hle
  suffices a ≤ 1 by
    have hp := h.a_pos
    omega
  have hle' : a * b ≤ 1 * b := by
    simpa using hle
  exact Nat.le_of_mul_le_mul_right hle' h.b_pos

lemma b_eq_one : b = 1 := h.symm.a_eq_one

end Condition

/-- This is to be determined by the solver of the original problem. -/
def solutionSet : Set (ℕ × ℕ) := {(1, 1)}

theorem result (a b : ℕ) : Condition a b ↔ (a, b) ∈ solutionSet := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [solutionSet, Set.mem_singleton_iff, Prod.mk.injEq]
    exact ⟨h.a_eq_one, h.b_eq_one⟩
  · simp only [solutionSet, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [Condition]
    refine ⟨by decide, by decide, 2, 1, ?_⟩
    simp

end Imo2024Q2

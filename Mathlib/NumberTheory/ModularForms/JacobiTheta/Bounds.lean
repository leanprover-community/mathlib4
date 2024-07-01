/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Asymptotic bounds for Jacobi theta functions

The goal of this file is to establish some technical lemmas about the asymptotics of the sums

`F_nat k a t = ∑' (n : ℕ), (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)`

and

`F_int k a t = ∑' (n : ℤ), |n + a| ^ k * exp (-π * (n + a) ^ 2 * t).`

Here `k : ℕ` and `a : ℝ` (resp `a : UnitAddCircle`) are fixed, and we are interested in
asymptotics as `t → ∞`. These results are needed for the theory of Hurwitz zeta functions (and
hence Dirichlet L-functions, etc).

## Main results

* `HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub` : for `0 ≤ a`, the function
  `F_nat 0 a - (if a = 0 then 1 else 0)` decays exponentially at `∞` (i.e. it satisfies
  `=O[atTop] fun t ↦ exp (-p * t)` for some real `0 < p`).
* `HurwitzKernelBounds.isBigO_atTop_F_nat_one` : for `0 ≤ a`, the function `F_nat 1 a` decays
  exponentially at `∞`.
* `HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub` : for any `a : UnitAddCircle`, the function
  `F_int 0 a - (if a = 0 then 1 else 0)` decays exponentially at `∞`.
* `HurwitzKernelBounds.isBigO_atTop_F_int_one`: the function `F_int 1 a` decays exponentially at
  `∞`.
-/

open Set Filter Topology Asymptotics Real Classical

noncomputable section

namespace HurwitzKernelBounds

section lemmas

lemma isBigO_exp_neg_mul_of_le {c d : ℝ} (hcd : c ≤ d) :
    (fun t ↦ exp (-d * t)) =O[atTop] fun t ↦ exp (-c * t) := by
  apply Eventually.isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  rwa [norm_of_nonneg (exp_pos _).le, exp_le_exp, mul_le_mul_right ht, neg_le_neg_iff]

private lemma exp_lt_aux {t : ℝ} (ht : 0 < t) : rexp (-π * t) < 1 := by
  simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos ht

private lemma isBigO_one_aux :
    IsBigO atTop (fun t : ℝ ↦ (1 - rexp (-π * t))⁻¹) (fun _ ↦ (1 : ℝ)) := by
  refine ((Tendsto.const_sub _ ?_).inv₀ (by norm_num)).isBigO_one ℝ (c := ((1 - 0)⁻¹ : ℝ))
  simpa only [neg_mul, tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
    using tendsto_id.const_mul_atTop pi_pos

end lemmas


section nat

/-- Summand in the sum to be bounded (`ℕ` version). -/
def f_nat (k : ℕ) (a t : ℝ) (n : ℕ) : ℝ := (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)

/-- An upper bound for the summand when `0 ≤ a`. -/
def g_nat (k : ℕ) (a t : ℝ) (n : ℕ) : ℝ := (n + a) ^ k * exp (-π * (n + a ^ 2) * t)

lemma f_le_g_nat (k : ℕ) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (n : ℕ) :
    ‖f_nat k a t n‖ ≤ g_nat k a t n := by
  rw [f_nat, norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_exp, mul_le_mul_right ht,
    mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos), ← sub_nonneg]
  have u : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    simpa only [← Nat.cast_pow, Nat.cast_le] using Nat.le_self_pow two_ne_zero _
  convert add_nonneg (sub_nonneg.mpr u) (by positivity : 0 ≤ 2 * n * a) using 1
  ring

/-- The sum to be bounded (`ℕ` version). -/
def F_nat (k : ℕ) (a t : ℝ) : ℝ := ∑' n, f_nat k a t n

lemma summable_f_nat (k : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) : Summable (f_nat k a t) := by
  have : Summable fun n : ℕ ↦ n ^ k * exp (-π * (n + a) ^ 2 * t) := by
    refine (((summable_pow_mul_jacobiTheta₂_term_bound (|a| * t) ht k).mul_right
      (rexp (-π * a ^ 2 * t))).comp_injective Nat.cast_injective).of_norm_bounded _ (fun n ↦ ?_)
    simp_rw [mul_assoc, Function.comp_apply, ← Real.exp_add, norm_mul, norm_pow, Int.cast_abs,
      Int.cast_natCast, norm_eq_abs, Nat.abs_cast, abs_exp]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg _) _)
    rw [exp_le_exp, ← sub_nonneg]
    rw [show -π * (t * n ^ 2 - 2 * (|a| * (t * n))) + -π * (a ^ 2 * t) - -π * ((n + a) ^ 2 * t)
         = π * t * n * (|a| + a) * 2 by ring]
    refine mul_nonneg (mul_nonneg (by positivity) ?_) two_pos.le
    rw [← neg_le_iff_add_nonneg]
    apply neg_le_abs
  apply (this.mul_left (2 ^ k)).of_norm_bounded_eventually_nat
  simp_rw [← mul_assoc, f_nat, norm_mul, norm_eq_abs, abs_exp,
    mul_le_mul_iff_of_pos_right (exp_pos _), ← mul_pow, abs_pow, two_mul]
  filter_upwards [eventually_ge_atTop (Nat.ceil |a|)] with n hn
  apply pow_le_pow_left (abs_nonneg _) ((abs_add_le _ _).trans
    (add_le_add (le_of_eq (Nat.abs_cast _)) (Nat.ceil_le.mp hn)))

section k_eq_zero

/-!
## Sum over `ℕ` with `k = 0`

Here we use direct comparison with a geometric series.
-/

lemma F_nat_zero_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    ‖F_nat 0 a t‖ ≤ rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 0 ha ht)
  convert (hasSum_geometric_of_lt_one (exp_pos _).le <| exp_lt_aux ht).mul_left _ using 1
  ext1 n
  simp only [g_nat]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  ring_nf

lemma F_nat_zero_zero_sub_le {t : ℝ} (ht : 0 < t) :
    ‖F_nat 0 0 t - 1‖ ≤ rexp (-π * t) / (1 - rexp (-π * t)) := by
  convert F_nat_zero_le zero_le_one ht using 2
  · rw [F_nat, tsum_eq_zero_add (summable_f_nat 0 0 ht), f_nat, Nat.cast_zero, add_zero, pow_zero,
      one_mul, pow_two, mul_zero, mul_zero, zero_mul, exp_zero, add_comm, add_sub_cancel_right]
    simp_rw [F_nat, f_nat, Nat.cast_add, Nat.cast_one, add_zero]
  · rw [one_pow, mul_one]

lemma isBigO_atTop_F_nat_zero_sub {a : ℝ} (ha : 0 ≤ a) : ∃ p, 0 < p ∧
    (fun t ↦ F_nat 0 a t - (if a = 0 then 1 else 0)) =O[atTop] fun t ↦ exp (-p * t) := by
  split_ifs with h
  · rw [h]
    have : (fun t ↦ F_nat 0 0 t - 1) =O[atTop] fun t ↦ rexp (-π * t) / (1 - rexp (-π * t)) := by
      apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_zero_sub_le ht
    refine ⟨_, pi_pos, this.trans ?_⟩
    simpa using (isBigO_refl (fun t ↦ rexp (-π * t)) _).mul isBigO_one_aux
  · simp_rw [sub_zero]
    have : (fun t ↦ F_nat 0 a t) =O[atTop] fun t ↦ rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
      apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_le ha ht
    refine ⟨π * a ^ 2, mul_pos pi_pos (sq_pos_of_ne_zero h), this.trans ?_⟩
    simpa only [neg_mul π (a ^ 2), mul_one] using (isBigO_refl _ _).mul isBigO_one_aux

end k_eq_zero

section k_eq_one

/-!
## Sum over `ℕ` with `k = 1`

Here we use comparison with the series `∑ n * r ^ n`, where `r = exp (-π * t)`.
-/

lemma F_nat_one_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    ‖F_nat 1 a t‖ ≤ rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 1 ha ht)
  unfold g_nat
  simp_rw [pow_one, add_mul]
  apply HasSum.add
  · have h0' : ‖rexp (-π * t)‖ < 1 := by
      simpa only [norm_eq_abs, abs_exp] using exp_lt_aux ht
    convert (hasSum_coe_mul_geometric_of_norm_lt_one h0').mul_left (exp (-π * a ^ 2 * t)) using 1
    · ext1 n
      rw [mul_comm (exp _), ← Real.exp_nat_mul, mul_assoc (n : ℝ), ← Real.exp_add]
      ring_nf
    · rw [mul_add, add_mul, mul_one, exp_add, mul_div_assoc]
  · convert (hasSum_geometric_of_lt_one (exp_pos _).le <| exp_lt_aux ht).mul_left _ using 1
    ext1 n
    rw [← Real.exp_nat_mul, mul_assoc _ (exp _), ← Real.exp_add]
    ring_nf

lemma isBigO_atTop_F_nat_one {a : ℝ} (ha : 0 ≤ a) : ∃ p, 0 < p ∧
    F_nat 1 a =O[atTop] fun t ↦ exp (-p * t) := by
  suffices ∃ p, 0 < p ∧ (fun t ↦ rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))) =O[atTop] fun t ↦ exp (-p * t) by
    let ⟨p, hp, hp'⟩ := this
    refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact F_nat_one_le ha ht
  have aux' : IsBigO atTop (fun t : ℝ ↦ ((1 - rexp (-π * t)) ^ 2)⁻¹) (fun _ ↦ (1 : ℝ)) := by
    simpa only [inv_pow, one_pow] using isBigO_one_aux.pow 2
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact ⟨_, pi_pos, by simpa only [zero_pow two_ne_zero, zero_add, mul_one, zero_mul, zero_div,
      add_zero] using (isBigO_refl _ _).mul aux'⟩
  · refine ⟨π * a ^ 2, mul_pos pi_pos <| pow_pos ha' _, IsBigO.add ?_ ?_⟩
    · conv_rhs => enter [t]; rw [← mul_one (rexp _)]
      refine (Eventually.isBigO ?_).mul aux'
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_of_nonneg (exp_pos _).le, exp_le_exp]
      nlinarith [pi_pos]
    · simp_rw [mul_div_assoc, ← neg_mul]
      apply IsBigO.const_mul_left
      simpa only [mul_one] using (isBigO_refl _ _).mul isBigO_one_aux

end k_eq_one

end nat

section int

/-- Summand in the sum to be bounded (`ℤ` version). -/
def f_int (k : ℕ) (a t : ℝ) (n : ℤ) : ℝ := |n + a| ^ k * exp (-π * (n + a) ^ 2 * t)

lemma f_int_ofNat (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (n : ℕ) :
    f_int k a t (Int.ofNat n) = f_nat k a t n := by
  rw [f_int, f_nat, Int.ofNat_eq_coe, Int.cast_natCast, abs_of_nonneg (by positivity)]

lemma f_int_negSucc (k : ℕ) {a : ℝ} (ha : a ≤ 1) (t : ℝ) (n : ℕ) :
    f_int k a t (Int.negSucc n) = f_nat k (1 - a) t n := by
  have : (Int.negSucc n) + a = -(n + (1 - a)) := by { push_cast; ring }
  rw [f_int, f_nat, this, abs_neg, neg_sq, abs_of_nonneg (by linarith)]

lemma summable_f_int (k : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) : Summable (f_int k a t) := by
  apply Summable.of_norm
  suffices ∀ n, ‖f_int k a t n‖ = ‖(Int.rec (f_nat k a t) (f_nat k (1 - a) t) : ℤ → ℝ) n‖ from
    funext this ▸ (HasSum.int_rec (summable_f_nat k a ht).hasSum
      (summable_f_nat k (1 - a) ht).hasSum).summable.norm
  intro n
  cases' n with m m
  · simp only [f_int, f_nat, Int.ofNat_eq_coe, Int.cast_natCast, norm_mul, norm_eq_abs, abs_pow,
      abs_abs]
  · simp only [f_int, f_nat, Int.cast_negSucc, norm_mul, norm_eq_abs, abs_pow, abs_abs,
      (by { push_cast; ring } : -↑(m + 1) + a = -(m + (1 - a))), abs_neg, neg_sq]

/-- The sum to be bounded (`ℤ` version). -/
def F_int (k : ℕ) (a : UnitAddCircle) (t : ℝ) : ℝ :=
  (show Function.Periodic (fun b ↦ ∑' (n : ℤ), f_int k b t n) 1 by
    intro b
    simp_rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (f := fun n ↦ f_int k b t n)]
    simp only [f_int, ← add_assoc, add_comm, Equiv.coe_addRight, Int.cast_add, Int.cast_one]
    ).lift a

lemma F_int_eq_of_mem_Icc (k : ℕ) {a : ℝ} (ha : a ∈ Icc 0 1) {t : ℝ} (ht : 0 < t) :
    F_int k a t = (F_nat k a t) + (F_nat k (1 - a) t) := by
  simp only [F_int, F_nat, Function.Periodic.lift_coe]
  convert ((summable_f_nat k a ht).hasSum.int_rec (summable_f_nat k (1 - a) ht).hasSum).tsum_eq
    using 3 with n
  cases' n with m m
  · rw [f_int_ofNat _ ha.1]
  · rw [f_int_negSucc _ ha.2]

lemma isBigO_atTop_F_int_zero_sub (a : UnitAddCircle) : ∃ p, 0 < p ∧
    (fun t ↦ F_int 0 a t - (if a = 0 then 1 else 0)) =O[atTop] fun t ↦ exp (-p * t) := by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_zero_sub ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_zero_sub (sub_nonneg.mpr ha.2.le)
  have ha' : (a : UnitAddCircle) = 0 ↔ a = 0 := by
    rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico (hp := ⟨zero_lt_one' ℝ⟩), QuotientAddGroup.mk_zero]
    · rw [zero_add]; exact ha
    · simp
  simp_rw [ha']
  simp_rw [eq_false_intro (by linarith [ha.2] : 1 - a ≠ 0), if_false, sub_zero] at hq'
  refine ⟨_, lt_min hp hq, ?_⟩
  have : (fun t ↦ F_int 0 a t - (if a = 0 then 1 else 0)) =ᶠ[atTop]
      fun t ↦ (F_nat 0 a t - (if a = 0 then 1 else 0)) + F_nat 0 (1 - a) t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [F_int_eq_of_mem_Icc 0 (Ico_subset_Icc_self ha) ht]
    ring
  refine this.isBigO.trans ((hp'.trans ?_).add (hq'.trans ?_)) <;>
  apply isBigO_exp_neg_mul_of_le
  exacts [min_le_left .., min_le_right ..]

lemma isBigO_atTop_F_int_one (a : UnitAddCircle) : ∃ p, 0 < p ∧
    F_int 1 a =O[atTop] fun t ↦ exp (-p * t) := by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_one ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_one (sub_nonneg.mpr ha.2.le)
  refine ⟨_, lt_min hp hq, ?_⟩
  have : F_int 1 a =ᶠ[atTop] fun t ↦ F_nat 1 a t + F_nat 1 (1 - a) t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact F_int_eq_of_mem_Icc 1 (Ico_subset_Icc_self ha) ht
  refine this.isBigO.trans ((hp'.trans ?_).add (hq'.trans ?_)) <;>
  apply isBigO_exp_neg_mul_of_le
  exacts [min_le_left .., min_le_right ..]

end int

end HurwitzKernelBounds

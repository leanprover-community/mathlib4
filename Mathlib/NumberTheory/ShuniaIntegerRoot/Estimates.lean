/-
Copyright (c) 2026 Ravi Bajaj and Alexander Benjamin Worth Burns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Bajaj, Alexander Benjamin Worth Burns
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Quantitative estimates for Shunia's integer-root formula

This file proves the uniform spectral estimate used in the proof of Shunia's integer-root
formula.  If `α = a ^ (1 / n)` and

`q = sqrt (1 + α ^ 2 + 2 * α * cos (2 * π / n)) / (1 + α)`,

then, under the admissibility hypotheses, `(n - 1) * q ^ (2 * a * n)` is smaller than
`1 / (16 * n * a ^ 2)`.
-/

open Real

namespace ShuniaIntegerRoot

private lemma nat_le_two_pow_pred {n : ℕ} (hn : 1 ≤ n) : n ≤ 2 ^ (n - 1) := by
  have h := (n - 1).lt_two_pow_self
  omega

private lemma nat_sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private lemma baseline_target_le_two_pow {n : ℕ} (hn : 1 ≤ n) :
    16 * n * (n - 1) * (2 ^ (n - 1)) ^ 2 ≤ 2 ^ (4 * n) := by
  have h₁ := nat_le_two_pow_pred hn
  have h₂ : n - 1 ≤ 2 ^ (n - 1) := (Nat.sub_le n 1).trans h₁
  calc
    16 * n * (n - 1) * (2 ^ (n - 1)) ^ 2
        ≤ 16 * (2 ^ (n - 1)) * (2 ^ (n - 1)) * (2 ^ (n - 1)) ^ 2 := by
          gcongr
    _ = 2 ^ (4 * n) := by
      rw [show 16 = 2 ^ 4 by norm_num]
      simp only [← pow_add, ← pow_mul]
      congr 1
      omega

private lemma log_two_lt_three_four : Real.log 2 < (3 : ℝ) / 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ) / 4) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  exact lt_of_lt_of_le (by norm_num) h

private lemma eight_thirds_lt_exp_one : (8 : ℝ) / 3 < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h ⊢
  exact lt_of_lt_of_le (by norm_num) h

private lemma exp_neg_lt_inv {T P : ℝ} (hT : 0 < T) (hlog : Real.log T < P) :
    Real.exp (-P) < 1 / T := by
  calc
    Real.exp (-P) < Real.exp (-Real.log T) := Real.exp_lt_exp.mpr (neg_lt_neg hlog)
    _ = 1 / T := by rw [Real.exp_neg, Real.exp_log hT]; simp [one_div]

private lemma baseline_exponent_bound {n : ℕ} (hn : 3 ≤ n) :
    Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * ((2 : ℝ) ^ (n - 1)) ^ 2) <
      6 * (2 : ℝ) ^ (n - 1) / n := by
  rcases eq_or_lt_of_le hn with rfl | hn4
  · norm_num only [Nat.cast_ofNat, Nat.cast_sub (by omega), Nat.cast_one,
      Nat.reduceSubDiff, Nat.reducePow, Nat.cast_pow]
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hp : (8 / 3 : ℝ) ^ 8 < Real.exp 8 := by
      calc
        _ < (Real.exp 1) ^ 8 :=
          pow_lt_pow_left₀ eight_thirds_lt_exp_one (by positivity) (by norm_num)
        _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
    exact (by norm_num : (1536 : ℝ) < (8 / 3) ^ 8).trans hp
  · have htarget :
        (16 * (n : ℝ) * (↑(n - 1) : ℝ) * ((2 : ℝ) ^ (n - 1)) ^ 2) ≤
          (2 : ℝ) ^ (4 * n) := by
      exact_mod_cast baseline_target_le_two_pow (show 1 ≤ n by omega)
    have hpos :
        0 < 16 * (n : ℝ) * (↑(n - 1) : ℝ) * ((2 : ℝ) ^ (n - 1)) ^ 2 := by
      have hn1pos : 0 < n - 1 := by omega
      positivity
    have hlog :
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * ((2 : ℝ) ^ (n - 1)) ^ 2) ≤
          (4 * n : ℝ) * Real.log 2 := by
      calc
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * ((2 : ℝ) ^ (n - 1)) ^ 2)
            ≤ Real.log ((2 : ℝ) ^ (4 * n)) := Real.log_le_log hpos htarget
        _ = (4 * n : ℕ) * Real.log 2 := Real.log_pow 2 (4 * n)
        _ = (4 * n : ℝ) * Real.log 2 := by norm_num
    have hlog3 :
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * ((2 : ℝ) ^ (n - 1)) ^ 2) <
          3 * n := by
      calc
        _ ≤ (4 * n : ℝ) * Real.log 2 := hlog
        _ < (4 * n : ℝ) * ((3 : ℝ) / 4) :=
          mul_lt_mul_of_pos_left log_two_lt_three_four (by positivity)
        _ = 3 * n := by ring
    have hsquare' : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
      exact_mod_cast nat_sq_le_two_pow (show 4 ≤ n by omega)
    have hL : (3 : ℝ) * n ≤ 6 * (2 : ℝ) ^ (n - 1) / n := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < n)]
      calc
        3 * (n : ℝ) * n = 3 * (n : ℝ) ^ 2 := by ring
        _ ≤ 3 * (2 : ℝ) ^ n := by gcongr
        _ = 6 * (2 : ℝ) ^ (n - 1) := by
          rw [← mul_pow_sub_one (n := n) (by omega) (2 : ℝ)]
          ring
    exact hlog3.trans_le hL

private lemma two_ninths_le_root_factor {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) :
    (2 : ℝ) / 9 ≤ x / (1 + x) ^ 2 := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 9) (sq_pos_of_pos (by linarith))]
  have hprod : 0 ≤ (2 * x - 1) * (2 - x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private lemma four_ninths_div_le_root_factor {x : ℝ} (hx : 2 ≤ x) :
    (4 : ℝ) / (9 * x) ≤ x / (1 + x) ^ 2 := by
  rw [div_le_div_iff₀ (mul_pos (by norm_num) (by linarith))
    (sq_pos_of_pos (by linarith))]
  have hprod : 0 ≤ (x - 2) * (5 * x + 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private lemma exponent_gt_log_of_pow {a n : ℕ} {α : ℝ}
    (hn : 3 ≤ n) (ha₀ : 2 ^ (n - 1) ≤ a)
    (hα₁ : 1 ≤ α) (hαpow : α ^ n = (a : ℝ)) :
    Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (a : ℝ) ^ 2) <
      27 * (a : ℝ) * α / ((n : ℝ) * (1 + α) ^ 2) := by
  let A : ℝ := (2 : ℝ) ^ (n - 1)
  let L : ℝ := 6 * A / n
  let R : ℝ := Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2)
  have hApos : 0 < A := by dsimp [A]; positivity
  have hn1pos : 0 < n - 1 := by omega
  have haNat : 0 < a := lt_of_lt_of_le (by positivity : 0 < 2 ^ (n - 1)) ha₀
  have hR_L : R < L := by
    simpa only [A, L, R] using baseline_exponent_bound hn
  have hnA' : (n : ℝ) ≤ A := by
    dsimp [A]
    exact_mod_cast nat_le_two_pow_pred (show 1 ≤ n by omega)
  have hL6 : 6 ≤ L := by
    dsimp [L]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < n)]
    nlinarith
  rcases le_total α 2 with hα₂ | hα₂
  · let s : ℝ := (a : ℝ) / A
    have hspos : 0 < s := by dsimp [s]; positivity
    have hs₁ : 1 ≤ s := by
      dsimp [s]
      rw [le_div_iff₀ hApos]
      dsimp [A]
      simpa using (show ((2 : ℝ) ^ (n - 1) ≤ (a : ℝ)) by exact_mod_cast ha₀)
    have ha_eq : (a : ℝ) = A * s := by
      dsimp [s]
      field_simp
    have hlog_eq :
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (a : ℝ) ^ 2) =
          R + 2 * Real.log s := by
      rw [ha_eq]
      have hbase_ne :
          16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2 ≠ 0 := by positivity
      calc
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (A * s) ^ 2)
            = Real.log ((16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2) * s ^ 2) := by
                congr 1
                ring
        _ = Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2) +
              Real.log (s ^ 2) := Real.log_mul hbase_ne (pow_ne_zero 2 hspos.ne')
        _ = R + 2 * Real.log s := by rw [Real.log_pow]; simp [R]
    have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
    have hsmall : R + 2 * Real.log s < L * s := by
      have hmul : 2 * (s - 1) ≤ L * (s - 1) :=
        mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ L) (sub_nonneg.mpr hs₁)
      nlinarith
    have hfac := two_ninths_le_root_factor hα₁ hα₂
    have hP :
        6 * (a : ℝ) / n ≤
          27 * (a : ℝ) * α / ((n : ℝ) * (1 + α) ^ 2) := by
      calc
        6 * (a : ℝ) / n =
            (27 * (a : ℝ) / n) * ((2 : ℝ) / 9) := by ring
        _ ≤ (27 * (a : ℝ) / n) * (α / (1 + α) ^ 2) := by
          gcongr
        _ = 27 * (a : ℝ) * α / ((n : ℝ) * (1 + α) ^ 2) := by
          field_simp
    rw [hlog_eq]
    exact hsmall.trans_le <| by
      calc
        L * s = 6 * (a : ℝ) / n := by rw [ha_eq]; simp [L]; ring
        _ ≤ _ := hP
  · let t : ℝ := α / 2
    have htpos : 0 < t := div_pos (zero_lt_one.trans_le hα₁) (by norm_num)
    have ht₁ : 1 ≤ t := by dsimp [t]; linarith
    have hα_eq : α = 2 * t := by dsimp [t]; ring
    have ha_eq : (a : ℝ) = A * (2 * t ^ n) := by
      rw [← hαpow, hα_eq]
      dsimp [A]
      rw [mul_pow, ← mul_pow_sub_one (n := n) (by omega) (2 : ℝ)]
      ring
    have hlog_eq :
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (a : ℝ) ^ 2) =
          R + 2 * Real.log 2 + 2 * n * Real.log t := by
      rw [ha_eq]
      have hbase_ne :
          16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2 ≠ 0 := by positivity
      calc
        Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (A * (2 * t ^ n)) ^ 2)
            = Real.log ((16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2) *
                (2 * t ^ n) ^ 2) := by
                  congr 1
                  ring
        _ = Real.log (16 * (n : ℝ) * (↑(n - 1) : ℝ) * A ^ 2) +
              Real.log ((2 * t ^ n) ^ 2) :=
                Real.log_mul hbase_ne
                  (pow_ne_zero 2 (mul_ne_zero (by norm_num) (pow_ne_zero _ htpos.ne')))
        _ = R + 2 * Real.log 2 + 2 * n * Real.log t := by
          rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero _ htpos.ne'),
            Real.log_pow]
          simp [R]
          ring
    have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
    have htpow : 1 + (n - 1 : ℕ) * (t - 1) ≤ t ^ (n - 1) := by
      simpa [add_sub_cancel_left] using
        (one_add_mul_le_pow (show (-2 : ℝ) ≤ t - 1 by linarith) (n - 1))
    have hsecond : 2 * Real.log 2 + 2 * n * Real.log t ≤ L * t ^ (n - 1) := by
      have hcoef : (2 : ℝ) * n ≤ 6 * (↑(n - 1) : ℝ) := by
        norm_cast
        omega
      have hlinear :
          (3 : ℝ) / 2 + 2 * n * (t - 1) ≤
            6 * (1 + (n - 1 : ℕ) * (t - 1)) := by
        have hmul := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr ht₁)
        nlinarith
      calc
        2 * Real.log 2 + 2 * n * Real.log t
            ≤ (3 : ℝ) / 2 + 2 * n * (t - 1) := by
              nlinarith [log_two_lt_three_four.le]
        _ ≤ 6 * (1 + (n - 1 : ℕ) * (t - 1)) := hlinear
        _ ≤ 6 * t ^ (n - 1) := by gcongr
        _ ≤ L * t ^ (n - 1) := by gcongr
    have htotal :
        R + 2 * Real.log 2 + 2 * n * Real.log t <
          2 * L * t ^ (n - 1) := by
      have hfirst : R < L * t ^ (n - 1) :=
        hR_L.trans_le (by simpa using
          mul_le_mul_of_nonneg_left (one_le_pow₀ ht₁) (by linarith [hL6]))
      nlinarith
    have hfac := four_ninths_div_le_root_factor hα₂
    have hP :
        12 * (a : ℝ) / ((n : ℝ) * α) ≤
          27 * (a : ℝ) * α / ((n : ℝ) * (1 + α) ^ 2) := by
      calc
        12 * (a : ℝ) / ((n : ℝ) * α) =
            (27 * (a : ℝ) / n) * ((4 : ℝ) / (9 * α)) := by ring
        _ ≤ (27 * (a : ℝ) / n) * (α / (1 + α) ^ 2) := by gcongr
        _ = 27 * (a : ℝ) * α / ((n : ℝ) * (1 + α) ^ 2) := by
          field_simp
    have hlower :
        2 * L * t ^ (n - 1) = 12 * (a : ℝ) / ((n : ℝ) * α) := by
      rw [ha_eq, hα_eq]
      dsimp [L]
      rw [← pow_sub_one_mul (n := n) (by omega) t]
      field_simp
      ring
    rw [hlog_eq]
    exact htotal.trans_le (hlower.le.trans hP)

private lemma sin_pi_div_lower {n : ℕ} (hn : 3 ≤ n) :
    (3 * Real.sqrt 3) / (2 * n) ≤ Real.sin (Real.pi / n) := by
  have hlam1 : (3 : ℝ) / n ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < n)]
    exact_mod_cast hn
  have hpi3 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have hc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi by simp [Real.pi_pos.le])
    hpi3 (sub_nonneg.mpr hlam1) (show (0 : ℝ) ≤ 3 / n by positivity)
  calc
    (3 * Real.sqrt 3) / (2 * n) = (3 / n) * (Real.sqrt 3 / 2) := by ring
    _ ≤ Real.sin (Real.pi / n) := by
      simpa [Real.sin_pi_div_three, smul_eq_mul] using hc

private lemma one_sub_cos_two_pi_div_lower {n : ℕ} (hn : 3 ≤ n) :
    (27 : ℝ) / (2 * n ^ 2) ≤ 1 - Real.cos (2 * Real.pi / n) := by
  have hsin_sq :
      ((3 * Real.sqrt 3) / (2 * n)) ^ 2 ≤ (Real.sin (Real.pi / n)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (sin_pi_div_lower hn) 2
  rw [show 2 * Real.pi / (n : ℝ) = 2 * (Real.pi / n) by ring,
    Real.cos_two_mul_eq_one_sub]
  rw [div_pow] at hsin_sq
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0] at hsin_sq ⊢
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private lemma spectral_error_bound_n_ge_three {a n : ℕ} (hn : 3 ≤ n)
    (ha₀ : 2 ^ (n - 1) ≤ a) :
    let α : ℝ := (a : ℝ) ^ ((n : ℝ)⁻¹)
    let q : ℝ :=
      Real.sqrt (1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / n)) / (1 + α)
    (n - 1 : ℕ) * q ^ (2 * a * n) <
      1 / (16 * (n : ℝ) * (a : ℝ) ^ 2) := by
  let α : ℝ := (a : ℝ) ^ ((n : ℝ)⁻¹)
  let c : ℝ := Real.cos (2 * Real.pi / n)
  let rad : ℝ := 1 + α ^ 2 + 2 * α * c
  let q : ℝ := Real.sqrt rad / (1 + α)
  let D : ℝ := (1 + α) ^ 2
  let u : ℝ := 2 * α * (1 - c) / D
  let v : ℝ := 27 * α / ((n : ℝ) ^ 2 * D)
  let P : ℝ := 27 * (a : ℝ) * α / ((n : ℝ) * D)
  have ha₁ : 1 ≤ a := (show 1 ≤ n by omega).trans
    ((nat_le_two_pow_pred (show 1 ≤ n by omega)).trans ha₀)
  have hapos : 0 < a := by omega
  have hα₁ : 1 ≤ α := by
    dsimp [α]
    exact Real.one_le_rpow (by exact_mod_cast ha₁) (by positivity)
  have hrad : 0 ≤ rad := by
    have hc := Real.neg_one_le_cos (2 * Real.pi / (n : ℝ))
    dsimp [rad, c]
    nlinarith [sq_nonneg (α - 1)]
  have hq_sq : q ^ 2 = rad / D := by
    dsimp [q, D]
    rw [div_pow, Real.sq_sqrt hrad]
  have hratio : rad / D = 1 - u := by
    dsimp [rad, D, u]
    field_simp
    ring
  have hcos :
      (27 : ℝ) / (2 * n ^ 2) ≤ 1 - c := by
    simpa only [c] using one_sub_cos_two_pi_div_lower hn
  have huv : v ≤ u := by
    calc
      v = (2 * α / D) * ((27 : ℝ) / (2 * n ^ 2)) := by
        dsimp [v]
        field_simp
      _ ≤ (2 * α / D) * (1 - c) := by
        exact mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = u := by dsimp [u]; ring
  have hq_sq_exp : q ^ 2 ≤ Real.exp (-v) := by
    rw [hq_sq, hratio]
    exact (Real.one_sub_le_exp_neg u).trans (Real.exp_le_exp.mpr (neg_le_neg huv))
  have hpow_exp : q ^ (2 * a * n) ≤ Real.exp (-P) := by
    calc
      q ^ (2 * a * n) = (q ^ 2) ^ (a * n) := by
        simpa [mul_assoc] using pow_mul q 2 (a * n)
      _ ≤ (Real.exp (-v)) ^ (a * n) :=
        pow_le_pow_left₀ (sq_nonneg q) hq_sq_exp (a * n)
      _ = Real.exp ((a * n : ℕ) * (-v)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-P) := by
        congr 1
        dsimp [v, P]
        push_cast
        field_simp
  have hn1 : n - 1 ≠ 0 := by omega
  have hexp : Real.exp (-P) <
      1 / (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (a : ℝ) ^ 2) := by
    apply exp_neg_lt_inv
    · positivity
    · simpa only [P, D, α] using
        exponent_gt_log_of_pow hn ha₀ hα₁
          (Real.rpow_inv_natCast_pow (by positivity) (by omega))
  have hmul := mul_lt_mul_of_pos_left (hpow_exp.trans_lt hexp)
    (show (0 : ℝ) < (n - 1 : ℕ) by positivity)
  change (↑(n - 1) : ℝ) * q ^ (2 * a * n) < 1 / (16 * (n : ℝ) * (a : ℝ) ^ 2)
  calc
    (↑(n - 1) : ℝ) * q ^ (2 * a * n)
        < (↑(n - 1) : ℝ) *
            (1 / (16 * (n : ℝ) * (↑(n - 1) : ℝ) * (a : ℝ) ^ 2)) := hmul
    _ = 1 / (16 * (n : ℝ) * (a : ℝ) ^ 2) := by
      field_simp [hn1]

private lemma exponent_two_gt_log {a : ℕ} (ha : 4 ≤ a) :
    let α : ℝ := (a : ℝ) ^ ((2 : ℝ)⁻¹)
    Real.log (32 * (a : ℝ) ^ 2) <
      8 * (a : ℝ) * α / (1 + α) ^ 2 := by
  let α : ℝ := (a : ℝ) ^ ((2 : ℝ)⁻¹)
  let t : ℝ := α / 2
  have hαpow : α ^ 2 = (a : ℝ) := by
    exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  have hαnonneg : 0 ≤ α := by dsimp [α]; positivity
  have hα₂ : 2 ≤ α := by
    have ha' : (4 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  have ht₁ : 1 ≤ t := by dsimp [t]; linarith
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht₁
  have hα_eq : α = 2 * t := by dsimp [t]; ring
  have ha_eq : (a : ℝ) = 4 * t ^ 2 := by rw [← hαpow, hα_eq]; ring
  have hlog512 : Real.log 512 < (27 : ℝ) / 4 := by
    calc
      Real.log 512 = 9 * Real.log 2 := by
        rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
        norm_num
      _ < 9 * ((3 : ℝ) / 4) :=
        mul_lt_mul_of_pos_left log_two_lt_three_four (by norm_num)
      _ = (27 : ℝ) / 4 := by norm_num
  have hlog_eq :
      Real.log (32 * (a : ℝ) ^ 2) = Real.log 512 + 4 * Real.log t := by
    rw [ha_eq]
    calc
      Real.log (32 * (4 * t ^ 2) ^ 2) = Real.log (512 * t ^ 4) := by
        congr 1
        ring
      _ = Real.log 512 + Real.log (t ^ 4) :=
        Real.log_mul (by norm_num) (pow_ne_zero 4 htpos.ne')
      _ = Real.log 512 + 4 * Real.log t := by rw [Real.log_pow]; norm_num
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
  have htarget : Real.log (32 * (a : ℝ) ^ 2) < (64 : ℝ) * t / 9 := by
    rw [hlog_eq]
    nlinarith
  have hdenom : (1 + 2 * t) ^ 2 ≤ 9 * t ^ 2 := by
    have hlin : 1 + 2 * t ≤ 3 * t := by linarith
    exact pow_le_pow_left₀ (by positivity) hlin 2 |>.trans_eq (by ring)
  have hlower :
      (64 : ℝ) * t / 9 ≤ 8 * (a : ℝ) * α / (1 + α) ^ 2 := by
    rw [ha_eq, hα_eq]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 9) (sq_pos_of_pos (by linarith))]
    nlinarith [mul_le_mul_of_nonneg_left hdenom (by positivity : (0 : ℝ) ≤ 64 * t / 9)]
  exact htarget.trans_le hlower

private lemma spectral_error_bound_n_two {a : ℕ} (ha : 4 ≤ a) :
    let α : ℝ := (a : ℝ) ^ ((2 : ℝ)⁻¹)
    let q : ℝ :=
      Real.sqrt (1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / 2)) / (1 + α)
    q ^ (4 * a) < 1 / (32 * (a : ℝ) ^ 2) := by
  let α : ℝ := (a : ℝ) ^ ((2 : ℝ)⁻¹)
  let rad : ℝ := 1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / 2)
  let q : ℝ := Real.sqrt rad / (1 + α)
  let D : ℝ := (1 + α) ^ 2
  let u : ℝ := 4 * α / D
  let P : ℝ := 8 * (a : ℝ) * α / D
  have hαnonneg : 0 ≤ α := by dsimp [α]; positivity
  have hrad : 0 ≤ rad := by
    dsimp [rad]
    rw [show (2 : ℝ) * Real.pi / 2 = Real.pi by ring, Real.cos_pi]
    nlinarith [sq_nonneg (α - 1)]
  have hq_sq : q ^ 2 = rad / D := by
    dsimp [q, D]
    rw [div_pow, Real.sq_sqrt hrad]
  have hratio : rad / D = 1 - u := by
    dsimp [rad, D, u]
    rw [show (2 : ℝ) * Real.pi / 2 = Real.pi by ring, Real.cos_pi]
    field_simp
    ring
  have hq_sq_exp : q ^ 2 ≤ Real.exp (-u) := by
    rw [hq_sq, hratio]
    exact Real.one_sub_le_exp_neg u
  have hpow_exp : q ^ (4 * a) ≤ Real.exp (-P) := by
    calc
      q ^ (4 * a) = (q ^ 2) ^ (2 * a) := by
        simpa [← mul_assoc] using pow_mul q 2 (2 * a)
      _ ≤ (Real.exp (-u)) ^ (2 * a) :=
        pow_le_pow_left₀ (sq_nonneg q) hq_sq_exp (2 * a)
      _ = Real.exp ((2 * a : ℕ) * (-u)) := by rw [Real.exp_nat_mul]
      _ = Real.exp (-P) := by
        congr 1
        dsimp [u, P]
        push_cast
        field_simp
        ring
  have hexp : Real.exp (-P) < 1 / (32 * (a : ℝ) ^ 2) := by
    apply exp_neg_lt_inv
    · positivity
    · simpa only [P, D, α] using exponent_two_gt_log ha
  simpa only [q, rad, α] using hpow_exp.trans_lt hexp

public lemma spectral_error_bound {a n : ℕ} (ha : 4 ≤ a) (hn : 1 < n)
    (ha₀ : 2 ^ (n - 1) ≤ a) :
    let α : ℝ := (a : ℝ) ^ ((n : ℝ)⁻¹)
    let q : ℝ :=
      Real.sqrt (1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / n)) / (1 + α)
    (n - 1 : ℕ) * q ^ (2 * a * n) <
      1 / (16 * (n : ℝ) * (a : ℝ) ^ 2) := by
  rcases eq_or_lt_of_le (show 2 ≤ n by omega) with rfl | hn3
  · rw [show (2 * a * 2 : ℕ) = 4 * a by ring]
    norm_num only [Nat.cast_ofNat, Nat.reduceSubDiff, one_mul]
    simpa only [one_div] using spectral_error_bound_n_two ha
  · exact spectral_error_bound_n_ge_three (by omega) ha₀

end ShuniaIntegerRoot

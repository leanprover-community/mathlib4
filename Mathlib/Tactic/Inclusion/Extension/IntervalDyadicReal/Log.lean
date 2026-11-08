/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Int.Log
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# `Real.log` extension for tactic `dyadic_interval`

This file implements `Real.log` extension for the tactic `dyadic_interval`.

## Implementation details

We first define `Inclusion.IntervalDyadicReal.smallArtanh`, which computes `artanh` of a small
dyadic number `num / den` using the binary splitting method. Then we use the identity
`log 2 = 6 * artanh (1 / 17) + 4 * artanh (1 / 19) + 4 * artanh (1 / 31)`
to obtain a dyadic approximation of `log 2`.

With these, `log x` is computed for arbitrary `x` by first bringing `|x|` into the interval
`[1, 2)` (writing `x = x' * 2 ^ k` with `|x'| ∈ [1, 2)`) and then adding `k * log 2`; this keeps
the argument of the series small, so that it converges quickly.

We use `artanh` rather than `log` itself because all the terms of its series are positive (for a
positive argument). Hence every truncated partial sum is a lower bound, and an upper bound is
obtained by adding a `step prec`.

## References

* <http://numbers.computation.free.fr/Constants/Algorithms/splitting.html>

-/

public section

open Real Dyadic

namespace Inclusion

namespace IntervalDyadicReal

open Dyadic

section SmallArtanh

/-- The `n`-th partial sum of the `artanh` series at `num / den`,
returned as `(P, Q)` with `P / Q` equal to this sum.
Note that the series converges slowly when the input is close to `1`. -/
@[expose]
def smallArtanh (num den : ℕ) (n : ℕ) : ℕ × ℕ :=
  let (_, Q, R) := go 0 n
  (num * R, den * Q)
where
  /-- Binary splitting auxiliary function: `go a b` returns `(P, Q, R)` on segment `[a, b)`.

  `R` is the numerator of `∑ k ∈ Finset.Ico a b, ∏ j ∈ Finset.Ico a k, t (j + 1) / t j` put over
  the common denominator of the term ratios `((2 * k + 1) * num ^ 2) / ((2 * k + 3) * den ^ 2)`. -/
  go : ℕ -> ℕ -> ℕ × ℕ × ℕ := fun a b =>
    match h : b - a with
    | 0 => (1, 1, 0)
    | 1 => ((2 * a + 1) * num ^ 2, (2 * a + 3) * den ^ 2, (2 * a + 3) * den ^ 2)
    | _ + 2 =>
      let m : ℕ := (a + b) / 2
      let (Pl, Ql, Rl) : ℕ × ℕ × ℕ := go a m
      let (Pr, Qr, Rr) : ℕ × ℕ × ℕ := go m b
      (Pl * Pr, Ql * Qr, Qr * Rl + Pl * Rr)
  termination_by a b => b - a
  decreasing_by all_goals lia

theorem smallArtanh.go_spec (num den a b : ℕ) :
    let (P, Q, R) : ℕ × ℕ × ℕ := go num den a b
    P = ∏ i ∈ Finset.Ico a b, (2 * i + 1) * num ^ 2 ∧
    Q = ∏ i ∈ Finset.Ico a b, (2 * i + 3) * den ^ 2 ∧
    R = ∑ i ∈ Finset.Ico a b, (∏ j ∈ Finset.Ico a i, (2 * j + 1) * num ^ 2) *
      ∏ j ∈ Finset.Ico i b, (2 * j + 3) * den ^ 2 := by
  fun_induction go num den a b with
  | case1 a b h => simp [Finset.Ico_eq_empty_of_le (by lia : b ≤ a)]
  | case2 a b h => simp [show b = a + 1 by lia]
  | case3 a b n h m Pl Ql Rl hl Pr Qr Rr hr ihl ihr =>
    obtain ⟨rfl, rfl, rfl⟩ := hl ▸ ihl
    obtain ⟨rfl, rfl, rfl⟩ := hr ▸ ihr
    split_ands
    · apply Finset.prod_Ico_consecutive <;> lia
    · apply Finset.prod_Ico_consecutive <;> lia
    · rw [Finset.mul_sum, Finset.mul_sum]
      conv_lhs =>
        congr
        · apply Finset.sum_congr rfl
          tactic =>
            intro i hi
            rw [← Nat.mul_assoc, mul_rotate, Nat.mul_assoc,
              Finset.prod_Ico_consecutive _ (by grind) (by lia)]
        · apply Finset.sum_congr rfl
          tactic =>
            intro i hi
            rw [← Nat.mul_assoc, Finset.prod_Ico_consecutive _ (by lia) (by grind)]
      apply Finset.sum_Ico_consecutive <;> lia

theorem smallArtanh.go_spec' {num den : ℕ} (hden : den ≠ 0) (a b : ℕ) :
    let (_, Q, R) : ℕ × ℕ × ℕ := go num den a b
    R / Q = ∑ i ∈ Finset.Ico a b, ∏ j ∈ Finset.Ico a i,
      (((2 * j + 1) * num ^ 2) / ((2 * j + 3) * den ^ 2) : ℝ) := by
  simp only [go_spec num den a b]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  conv_lhs =>
    apply Finset.sum_congr rfl
    tactic =>
      intro i hi
      rw [← div_eq_mul_inv,
        ← Finset.prod_Ico_consecutive (m := a) (n := i) (k := b) _ (by grind) (by grind),
        mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.mpr fun j _ => by positivity),
        ← Finset.prod_div_distrib]

theorem smallArtanh.den_ne_zero (num den n : ℕ) (hden : den ≠ 0) :
    (smallArtanh num den n).2 ≠ 0 := by
  unfold smallArtanh
  simp only [go_spec num den 0 n]
  simpa [hden] using Finset.prod_ne_zero_iff.mpr fun j _ => by positivity

theorem smallArtanh.spec (num den n : ℕ) :
    let (P, Q) : ℕ × ℕ := smallArtanh num den n
    P / Q = ∑ k ∈ Finset.range n, (num / den : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  unfold smallArtanh
  by_cases hden : den = 0
  · simp [hden]
  push_cast
  rw [mul_div_mul_comm, go_spec' hden, Finset.mul_sum]
  simp only [Nat.Ico_zero_eq_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  induction i with
  | zero => simp
  | succ i ih =>
    specialize ih (by grind)
    rw [Finset.prod_range_succ, ← _root_.mul_assoc, ih]
    simp [div_pow, field]
    ring

private theorem abs_artanh_sub_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    |artanh x - ∑ k ∈ Finset.range n, x ^ (2 * k + 1) / (2 * k + 1)| ≤
      |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  rw [artanh_eq_half_log <| Set.Ioo_subset_Icc_self hx]
  exact sum_range_sub_log_div_le (abs_lt.mpr hx) n

end SmallArtanh

section Log

section LogTwo

/-- Computes a lower bound `l : Dyadic` for `log 2` with precision `prec`. -/
@[expose]
def logTwo (prec : ℕ) : Dyadic :=
  let (P1, Q1) : ℕ × ℕ := smallArtanh 1 17 ((prec + 7) / 8)
  let (P2, Q2) : ℕ × ℕ := smallArtanh 1 19 ((prec + 7) / 8)
  let (P3, Q3) : ℕ × ℕ := smallArtanh 1 31 ((prec + 8) / 9)
  let P : ℕ := 6 * P1 * Q2 * Q3 + 4 * Q1 * P2 * Q3 + 4 * Q1 * Q2 * P3
  let Q : ℕ := Q1 * Q2 * Q3
  (P / Q : ℚ).toDyadic (prec + 3)

private theorem logTwo_aux :
    log 2 = 6 * artanh (1 / 17) + 4 * artanh (1 / 19) + 4 * artanh (1 / 31) := by
  rw [show (2 : ℝ) = (9 / 8) ^ 3 * (10 / 9) ^ 2 * (16 / 15) ^ 2 by norm_num]
  simp [log_mul]
  norm_num [artanh_eq_half_log]
  field

theorem abs_log_two_sub_le (prec : ℕ) :
    |log 2 - (logTwo prec).toRat| ≤ (1 / 2) ^ prec := by
  unfold logTwo
  have hartanh17 := smallArtanh.spec 1 17 ((prec + 7) / 8)
  have hartanh19 := smallArtanh.spec 1 19 ((prec + 7) / 8)
  have hartanh31 := smallArtanh.spec 1 31 ((prec + 8) / 9)
  have hartanh17₀ := smallArtanh.den_ne_zero 1 17 ((prec + 7) / 8) (by simp)
  have hartanh19₀ := smallArtanh.den_ne_zero 1 19 ((prec + 7) / 8) (by simp)
  have hartanh31₀ := smallArtanh.den_ne_zero 1 31 ((prec + 8) / 9) (by simp)
  set artanh17 : ℕ × ℕ := smallArtanh 1 17 ((prec + 7) / 8)
  set artanh19 : ℕ × ℕ := smallArtanh 1 19 ((prec + 7) / 8)
  set artanh31 : ℕ × ℕ := smallArtanh 1 31 ((prec + 8) / 9)
  simp only at *
  rw [show (1 / 2 : ℝ) ^ prec = (6 + 4 + 4) * (1 / 2) ^ (prec + 4) + (1 / 2) ^ (prec + 3 : ℤ) by
    norm_cast; ring]
  refine abs_sub_le _ _ _ |>.trans <| add_le_add ?_ abs_toRat_toDyadic_le_pow_real
  push_cast
  simp only [add_div]
  conv in _ + _ => congr; congr; all_goals field_simp; rw [mul_div_assoc]
  rw [logTwo_aux, ← sub_sub, ← sub_sub, add_sub_right_comm, add_sub_right_comm,
    add_sub_right_comm (6 * _), ← mul_sub, add_sub_assoc, ← mul_sub, add_sub_assoc, ← mul_sub]
  grw [abs_add_le, abs_add_le, _root_.add_mul, _root_.add_mul]
  iterate 3 rw [abs_mul, Nat.abs_ofNat]
  gcongr <;> [rw [hartanh17]; rw [hartanh19]; rw [hartanh31]]
  <;> grw [Nat.cast_one, Nat.cast_ofNat, abs_artanh_sub_le (by grind), abs_of_pos (by simp)]
  <;> clear * -
  <;> [set k : ℕ := (prec + 7) / 8; set k : ℕ := (prec + 7) / 8; set k : ℕ := (prec + 8) / 9]
  <;> [set m : ℕ := 8 * k; set m : ℕ := 8 * k; set m : ℕ := 9 * k]
  <;> (norm_num [pow_add, pow_mul]; field_simp; ring_nf)
  <;> (gcongr; on_goal 2 => norm_num)
  <;> apply pow_le_pow_iff_right_of_lt_one₀ (m := m) (by norm_num) (by norm_num)
    |>.mpr (by lia) |>.trans'
  <;> unfold m
  <;> norm_num [pow_mul]
  <;> exact pow_le_pow_left₀ (by norm_num) (by norm_num) k

theorem logTwo_le (prec : ℕ) :
    (logTwo prec).toRat ≤ log 2 := by
  unfold logTwo
  have hartanh17 := smallArtanh.spec 1 17 ((prec + 7) / 8)
  have hartanh19 := smallArtanh.spec 1 19 ((prec + 7) / 8)
  have hartanh31 := smallArtanh.spec 1 31 ((prec + 8) / 9)
  have hartanh17₀ := smallArtanh.den_ne_zero 1 17 ((prec + 7) / 8) (by simp)
  have hartanh19₀ := smallArtanh.den_ne_zero 1 19 ((prec + 7) / 8) (by simp)
  have hartanh31₀ := smallArtanh.den_ne_zero 1 31 ((prec + 8) / 9) (by simp)
  set artanh17 : ℕ × ℕ := smallArtanh 1 17 ((prec + 7) / 8)
  set artanh19 : ℕ × ℕ := smallArtanh 1 19 ((prec + 7) / 8)
  set artanh31 : ℕ × ℕ := smallArtanh 1 31 ((prec + 8) / 9)
  simp only at *
  grw [Rat.toRat_toDyadic_le]
  push_cast
  simp only [add_div]
  conv in _ + _ => congr; congr; all_goals field_simp; rw [mul_div_assoc]
  rw [hartanh17, hartanh19, hartanh31]
  iterate 3 grw [Real.sum_range_le_log_div (by norm_num) (by norm_num),
    ← artanh_eq_half_log (by grind)]
  simp only [Nat.cast_one, Nat.cast_ofNat, logTwo_aux, le_rfl]

theorem le_logTwo (prec : ℕ) :
    log 2 ≤ (logTwo prec).toRat + (step prec).toRat := by
  rw [toRat_step_real prec, zpow_natCast]
  grind [abs_sub_lt_iff, abs_log_two_sub_le prec]

end LogTwo

section LogSum

/-- Computes a lower bound `l : Dyadic` for `log x` when `1 ≤ |x| < 2` with precision `prec`. -/
@[expose]
def logSum (x : Dyadic) (prec : ℕ) : Dyadic :=
  if x = 1 ∨ x = -1 then 0 else
  match x with
  | zero => 0
  | ofOdd n _ _ =>
    -- `(x - 1) / (x + 1) = (m - 2 ^ e) / (m + 2 ^ e) ∈ (0, 1 / 3)`
    let e : ℕ := n.natAbs.log2
    let m : ℕ := n.natAbs
    -- Dyadic.smallArtanh → δ₁ < (1 / 2) ^ (prec + 2), although we only need `≤`
    let (P, Q) : ℕ × ℕ := smallArtanh (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
    -- (P / Q : ℚ).toDyadic → δ₂ ≤ (1 / 2) ^ (prec + 2)
    -- δ ≤ 2 * (δ₁ + δ₂) < (1 / 2) ^ prec
    2 * (P / Q : ℚ).toDyadic (prec + 2)

private theorem eq_log2_of_and (n k : ℤ) (hn : n % 2 = 1) :
    1 ≤ |ofOdd n k hn| ∧ |ofOdd n k hn| < 2 -> k = n.natAbs.log2 := by
  intro hx
  rw [← toRat_le_toRat_iff, ← toRat_lt_toRat_iff] at hx
  norm_num [toRat_ofOdd_eq_mul_two_pow, field, ← zpow_add_one₀] at hx
  have hn : 0 < |(n : ℚ)| := lt_of_lt_of_le (zpow_pos two_pos k) hx.left
  rw [le_antisymm ((Int.zpow_le_iff_le_log Nat.one_lt_two hn).mp hx.left)
    (Int.le_of_lt_add_one ((Int.lt_zpow_iff_log_lt Nat.one_lt_two hn).mp hx.right)),
    ← Int.cast_abs, ← Nat.cast_natAbs, Int.log_natCast, ← Nat.log2_eq_log_two]

theorem abs_sub_logSum_le {x : Dyadic} (hx : 1 ≤ |x| ∧ |x| < 2) (prec : ℕ) :
    |log x.toRat - (logSum x prec).toRat| ≤ (1 / 2) ^ prec := by
  fun_cases logSum with
  | case1 _ hx' => rcases hx' with rfl | rfl <;> simp
  | case2 _ => simp
  | case3 n k hn e m P Q hPQ hx' =>
  have hem : m ≥ 2 ^ e := Nat.log2_self_le <| by lia
  grw [show (1 / 2 : ℝ) ^ prec = (1 / 2) ^ (prec + 1) + (1 / 2) ^ (prec + 1) by ring,
    abs_sub_le (b := (2 * (P / Q) : ℝ))]
  apply add_le_add
  · rw [← log_abs, log_eq_two_mul_artanh (by simp), ← mul_sub, abs_mul, Nat.abs_ofNat]
    set X : ℝ := (m - 2 ^ e : ℕ) / (m + 2 ^ e : ℕ)
    have hX1 : X < 1 / 3 := by
      unfold X
      field_simp
      zify [hem]
      suffices (m : ℝ) < 2 * 2 ^ e by linarith
      norm_cast
      grind [n.natAbs.lt_log2_self]
    have hX2 : |X| < 1 / 3 := by
      rw [abs_lt]
      refine ⟨lt_of_lt_of_le (b := 0) (by simp) ?_, hX1⟩
      simp [X, field]
    have hX3 : X = (|↑(ofOdd n k hn).toRat| - 1) / (|↑(ofOdd n k hn).toRat| + 1) := by
      simp [toRat_ofOdd_eq_mul_two_pow, eq_log2_of_and n k hn hx, field, hem, m, e]
    have H := smallArtanh.spec (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
    simp only [hPQ] at H
    rw [← hX3, H]
    set N : ℕ := prec / 3 + 1
    grw [abs_artanh_sub_le (by grind)]
    calc
      _ ≤ 2 * (|X| ^ (2 * N + 1) / (1 - (1 / 3) ^ 2)) := by gcongr
      _ ≤ 2 * ((1 / 3) ^ (2 * N + 1) / (1 - (1 / 3) ^ 2)) := by gcongr
      _ ≤ (1 / 2) ^ (prec + 1) := by
        apply pow_le_pow_iff_right_of_lt_one₀ (m := 3 * N) one_half_pos one_half_lt_one
          |>.mpr (by lia) |>.trans'
        norm_num [pow_add, pow_mul]
        field_simp
        ring_nf
        gcongr <;> norm_num
  · rw [toRat_mul, Rat.cast_mul, toRat_ofNat, Rat.cast_ofNat, ← mul_sub, abs_mul, Nat.abs_ofNat]
    grw [← Rat.cast_natCast P, ← Rat.cast_natCast Q, ← Rat.cast_div, abs_toRat_toDyadic_le_pow_real]
    simp [zpow_add₀, pow_succ, -neg_add_rev, field]

theorem logSum_le {x : Dyadic} (hx : 1 ≤ |x| ∧ |x| < 2) (prec : ℕ) :
    (logSum x prec).toRat ≤ log x.toRat := by
  by_cases hx' : |x| = 1
  · rcases eq_or_eq_neg_of_abs_eq hx' with rfl | rfl <;> simp [logSum]
  replace hx' : 1 < |x| ∧ |x| < 2 := hx.imp_left (lt_of_le_of_ne · (Ne.symm hx'))
  fun_cases logSum with
  | case1 _ hx' => rcases hx' with rfl | rfl <;> simp [← toRat_lt_toRat_iff] at hx'
  | case2 _ => simp [← toRat_lt_toRat_iff, not_lt_of_gt] at hx'
  | case3 n k hn e m P Q hPQ hx' =>
    obtain rfl : k = n.natAbs.log2 := eq_log2_of_and n k hn hx
    have hem : m ≥ 2 ^ e := Nat.log2_self_le <| by lia
    have hem' : (↑(m - 2 ^ e) / ↑(m + 2 ^ e) : ℝ) ∈ Set.Ico 0 1 := by
      suffices (m : ℝ) < 2 * 2 ^ e by simpa [field, hem] using ⟨mod_cast hem, by linarith⟩
      norm_cast
      grind [n.natAbs.lt_log2_self]
    simp only [toRat_mul, toRat_ofNat, Rat.cast_mul, Rat.cast_ofNat]
    grw [Rat.toRat_toDyadic_le]
    simp only [Rat.cast_div, Rat.cast_natCast]
    have hartanh := smallArtanh.spec (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
    simp only [hPQ] at hartanh
    grw [hartanh, Real.sum_range_le_log_div hem'.left hem'.right,
      one_div, mul_inv_cancel_left₀ (by simp)]
    apply le_of_eq
    nth_rw 2 [← log_abs]
    congr
    simp [hem.le, field, toRat_ofOdd_eq_mul_two_pow, m]

end LogSum

/-- Computes a lower bound for `log x` with precision `prec`. -/
@[expose]
def lowerLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if x = 1 ∨ x = -1 then 0 else
  match x with
  | zero => 0
  | ofOdd n p hn =>
    let k : ℤ := n.natAbs.log2 - p -- `k ≥ 0 ↔ |x| ≥ 1`
    let x' : Dyadic := .ofOdd n n.natAbs.log2 hn -- `|x'| ∈ [1, 2)`
    let wp : ℕ := prec + k.natAbs.log2 + 2
    if k ≥ 0 then
      logSum x' (prec + 1) + k * logTwo wp
    else
      logSum x' (prec + 1) + k * (logTwo wp + step wp)

/-- Computes an upper bound for `log x` with precision `prec`. -/
@[expose]
def upperLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if x = 0 ∨ x = 1 ∨ x = -1 then 0 else lowerLog x prec + step prec

private theorem lowerLog_aux1 (n : ℤ) (hn : n % 2 = 1) :
    1 ≤ |ofOdd n n.natAbs.log2 hn| ∧ |ofOdd n n.natAbs.log2 hn| < 2 := by
  rw [← toRat_le_toRat_iff, ← toRat_lt_toRat_iff]
  simp only [toRat_abs, toRat_ofOdd_eq_mul_two_pow, zpow_neg, zpow_natCast, abs_pow,
    Nat.abs_ofNat, toRat_ofNat, ← div_eq_mul_inv, abs_div, ← Int.cast_abs, ← Nat.cast_natAbs]
  rw [le_div_iff₀ (by positivity), Rat.one_mul, div_lt_iff₀ (by positivity), ← pow_succ']
  exact ⟨mod_cast Nat.log2_self_le (by lia), mod_cast Nat.lt_log2_self⟩

private theorem lowerLog_aux2 (n k : ℤ) (hn : n % 2 = 1) :
    ofOdd n k hn = ofOdd n n.natAbs.log2 hn <<< (n.natAbs.log2 - k) := by
  grind [ofOdd_shiftLeft]

theorem abs_lowerLog_le (x : Dyadic) (prec : ℕ) :
    |log x.toRat - (lowerLog x prec).toRat| ≤ (step prec).toRat := by
  fun_cases lowerLog x prec
  · rcases ‹x = 1 ∨ x = -1› with rfl | rfl <;> simp [step]
  · simp [step]
  all_goals
    rename_i n k hn k' x' wp hk' hx'
    simp only [toRat_add, toRat_mul, toRat_intCast, Rat.cast_add, Rat.cast_mul, Rat.cast_intCast]
    grw [lowerLog_aux2 n k hn, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), add_sub_add_comm, abs_add_le]
    simp only [Rat.cast_zpow, Rat.cast_ofNat, log_zpow]
    rw [step_eq_add prec, toRat_add, Rat.cast_add, ← mul_sub (k' : ℝ), abs_mul]
    apply add_le_add
    · rw [toRat_step]
      convert abs_sub_logSum_le (lowerLog_aux1 n hn) (prec + 1)
      norm_num [zpow_add₀, pow_succ]
  all_goals
    replace hk' : |(k' : ℝ)| ≤ 2 ^ (k'.natAbs.log2 + 1) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast Nat.lt_log2_self.le
    have H : |↑k'| * (1 / 2 : ℝ) ^ wp ≤ (step (prec + 1)).toRat := by
      grw [hk']
      simp [toRat_step, zpow_add_one₀, pow_succ, pow_add, field, -neg_add_rev, wp]
  · grw [abs_log_two_sub_le wp, H]
  · grw [abs_sub_comm, abs_of_nonneg <| sub_nonneg_of_le <| le_logTwo wp, toRat_step_real,
      zpow_natCast, logTwo_le wp, add_sub_cancel_left, H]

theorem lowerLog_le (x : Dyadic) (prec : ℕ) :
    (lowerLog x prec).toRat ≤ log x.toRat := by
  by_cases hx : x = 0 ∨ x = 1 ∨ x = -1
  · rcases hx with rfl | rfl | rfl <;>
      simp [lowerLog, Eq.comm, ← Dyadic.zero_eq] <;>
      simp [Dyadic.zero_eq]
  push +distrib Not at hx
  fun_cases lowerLog with
  | case1 | case2 => tauto
  | case3 n k hn k' x' wp hk' hx' =>
    rw [lowerLog_aux2 n k hn, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), Rat.cast_zpow, Rat.cast_ofNat, log_zpow,
      toRat_add, Rat.cast_add, toRat_mul, Rat.cast_mul, toRat_intCast, Rat.cast_intCast]
    exact add_le_add (logSum_le (lowerLog_aux1 n hn) (prec + 1)) <|
      mul_le_mul_of_nonneg_left (logTwo_le wp) (mod_cast hk'.le)
  | case4 n k hn k' x' wp hk' hx' =>
    rw [lowerLog_aux2 n k hn, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), Rat.cast_zpow, Rat.cast_ofNat, log_zpow,
      toRat_add, Rat.cast_add]
    apply add_le_add (logSum_le (lowerLog_aux1 n hn) (prec + 1))
    rw [toRat_mul, Rat.cast_mul, toRat_intCast, Rat.cast_intCast, toRat_add, Rat.cast_add]
    exact mul_le_mul_of_nonpos_left (le_logTwo wp) (mod_cast Int.le_of_not_le hk')

theorem le_upperLog (x : Dyadic) (prec : ℕ) :
    log x.toRat ≤ (upperLog x prec).toRat := by
  unfold upperLog
  by_cases hx : x = 0 ∨ x = 1 ∨ x = -1
  · simp only [hx, ↓reduceIte, toRat_zero, Rat.cast_zero]
    rw [log_eq_zero.mpr]
    rcases hx with rfl | rfl | rfl <;> simp
  · simp [hx]
    grind [abs_lowerLog_le x prec]

end Log

/-- Logarithm of an Interval. -/
@[expose]
def log (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.abs with
  | ⟨WithBot.some lb, ⊤⟩ =>
    if lb = 0 then
      .univ Dyadic
    else
      .Ici <| lowerLog lb prec
  | ⟨WithBot.some lb, WithTop.some ub⟩ =>
    if lb = 0 then
      if ub = 0 then
        .singleton 0
      else
        .Iic <| (max (upperLog ub prec) 0)
    else
      ⟨lowerLog lb prec, upperLog ub prec⟩
  | _ => .univ Dyadic -- impossible case

@[inclusion_op interval_dyadic_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : x.log ∈ log I prec := by
  apply IntervalDyadicReal.abs_mem at hx
  rw [← Real.log_abs]
  have hx' : 0 ≤ |x| := abs_nonneg x
  generalize |x| = x at *
  fun_cases log with
  | case1 | case6 => apply Interval.mem_map_univ
  | case2 lb hI' hlb =>
    rw [hI'] at hx
    refine IntervalDyadicReal.mem_Ici_coe _ _ |>.mpr <|
      lowerLog_le lb prec |>.trans <| Real.log_le_log ?_ <|
        IntervalDyadicReal.mem_Ici_coe x lb |>.mp hx
    have := WithBot.coe_nonneg.mp <| hI' ▸ I.abs_lb_nonneg
    simpa using lt_of_le_of_ne this <| Ne.symm hlb
  | case3 hI' =>
    rw [hI'] at hx
    replace hx : 0 ≤ x ∧ x ≤ 0 := Dyadic.toReal_zero ▸ (IntervalDyadicReal.mem_mk_coe x 0 0).mp hx
    rw [le_antisymm hx.2 hx.1, Real.log_zero, ← Dyadic.toReal_zero]
    exact Interval.mem_map_singleton 0 Dyadic.toReal
  | case4 ub hub hI' =>
    rw [hI'] at hx
    replace hx : 0 ≤ x ∧ x ≤ Dyadic.toReal ub :=
      Dyadic.toReal_zero ▸ (IntervalDyadicReal.mem_mk_coe x 0 ub |>.mp hx)
    refine IntervalDyadicReal.mem_Iic_coe x.log (max (upperLog ub prec) 0) |>.mpr ?_
    rw [Monotone.map_max (f := Dyadic.toReal) Dyadic.toRealOrderEmbedding.monotone]
    simp only [Dyadic.toReal_zero, le_max_iff]
    by_cases hx₀ : x = 0
    · simp [hx₀, Dyadic.toReal]
    · exact Or.inl <| le_upperLog ub prec |>.trans' <| Real.log_le_log (by grind) hx.right
  | case5 lb ub hI' hlb =>
    rw [hI'] at hx
    replace hx : Dyadic.toReal lb ≤ x ∧ x ≤ Dyadic.toReal ub :=
      IntervalDyadicReal.mem_mk_coe x _ _ |>.mp hx
    simp only [IntervalDyadicReal.mem_mk_coe]
    have : 0 < Dyadic.toReal lb := by
      have := WithBot.coe_nonneg.mp <| hI' ▸ I.abs_lb_nonneg
      simpa [← Dyadic.toReal_zero] using lt_of_le_of_ne this <| Ne.symm hlb
    exact ⟨lowerLog_le lb prec |>.trans <| Real.log_le_log this <| hx.left,
      le_upperLog ub prec |>.trans' <| Real.log_le_log (this.trans_le hx.left) hx.right⟩

end IntervalDyadicReal

end Inclusion

/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# `Real.log` extension for tactic `dyadic_interval`

This file implements `Real.log` extension for the tactic `dyadic_interval`.

## Implementation notes

We first define `Inclusion.IntervalDyadicReal.smallArtanh`, which computes `artanh` of a small
rational number `num / den` using the binary splitting method. Then we use the identity
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

open Dyadic Finset Inclusion.IntervalDyadicReal.Dyadic Real

namespace Inclusion.IntervalDyadicReal

/-- The `n`-th partial sum of the `artanh` series at `num / den`,
returned as `(P, Q)` with `P / Q` equal to this sum.
Note that the series converges slowly when the input is close to `1`. -/
@[expose]
def smallArtanh (num den : ℕ) (n : ℕ) : ℕ × ℕ :=
  let r := go 0 n
  (num * r.2.2, den * r.2.1)
where
  /-- Binary splitting auxiliary function: `go a b` returns `(P, Q, R)` on segment `[a, b)`.

  `R` is the numerator of `∑ k ∈ Finset.Ico a b, ∏ j ∈ Finset.Ico a k, t (j + 1) / t j` put over
  the common denominator of the term ratios `((2 * k + 1) * num ^ 2) / ((2 * k + 3) * den ^ 2)`. -/
  go : ℕ → ℕ → ℕ × ℕ × ℕ := fun a b =>
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

namespace smallArtanh

theorem go_spec (num den a b : ℕ) :
    letI X := go num den a b
    X.1 = ∏ i ∈ Ico a b, (2 * i + 1) * num ^ 2 ∧
    X.2.1 = ∏ i ∈ Ico a b, (2 * i + 3) * den ^ 2 ∧
    X.2.2 = ∑ i ∈ Ico a b,
      (∏ j ∈ Ico a i, (2 * j + 1) * num ^ 2) * ∏ j ∈ Ico i b, (2 * j + 3) * den ^ 2 := by
  fun_induction go num den a b with
  | case1 a b h => simp [Ico_eq_empty_of_le (by lia : b ≤ a)]
  | case2 a b h => simp [show b = a + 1 by lia]
  | case3 a b n h m Pl Ql Rl hl Pr Qr Rr hr ihl ihr =>
    rw [hl] at ihl
    rw [hr] at ihr
    obtain ⟨rfl, rfl, rfl⟩ := ihl
    obtain ⟨rfl, rfl, rfl⟩ := ihr
    dsimp only
    split_ands
    · apply prod_Ico_consecutive <;> lia
    · apply prod_Ico_consecutive <;> lia
    · have ham : a ≤ m := by lia
      have hmb : m ≤ b := by lia
      rw [mul_sum, mul_sum, ← sum_Ico_consecutive _ ham hmb]
      congr 1 <;> refine sum_congr rfl fun i hi ↦ ?_
      · rw [← prod_Ico_consecutive _ (Finset.mem_Ico.mp hi).2.le hmb]
        ring
      · rw [← prod_Ico_consecutive _ ham (Finset.mem_Ico.mp hi).1]
        ring

theorem den_ne_zero (num den n : ℕ) (hden : den ≠ 0) :
    (smallArtanh num den n).2 ≠ 0 := by
  simp only [smallArtanh, (go_spec num den 0 n).2.1]
  simpa [hden] using prod_ne_zero_iff.mpr fun j _ => by positivity

theorem spec (num den n : ℕ) :
    letI X := smallArtanh num den n
    (X.1 : ℝ) / X.2 = ∑ k ∈ range n, (num / den : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  rw [smallArtanh]
  rcases eq_or_ne den 0 with rfl | hden; · simp
  simp only [(go_spec num den 0 n).2.1, (go_spec num den 0 n).2.2]
  push_cast
  rw [mul_div_mul_comm, div_eq_mul_inv (∑ _ ∈ _, _), sum_mul, mul_sum, Nat.Ico_zero_eq_range]
  refine sum_congr rfl fun i hi => ?_
  rw [← div_eq_mul_inv, Nat.Ico_zero_eq_range, ← prod_range_mul_prod_Ico _ (mem_range.mp hi).le,
    mul_div_mul_right _ _ (prod_ne_zero_iff.mpr fun j _ => by positivity), ← prod_div_distrib]
  induction i with
  | zero => simp
  | succ i ih =>
    specialize ih (by grind)
    simp_rw [prod_range_succ, ← _root_.mul_assoc, ih, div_pow, Nat.cast_add, Nat.cast_one, fieldEq]
    ring

/-- The partial sums computed by `smallArtanh` are lower bounds for `artanh (num / den)`. -/
theorem div_le_artanh {num den : ℕ} (h : num < den) (n : ℕ) :
    ((smallArtanh num den n).1 : ℝ) / (smallArtanh num den n).2 ≤ artanh (num / den) := by
  rw [spec]
  have : (num : ℝ) / den < 1 := by (have : den ≠ 0 := by lia); field_simp; norm_cast
  exact sum_range_le_artanh (by positivity) this n

/-- An upper bound for `artanh (num / den)` in terms of the partial sums computed by
`smallArtanh`. -/
theorem artanh_le_div_add {num den : ℕ} (h : num < den) (n : ℕ) :
    letI X := smallArtanh num den n
    artanh (num / den) ≤ (X.1 : ℝ) / X.2 + (num / den) ^ (2 * n + 1) / (1 - (num / den) ^ 2) := by
  rw [spec]
  have : (num : ℝ) / den < 1 := by (have : den ≠ 0 := by lia); field_simp; norm_cast
  exact artanh_le_sum_range_add (by positivity) this n

end smallArtanh

private theorem div_le_pow (p N prec m n : ℕ) (hp : 2 ≤ p) (hm : 2 ^ m ≤ p ^ 2)
    (hn : (1 / p) / (1 - (1 / p) ^ 2) ≤ (1 / 2 : ℝ) ^ n) (hN : prec ≤ m * N + n) :
    (1 / p : ℝ) ^ (2 * N + 1) / (1 - (1 / p) ^ 2) ≤ (step prec).toRat := by
  grw [pow_succ, mul_div_assoc, hn, toRat_step_real]
  apply pow_le_pow_iff_right_of_lt_one₀ (by simp) (by norm_num) |>.mpr hN |>.trans'
  rw [pow_add]
  gcongr
  rw [pow_mul, pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by simpa [field] using mod_cast hm) N

/-- Two-sided bounds for `artanh (1 / p)` in terms of the partial sums computed by `smallArtanh`,
with error at most `step prec`. -/
private theorem artanh_one_div_bounds (p N prec m n : ℕ) (hp : 2 ≤ p) (hm : 2 ^ m ≤ p ^ 2)
    (hn : (1 / p) / (1 - (1 / p) ^ 2) ≤ (1 / 2 : ℝ) ^ n) (hN : prec ≤ m * N + n) :
    letI X := smallArtanh 1 p N
    (X.1 : ℝ) / X.2 ≤ artanh (1 / p) ∧ artanh (1 / p) ≤ X.1 / X.2 + (step prec).toRat := by
  have hlo := smallArtanh.div_le_artanh (by lia : 1 < p) N
  have hup := smallArtanh.artanh_le_div_add (by lia : 1 < p) N
  rw [Nat.cast_one] at hlo hup
  refine ⟨hlo, hup.trans ?_⟩
  grw [div_le_pow p N prec m n hp hm hn hN]

/-- Computes a lower bound `l : Dyadic` for `log 2` with precision `prec`. -/
@[expose]
def logTwo (prec : ℕ) : Dyadic :=
  let (P1, Q1) : ℕ × ℕ := smallArtanh 1 17 ((prec + 7) / 8)
  let (P2, Q2) : ℕ × ℕ := smallArtanh 1 19 ((prec + 7) / 8)
  let (P3, Q3) : ℕ × ℕ := smallArtanh 1 31 ((prec + 8) / 9)
  let P : ℕ := 6 * P1 * Q2 * Q3 + 4 * Q1 * P2 * Q3 + 4 * Q1 * Q2 * P3
  let Q : ℕ := Q1 * Q2 * Q3
  natDivLower P Q (prec + 3)

theorem logTwo_spec (prec : ℕ) :
    (logTwo prec).toRat ≤ log 2 ∧ log 2 ≤ (logTwo prec).toRat + (step prec).toRat := by
  obtain ⟨l17, u17⟩ := artanh_one_div_bounds 17 ((prec + 7) / 8) (prec + 4) 8 4
    (by norm_num) (by norm_num) (by norm_num) (by lia)
  obtain ⟨l19, u19⟩ := artanh_one_div_bounds 19 ((prec + 7) / 8) (prec + 4) 8 4
    (by norm_num) (by norm_num) (by norm_num) (by lia)
  obtain ⟨l31, u31⟩ := artanh_one_div_bounds 31 ((prec + 8) / 9) (prec + 4) 9 4
    (by norm_num) (by norm_num) (by norm_num) (by lia)
  have h17 := smallArtanh.den_ne_zero 1 17 ((prec + 7) / 8) (by simp)
  have h19 := smallArtanh.den_ne_zero 1 19 ((prec + 7) / 8) (by simp)
  have h31 := smallArtanh.den_ne_zero 1 31 ((prec + 8) / 9) (by simp)
  push_cast at l17 u17 l19 u19 l31 u31
  simp only [logTwo, natDivLower_eq]
  generalize smallArtanh 1 17 ((prec + 7) / 8) = a17 at *
  generalize smallArtanh 1 19 ((prec + 7) / 8) = a19 at *
  generalize smallArtanh 1 31 ((prec + 8) / 9) = a31 at *
  obtain ⟨P1, Q1⟩ := a17
  obtain ⟨P2, Q2⟩ := a19
  obtain ⟨P3, Q3⟩ := a31
  generalize hr :
      ((6 * P1 * Q2 * Q3 + 4 * Q1 * P2 * Q3 + 4 * Q1 * Q2 * P3 : ℕ) / (Q1 * Q2 * Q3 : ℕ) : ℚ) = r
  have hr' : (r : ℝ) = 6 * (P1 / Q1 : ℝ) + 4 * (P2 / Q2) + 4 * (P3 / Q3) := by
    rw [← hr]
    push_cast
    field_simp
  have hlo : ((r.toDyadic (prec + 3)).toRat : ℝ) ≤ r := mod_cast Rat.toRat_toDyadic_le
  obtain ⟨-, hup⟩ := abs_le.mp (abs_toRat_toDyadic_le_real (x := r) (prec := prec + 3))
  have hstep :
      ((step prec).toRat : ℝ) = (step (prec + 3)).toRat + 14 * (step (prec + 4)).toRat := by
    norm_num [toRat_step, zpow_add₀]
    ring
  grind [log_two_eq_six_mul_artanh_add]

/-- Computes a lower bound `l : Dyadic` for `log (m / 2 ^ m.log2)` with precision `prec`.
Note that `m / 2 ^ m.log2 ∈ [1, 2)` when `m ≠ 0`. -/
@[expose]
def logSum (m : ℕ) (prec : ℕ) : Dyadic :=
  -- with `x = m / 2 ^ e`, we have `(x - 1) / (x + 1) = (m - 2 ^ e) / (m + 2 ^ e) ∈ [0, 1 / 3)`
  let e : ℕ := m.log2
  -- Dyadic.smallArtanh → δ₁ < step (prec + 2), although we only need `≤`
  let (P, Q) : ℕ × ℕ := smallArtanh (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
  -- natDivLower → δ₂ ≤ step (prec + 2)
  -- δ ≤ 2 * (δ₁ + δ₂) < step prec
  2 * natDivLower P Q (prec + 2)

theorem logSum_spec {m : ℕ} (hm : m ≠ 0) (prec : ℕ) :
    (logSum m prec).toRat ≤ log (m / 2 ^ m.log2) ∧
      log (m / 2 ^ m.log2) ≤ (logSum m prec).toRat + (step prec).toRat := by
  fun_cases logSum with
  | case1 e P Q hPQ =>
    have hem : 2 ^ e ≤ m := Nat.log2_self_le hm
    have hlt : m - 2 ^ e < m + 2 ^ e := by have := Nat.two_pow_pos e; lia
    have hlo := smallArtanh.div_le_artanh hlt (prec / 3 + 1)
    have hup := smallArtanh.artanh_le_div_add hlt (prec / 3 + 1)
    simp only [hPQ] at hlo hup
    set X : ℝ := (m - 2 ^ e : ℕ) / (m + 2 ^ e : ℕ)
    have hX1 : X < 1 / 3 := by
      unfold X
      field_simp
      norm_cast
      grind [m.lt_log2_self]
    have hX2 : 0 ≤ X := by positivity
    have herr : X ^ (2 * (prec / 3 + 1) + 1) / (1 - X ^ 2) ≤ (step (prec + 2)).toRat := by
      have := div_le_pow 3 (prec / 3 + 1) (prec + 2) 3 1
        (by norm_num) (by norm_num) (by norm_num) (by lia)
      push_cast at this
      refine le_trans ?_ this
      gcongr
    have hlog : log (m / 2 ^ m.log2) = 2 * artanh X := by
      rw [log_eq_two_mul_artanh (by positivity)]
      congr 2
      simp [hem, field, X]
    have hround : (((P / Q : ℚ).toDyadic (prec + 2)).toRat : ℝ) ≤ (P / Q : ℚ) :=
      mod_cast Rat.toRat_toDyadic_le
    obtain ⟨-, hround'⟩ :=
      abs_le.mp (abs_toRat_toDyadic_le_real (x := (P / Q : ℚ)) (prec := prec + 2))
    have hstep : ((step prec).toRat : ℝ) = 4 * (step (prec + 2)).toRat := by
      norm_num [toRat_step, zpow_add₀]
      ring
    push_cast at hround hround'
    simp only [natDivLower_eq, toRat_mul, toRat_ofNat, hlog]
    push_cast
    constructor <;> linarith

/-- Computes a lower bound for `log x` with precision `prec`. -/
@[expose]
def lowerLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  match x with
  | zero => 0
  | ofOdd n p _ =>
    let m : ℕ := n.natAbs
    let k : ℤ := m.log2 - p -- `|x| = x' * 2 ^ k` where `x' = m / 2 ^ m.log2 ∈ [1, 2)`
    let wp : ℕ := prec + k.natAbs.log2 + 2
    let l2 : Dyadic := if 0 ≤ k then logTwo wp else logTwo wp + step wp
    logSum m (prec + 1) + k * l2

theorem lowerLog_spec (x : Dyadic) (prec : ℕ) :
    (lowerLog x prec).toRat ≤ log x.toRat ∧
      log x.toRat ≤ (lowerLog x prec).toRat + (step prec).toRat := by
  fun_cases lowerLog x prec with
  | case1 => simp [Dyadic.zero_eq]
  | case2 n p hn m k wp l2 =>
    have hm : m ≠ 0 := by lia
    have H1 := logSum_spec hm (prec + 1)
    push_cast at H1
    obtain ⟨H2, H2'⟩ := logTwo_spec wp
    have hwp : (|k| * (step wp).toRat : ℝ) ≤ (step (prec + 1)).toRat := by
      grw [← Int.natCast_natAbs, k.natAbs.lt_log2_self.le]
      · simp [toRat_step, pow_succ, zpow_add₀, field, wp]
      · simp
    have hl2 : (k * l2.toRat : ℝ) ≤ k * log 2 ∧
        (k * log 2 : ℝ) ≤ k * l2.toRat + |k| * (step wp).toRat := by
      simp only [l2]
      split_ifs with hk
      · have hk' : (0 : ℝ) ≤ k := mod_cast hk
        rw [Int.cast_abs, abs_of_nonneg hk']
        have := mul_le_mul_of_nonneg_left H2' hk'
        exact ⟨mul_le_mul_of_nonneg_left H2 hk', by linarith⟩
      · have hk' : (k : ℝ) ≤ 0 := mod_cast (not_le.mp hk).le
        rw [Int.cast_abs, abs_of_nonpos hk', toRat_add, Rat.cast_add]
        have := mul_le_mul_of_nonpos_left H2 hk'
        exact ⟨mul_le_mul_of_nonpos_left H2' hk', by linarith⟩
    have hlog : log ((ofOdd n p hn).toRat : ℝ) = log (m / 2 ^ m.log2) + k * log 2 := by
      have hn' : (n : ℝ) ≠ 0 := by rwa [Int.cast_ne_zero, ← Int.natAbs_ne_zero]
      have hm' : (m : ℝ) = |(n : ℝ)| := by simp [m, Nat.cast_natAbs]
      rw [toRat_ofOdd_eq_mul_two_pow, log_div (mod_cast hm) (by positivity), hm', log_abs]
      push_cast [k]
      rw [log_mul hn' (by positivity), log_zpow, log_pow]
      push_cast
      ring
    rw [step_eq_add prec, hlog]
    simp only [toRat_add, toRat_mul, toRat_intCast, Rat.cast_add, Rat.cast_mul, Rat.cast_intCast]
    constructor <;> linarith [H1.1, H1.2]

/-- An enclosure of `log x` of width `step prec`, which is exact when `log x = 0`. -/
@[expose]
def logPoint (x : Dyadic) (prec : ℕ) : Interval Dyadic :=
  if x = 0 ∨ x = 1 ∨ x = -1 then
    .singleton 0
  else
    let l := lowerLog x prec
    .Icc l (l + step prec)

theorem logPoint_mem (x : Dyadic) (prec : ℕ) : Real.log (toReal x) ∈ logPoint x prec := by
  rw [mem_iff_mem_map, logPoint]
  split_ifs with hx
  · convert Interval.mem_map_singleton (0 : Dyadic) Dyadic.toReal
    rcases hx with rfl | rfl | rfl <;> simp [Dyadic.toReal]
  · obtain ⟨hl, hu⟩ := lowerLog_spec x prec
    exact Interval.mem_map_Icc _ hl (by simpa [Dyadic.toReal] using hu)

/-- Logarithm of an `Interval Dyadic`, computed from the enclosures `logPoint` at the endpoints of
its absolute value. When `0` lies in the interval, the result must also contain `log 0 = 0`. -/
@[expose]
def log (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.abs with
  | ⟨some l, some u⟩ =>
    if l = 0 then
      if u = 0 then .singleton 0 else (Interval.singleton 0).hull (.Iic (logPoint u prec).ub)
    else
      .Icc (logPoint l prec).lb (logPoint u prec).ub
  | ⟨some l, ⊤⟩ => if l = 0 then .univ Dyadic else .Ici (logPoint l prec).lb
  | ⟨⊥, _⟩ => .univ Dyadic -- impossible since `0 ≤ I.abs.lb`

@[inclusion_op interval_dyadic_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) :
    Real.log x ∈ log I prec := by
  replace hx := mem_iff_mem_map.mp (abs_mem hx)
  rw [← Real.log_abs, mem_iff_mem_map]
  have hx₀ : 0 ≤ |x| := abs_nonneg x
  generalize |x| = x at hx hx₀
  have h0 : Real.log 0 = toRealOrderEmbedding 0 := Real.log_zero.trans toReal_zero.symm
  -- if the lower endpoint `l` of `I.abs` is nonzero, then it is positive
  have hpos {l : Dyadic} {u : WithTop Dyadic} (hI : I.abs = ⟨l, u⟩) (hl : l ≠ 0) :
      0 < toReal l := by
    have := I.abs_lb_nonneg
    simp only [hI, WithBot.coe_nonneg] at this
    simpa [toReal] using lt_of_le_of_ne this (Ne.symm hl)
  fun_cases log with
  | case1 hI =>
    rw [hI] at hx
    obtain rfl : x = 0 := le_antisymm ((Interval.le_map_ub _ hx).trans_eq toReal_zero) hx₀
    rw [h0]
    exact Interval.mem_map_singleton _ _
  | case2 u _ hI =>
    rw [hI] at hx
    change _ ∈ Interval.map _ toRealOrderEmbedding
    rcases hx₀.eq_or_lt with rfl | hx₀
    · rw [h0]
      exact Interval.hull_mem_left _ (Interval.mem_map_singleton _ _)
    · exact Interval.hull_mem_right _ <| Interval.mem_Iic_of_le
        (Real.log_le_log hx₀ (Interval.le_map_ub _ hx)) (logPoint_mem u prec)
  | case3 l u hI hl =>
    rw [hI] at hx
    have hlx := Interval.map_lb_le _ hx
    exact Interval.mem_Icc_of_le (logPoint_mem l prec) (Real.log_le_log (hpos hI hl) hlx)
      (Real.log_le_log ((hpos hI hl).trans_le hlx) (Interval.le_map_ub _ hx))
      (logPoint_mem u prec)
  | case4 | case6 => exact Interval.mem_map_univ _ _
  | case5 l hI hl =>
    rw [hI] at hx
    exact Interval.mem_Ici_of_le (Real.log_le_log (hpos hI hl) (Interval.map_lb_le _ hx))
      (logPoint_mem l prec)

end Inclusion.IntervalDyadicReal

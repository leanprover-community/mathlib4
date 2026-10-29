
/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens's theorems (hunt r_3c1cbb, Wikidata Q1196729)

Mertens's first theorem with explicit constants, in both the von Mangoldt
form and the prime form, against Mathlib v4.33.0-rc2, which carries no
Mertens statement of its own.

* `sum_log_eq_sum_vonMangoldt_mul_div`: the summatory identity
  `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`, from
  `ArithmeticFunction.vonMangoldt_sum` by counting multiples.
* `log_sub_one_le_sum_vonMangoldt_div`: the lower half on its own, where
  the loss is only `1`: `log N − 1 ≤ ∑_{n ≤ N} Λ(n)/n` for `N ≥ 1`.
* `abs_sum_vonMangoldt_div_sub_log_le`: Mertens's first theorem, von
  Mangoldt form: `|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 3/2` for `N ≥ 1`.
* `mertens_first_bracket`: the prime form as the asymmetric bracket the
  proof gives, `−4 ≤ ∑_{p ≤ N} (log p)/p − log N ≤ log 4 + 3/2`, with
  `sum_log_div_prime_sub_log_le` and `neg_four_le_sum_log_div_prime_sub_log`
  the two halves on their own.
* `mertens_first_theorem`: Mertens's first theorem, prime form, in its
  usual symmetric statement `|∑_{p ≤ N} (log p)/p − log N| ≤ log 4 + 3`,
  which is the weakening of the bracket that discards the asymmetry.

The constants are explicit and still not optimal (the true error in the
prime form is bounded by 2); they are what the elementary argument gives
without any numerical case analysis.

The upper Chebyshev input is Mathlib's `Chebyshev.psi_le`
(`ψ x ≤ x log 4 + 2 √x log x`), whose remainder is majorised here by
`log_le_div_exp_one` rather than by Mathlib's own
`psi_le_const_mul_self`: writing `log x = 2 log √x ≤ 2 √x / e` gives
`2 √x log x ≤ (4/e) x ≤ (3/2) x`, where Mathlib's packaged corollary
settles for `4 x`.  The factorial bounds are replaced by an induction
using `log (1 + 1/M) ≤ 1/M`, so no integral comparison and no Stirling
estimate is needed anywhere in the file.  The prime-power correction is
controlled by `Chebyshev.sum_PrimePow_eq_sum_sum`, a geometric tail in
the exponent, and a telescoping bound for `∑ n^(-3/2)`.

The same `log t ≤ t/e` majorant is what replaces `log n ≤ 2 √n` in
`sum_log_div_sq_le`; together with dropping the vanishing `n = 1` term
that carries `∑_{n ≤ N} (log n)/n²` from `6` to `3/2`.
-/


@[expose] public section

open Finset Real
open ArithmeticFunction hiding log id

/-! ## The summatory identity -/

/-- `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`: sum `vonMangoldt_sum` over
`n ≤ N` and count multiples of each `d`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, log n = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Ioc 0 N, log n = ∑ d ∈ Ioc 0 N with d ∣ n, Λ d := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [← vonMangoldt_sum]
    refine (sum_congr ?_ fun _ _ => rfl).symm
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hd0, _⟩, hd⟩
      exact ⟨hd, hn.1.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn.1, (Nat.le_of_dvd hn.1 hd).trans hn.2⟩, hd⟩
  rw [sum_congr rfl h1]
  simp_rw [sum_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

/-! ## Bounds on the log-factorial sum -/

/-- Upper bound `∑_{n ≤ N} log n ≤ N log N`, termwise. -/
theorem sum_log_le (N : ℕ) : ∑ n ∈ Ioc 0 N, log n ≤ (N : ℝ) * log N := by
  calc ∑ n ∈ Ioc 0 N, log n ≤ ∑ _n ∈ Ioc 0 N, log N := by
        refine sum_le_sum fun n hn => ?_
        rw [mem_Ioc] at hn
        exact log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    _ = (N : ℝ) * log N := by
        rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- Lower bound `N log N − N + 1 ≤ ∑_{n ≤ N} log n` for `N ≥ 1`, by
induction: the step needs only `M log(1 + 1/M) ≤ 1`, which is
`log x ≤ x − 1`.  This replaces the usual integral comparison. -/
theorem sum_log_ge (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * log N - N + 1 ≤ ∑ n ∈ Ioc 0 N, log n := by
  induction N with
  | zero => exact absurd hN (by norm_num)
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      rw [Nat.Ioc_succ_singleton, sum_singleton]
      norm_num
    · have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]
      have key : (M : ℝ) * (log (M + 1) - log M) ≤ 1 := by
        have hlog : log (((M : ℝ) + 1) / M) ≤ ((M : ℝ) + 1) / M - 1 :=
          log_le_sub_one_of_pos (by positivity)
        rw [log_div (by positivity) (by positivity)] at hlog
        have hfrac : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
        rw [hfrac] at hlog
        calc (M : ℝ) * (log (M + 1) - log M) ≤ (M : ℝ) * (1 / M) :=
              mul_le_mul_of_nonneg_left hlog (by linarith)
          _ = 1 := by field_simp
      have ihM := ih hM
      push_cast
      nlinarith [key, ihM]

/-! ## The `log t ≤ t/e` majorant and a sharper Chebyshev constant -/

/-- `log t ≤ t / e` for `t > 0`: apply `log x ≤ x − 1` at `x = t/e` and use
`log e = 1`.  This is the sharp form of the crude `log x ≤ x − 1`, and it
is the majorant that replaces `log n ≤ 2 √n` below: composing it with
`log t = 2 log √t` gives `log t ≤ (2/e) √t`, whose constant `2/e` is the
best possible (it is attained at `t = e²`). -/
theorem log_le_div_exp_one {t : ℝ} (ht : 0 < t) : log t ≤ t / exp 1 := by
  have he0 : (0 : ℝ) < exp 1 := exp_pos 1
  have h := log_le_sub_one_of_pos (x := t / exp 1) (by positivity)
  rw [log_div ht.ne' he0.ne', log_exp] at h
  linarith

/-- A sharper Chebyshev constant than Mathlib's packaged
`Chebyshev.psi_le_const_mul_self` (`ψ x ≤ (log 4 + 4) x`): for `x ≥ 1`,
`ψ x ≤ (log 4 + 3/2) x`.

The main term `x log 4` is Mathlib's and untouched; only the remainder of
`Chebyshev.psi_le` is re-estimated.  Mathlib bounds `2 √x log x` by `4 x`;
writing `log x = 2 log √x` and applying `log_le_div_exp_one` to `√x` gives
`2 √x log x ≤ (4/e) x`, and `4/e < 3/2` because `3 e > 8`. -/
theorem psi_le_const_mul_self' {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ (log 4 + 3 / 2) * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : (0 : ℝ) < √x := sqrt_pos.mpr hx0
  have hss : √x * √x = x := mul_self_sqrt hx0.le
  have he : (2.7182818283 : ℝ) < exp 1 := exp_one_gt_d9
  have he0 : (0 : ℝ) < exp 1 := exp_pos 1
  have hlogx : log x = 2 * log (√x) := by rw [log_sqrt hx0.le]; ring
  have hlogs : log (√x) ≤ √x / exp 1 := log_le_div_exp_one hs
  have h2 : √x * (√x / exp 1) = x / exp 1 := by rw [← mul_div_assoc, hss]
  have h3 : x / exp 1 ≤ (3 / 8) * x := by
    rw [div_le_iff₀ he0]
    nlinarith [mul_le_mul_of_nonneg_left he.le hx0.le, hx0]
  have hrem : 2 * √x * log x ≤ (3 / 2) * x := by
    have h1 : 4 * (√x * log (√x)) ≤ 4 * (√x * (√x / exp 1)) := by
      have := mul_le_mul_of_nonneg_left hlogs hs.le
      linarith
    calc 2 * √x * log x = 4 * (√x * log (√x)) := by rw [hlogx]; ring
      _ ≤ 4 * (√x * (√x / exp 1)) := h1
      _ = 4 * (x / exp 1) := by rw [h2]
      _ ≤ (3 / 2) * x := by linarith
  calc Chebyshev.psi x ≤ log 4 * x + 2 * √x * log x := Chebyshev.psi_le hx
    _ ≤ log 4 * x + (3 / 2) * x := by linarith
    _ = (log 4 + 3 / 2) * x := by ring

/-! ## Mertens's first theorem, von Mangoldt form -/

/-- `Chebyshev.psi` at a natural argument is the plain finite sum. -/
theorem psi_natCast (N : ℕ) : Chebyshev.psi (N : ℝ) = ∑ n ∈ Ioc 0 N, Λ n := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- The lower half of Mertens's first theorem in von Mangoldt form, stated
separately because its loss is only `1`, against the `log 4 + 3/2` the
upper half costs: for `N ≥ 1`, `log N − 1 ≤ ∑_{n ≤ N} Λ(n)/n`.

The prime form inherits this asymmetry, so keeping the halves apart is
what lets `mertens_first_theorem` carry `log 4 + 3` rather than the
`log 4 + 3/2 + 3` a symmetric band would force. -/
theorem log_sub_one_le_sum_vonMangoldt_div {N : ℕ} (hN : 1 ≤ N) :
    log N - 1 ≤ ∑ d ∈ Ioc 0 N, Λ d / d := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hTle : ∑ n ∈ Ioc 0 N, log n ≤ (N : ℝ) * ∑ d ∈ Ioc 0 N, Λ d / d := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, mul_sum]
    refine sum_le_sum fun d hd => ?_
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = (N : ℝ) * (Λ d / d) := by ring
  have hTlb := sum_log_ge N hN
  have h1 : (N : ℝ) * (log N - 1) ≤ (N : ℝ) * ∑ d ∈ Ioc 0 N, Λ d / d := by
    nlinarith [hTle, hTlb]
  exact le_of_mul_le_mul_left h1 hN0

/-- Mertens's first theorem, von Mangoldt form, with the explicit
constant `log 4 + 3/2`: for `N ≥ 1`,
`|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 3/2`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ d ∈ Ioc 0 N, Λ d / d) - log N| ≤ log 4 + 3 / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- upper bound for T := ∑ log n in terms of S := ∑ Λ d / d
  have hTle : ∑ n ∈ Ioc 0 N, log n ≤ (N : ℝ) * ∑ d ∈ Ioc 0 N, Λ d / d := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, mul_sum]
    refine sum_le_sum fun d hd => ?_
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = (N : ℝ) * (Λ d / d) := by ring
  -- lower bound: T ≥ N·S − ψ(N)
  have hTge : (N : ℝ) * (∑ d ∈ Ioc 0 N, Λ d / d) - Chebyshev.psi N
      ≤ ∑ n ∈ Ioc 0 N, log n := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, psi_natCast, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun d hd => ?_
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hfloor : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have h := Nat.sub_one_lt_floor ((N : ℝ) / (d : ℝ))
      rwa [Nat.floor_div_natCast, Nat.floor_natCast] at h
    calc (N : ℝ) * (Λ d / d) - Λ d = Λ d * ((N : ℝ) / d - 1) := by ring
      _ ≤ Λ d * ((N / d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hfloor.le vonMangoldt_nonneg
  have hpsi : Chebyshev.psi (N : ℝ) ≤ (log 4 + 3 / 2) * N :=
    psi_le_const_mul_self' hN1R
  have hTub := sum_log_le N
  rw [abs_le]
  constructor
  · -- S ≥ log N − 1 ≥ log N − (log 4 + 3/2)
    have h2 := log_sub_one_le_sum_vonMangoldt_div hN
    have h4 : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
    linarith
  · -- S ≤ log N + (log 4 + 3/2)
    have h1 : (N : ℝ) * (∑ d ∈ Ioc 0 N, Λ d / d)
        ≤ (N : ℝ) * (log N + (log 4 + 3 / 2)) := by nlinarith [hTge, hTub, hpsi]
    have h2 := le_of_mul_le_mul_left h1 hN0
    linarith

/-! ## Elementary summation bounds for the prime-power correction -/

/-- Telescoping bound `∑_{n ≤ N} 1/(n √n) ≤ 3 − 2/√N` for `N ≥ 1`.  The
step is `1/((M+1)√(M+1)) ≤ 2/√M − 2/√(M+1)`. -/
theorem sum_inv_mul_sqrt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, ((n : ℝ) * √(n : ℝ))⁻¹ ≤ 3 - 2 / √(N : ℝ) := by
  induction N with
  | zero => exact absurd hN (by norm_num)
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      rw [Nat.Ioc_succ_singleton, sum_singleton]
      norm_num
    · have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have ihM := ih hM
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]
      have ha : (0 : ℝ) < √(M : ℝ) := sqrt_pos.mpr (by linarith)
      have hb : (0 : ℝ) < √((M : ℝ) + 1) := sqrt_pos.mpr (by linarith)
      have hab : √(M : ℝ) ≤ √((M : ℝ) + 1) := sqrt_le_sqrt (by linarith)
      have ha2 : √(M : ℝ) ^ 2 = (M : ℝ) := sq_sqrt (by linarith)
      have hb2 : √((M : ℝ) + 1) ^ 2 = (M : ℝ) + 1 := sq_sqrt (by linarith)
      have hdiff : (√((M : ℝ) + 1) - √(M : ℝ)) * (√((M : ℝ) + 1) + √(M : ℝ)) = 1 := by
        nlinarith [ha2, hb2]
      have hsum_pos : (0 : ℝ) < √((M : ℝ) + 1) + √(M : ℝ) := by positivity
      have hba_eq : √((M : ℝ) + 1) - √(M : ℝ)
          = 1 / (√((M : ℝ) + 1) + √(M : ℝ)) := by
        rw [eq_div_iff hsum_pos.ne']
        exact hdiff
      have key : (((M : ℕ) + 1 : ℝ) * √((M : ℝ) + 1))⁻¹
          ≤ 2 / √(M : ℝ) - 2 / √((M : ℝ) + 1) := by
        have h1 : 2 / √(M : ℝ) - 2 / √((M : ℝ) + 1)
            = 2 / ((√((M : ℝ) + 1) + √(M : ℝ)) * (√(M : ℝ) * √((M : ℝ) + 1))) := by
          rw [div_sub_div _ _ ha.ne' hb.ne',
            div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (2 * (√(M : ℝ) * √((M : ℝ) + 1))) * hdiff
        rw [h1, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        -- (b+a)·a·b ≤ 2·(M+1)·b with b² = M+1, a ≤ b
        nlinarith [hb2, ha, hb,
          mul_nonneg (mul_nonneg hb.le hb.le) (sub_nonneg.mpr hab),
          mul_nonneg (mul_nonneg hb.le ha.le) (sub_nonneg.mpr hab),
          mul_nonneg (mul_nonneg hb.le hsum_pos.le) (sub_nonneg.mpr hab)]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      calc (∑ n ∈ Ioc 0 M, ((n : ℝ) * √(n : ℝ))⁻¹)
            + (((M + 1 : ℕ) : ℝ) * √((M + 1 : ℕ) : ℝ))⁻¹
          ≤ (3 - 2 / √(M : ℝ)) + (2 / √(M : ℝ) - 2 / √((M : ℝ) + 1)) := by
            rw [hcast]
            exact add_le_add ihM key
        _ = 3 - 2 / √(((M + 1 : ℕ) : ℝ)) := by rw [hcast]; ring

/-- `∑_{n ≤ N} (log n)/n² ≤ 3/2`.

Two independent tightenings of the same telescoping argument: the
majorant is `log n ≤ (2/e) √n` (`log_le_div_exp_one` composed with
`log n = 2 log √n`) rather than `log n ≤ 2 √n`, and the vanishing `n = 1`
term is dropped before the telescope is applied, which turns
`∑_{n ≤ N} n^{-3/2} ≤ 3` into `∑_{2 ≤ n ≤ N} n^{-3/2} ≤ 2`.  Together
they give `(2/e)·2 = 4/e < 3/2`, against the `2·3 = 6` of the crude
route.  For reference, the limit is `−ζ'(2) = 0.9375…`. -/
theorem sum_log_div_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 ≤ 3 / 2 := by
  have he0 : (0 : ℝ) < exp 1 := exp_pos 1
  have he : (2.7182818283 : ℝ) < exp 1 := exp_one_gt_d9
  have h01 : (Ioc 0 1 : Finset ℕ) = {1} := by
    ext x
    simp only [mem_Ioc, mem_singleton]
    omega
  -- the n = 1 term vanishes, so the sum starts at 2
  have hdrop : ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2
      = ∑ n ∈ Ioc 1 N, log n / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN, h01, sum_singleton]
    norm_num
  -- likewise the telescoped sum loses its n = 1 term, which is 1
  have hsplit : ∑ n ∈ Ioc 0 N, ((n : ℝ) * √(n : ℝ))⁻¹
      = 1 + ∑ n ∈ Ioc 1 N, ((n : ℝ) * √(n : ℝ))⁻¹ := by
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN, h01, sum_singleton]
    norm_num
  have htel : ∑ n ∈ Ioc 1 N, ((n : ℝ) * √(n : ℝ))⁻¹ ≤ 2 := by
    have h := sum_inv_mul_sqrt_le N hN
    rw [hsplit] at h
    have hsN : (0 : ℝ) < √(N : ℝ) := sqrt_pos.mpr (by exact_mod_cast hN)
    have : (0 : ℝ) < 2 / √(N : ℝ) := by positivity
    linarith
  have hstep : ∀ n ∈ Ioc 1 N,
      log n / (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) * √(n : ℝ))⁻¹ / exp 1 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.le
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hs : (0 : ℝ) < √(n : ℝ) := sqrt_pos.mpr hn0
    have hss : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := mul_self_sqrt hn0.le
    have hEq : 2 * √(n : ℝ) / (n : ℝ) ^ 2 = 2 * ((n : ℝ) * √(n : ℝ))⁻¹ := by
      rw [eq_comm, mul_comm 2 _, inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity)]
      nlinarith [hss]
    have hlog : log n ≤ 2 * √(n : ℝ) / exp 1 := by
      have h1 : log ((n : ℝ)) = 2 * log (√(n : ℝ)) := by
        rw [log_sqrt hn0.le]; ring
      have h2 : log (√(n : ℝ)) ≤ √(n : ℝ) / exp 1 := log_le_div_exp_one hs
      rw [h1]
      calc 2 * log (√(n : ℝ)) ≤ 2 * (√(n : ℝ) / exp 1) := by linarith
        _ = 2 * √(n : ℝ) / exp 1 := by ring
    calc log n / (n : ℝ) ^ 2 ≤ (2 * √(n : ℝ) / exp 1) / (n : ℝ) ^ 2 := by gcongr
      _ = (2 * √(n : ℝ) / (n : ℝ) ^ 2) / exp 1 := by ring
      _ = 2 * ((n : ℝ) * √(n : ℝ))⁻¹ / exp 1 := by rw [hEq]
  have hSnn : (0 : ℝ) ≤ ∑ n ∈ Ioc 1 N, ((n : ℝ) * √(n : ℝ))⁻¹ :=
    sum_nonneg fun n _ => by positivity
  calc ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2
      = ∑ n ∈ Ioc 1 N, log n / (n : ℝ) ^ 2 := hdrop
    _ ≤ ∑ n ∈ Ioc 1 N, 2 * ((n : ℝ) * √(n : ℝ))⁻¹ / exp 1 := sum_le_sum hstep
    _ = 2 * (∑ n ∈ Ioc 1 N, ((n : ℝ) * √(n : ℝ))⁻¹) / exp 1 := by
        rw [← sum_div, ← mul_sum]
    _ ≤ 2 * 2 / exp 1 := by gcongr
    _ ≤ 3 / 2 := by
        rw [div_le_iff₀ he0]
        linarith

/-- Geometric tail `∑_{k=2}^{K} 2⁻ᵏ ≤ 2⁻¹ − 2⁻ᴷ` for `K ≥ 1`. -/
theorem sum_geom_tail_le (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Icc 2 K, ((2 : ℝ)⁻¹) ^ k ≤ 2⁻¹ - (2⁻¹ : ℝ) ^ K := by
  induction K, hK using Nat.le_induction with
  | base =>
    rw [show Icc 2 1 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpow : (0 : ℝ) < (2⁻¹ : ℝ) ^ M := by positivity
    have hstep : ((2 : ℝ)⁻¹) ^ (M + 1) = ((2 : ℝ)⁻¹) ^ M * 2⁻¹ := pow_succ _ _
    nlinarith [ih, hpow]

/-! ## Mertens's first theorem, prime form -/

/-- Mertens's first theorem, prime form, as the **two-sided bracket the
proof actually gives**: for `N ≥ 1`,
`−4 ≤ ∑_{p ≤ N} (log p)/p − log N ≤ log 4 + 3/2`.

The sum runs over primes `p ≤ N`.  The distance to the von Mangoldt form
is the prime-power correction `∑_{p^k ≤ N, k ≥ 2} (log p)/p^k`, which is
nonnegative and at most `3`.  (Its limit is `0.7553…`.)

The two sides come by different routes, which is why they are not equal:
above, the prime sum is at most the von Mangoldt sum, so it inherits that
form's `log 4 + 3/2 ≈ 2.886`; below, it exceeds `log N − 1 − 3`, using the
one-sided `log_sub_one_le_sum_vonMangoldt_div` rather than the symmetric
band, so `−4`.  `mertens_first_theorem` is the symmetric `log 4 + 3`
weakening of this, and `sum_log_div_prime_sub_log_le` and
`neg_four_le_sum_log_div_prime_sub_log` are the two halves on their own.
A consumer that adds the two sides, as Mertens's second theorem does,
should take the halves and not the symmetric band. -/
theorem mertens_first_bracket {N : ℕ} (hN : 1 ≤ N) :
    -4 ≤ (∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N
      ∧ (∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N ≤ log 4 + 3 / 2 := by
  have h4 : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
  rcases eq_or_lt_of_le hN with hN1 | hN2
  · -- N = 1: both sums are empty or zero
    subst hN1
    have h0 : (∑ p ∈ (Ioc 0 1 : Finset ℕ) with p.Prime, log p / p)
        - log ((1 : ℕ) : ℝ) = 0 := by
      have hset : (Ioc 0 1 : Finset ℕ) = {1} := by
        ext x
        simp only [mem_Ioc, mem_singleton]
        omega
      rw [hset]
      simp [Finset.filter_singleton, Nat.not_prime_one]
    exact ⟨by linarith, by linarith⟩
  · have hN2 : 2 ≤ N := hN2
    have hN0 : (0 : ℝ) < N := by positivity
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    -- the von Mangoldt sum equals its restriction to prime powers
    have hfil : (∑ n ∈ Ioc 0 N with IsPrimePow n, Λ n / n) = ∑ d ∈ Ioc 0 N, Λ d / d := by
      refine sum_filter_of_ne fun n _ h => ?_
      have hΛ : Λ n ≠ 0 := by
        intro h0
        exact h (by rw [h0, zero_div])
      exact vonMangoldt_ne_zero_iff.mp hΛ
    -- decompose over exponents
    set K := ⌊log (N : ℝ) / log 2⌋₊ with hK
    have hK1 : 1 ≤ K := by
      rw [hK, Nat.one_le_floor_iff, le_div_iff₀ (log_pos (by norm_num)), one_mul]
      exact log_le_log (by norm_num) (by exact_mod_cast hN2)
    have hdec : (∑ n ∈ Ioc 0 N with IsPrimePow n, Λ n / n)
        = ∑ k ∈ Icc 1 K, ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
            Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
      have h := Chebyshev.sum_PrimePow_eq_sum_sum (R := ℝ)
        (fun n => Λ n / n) (Nat.cast_nonneg N)
      rw [Nat.floor_natCast] at h
      exact h
    -- the k = 1 layer is the prime sum
    have hone : (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (1 : ℕ))⌋₊ with p.Prime,
        Λ (p ^ 1) / ((p ^ 1 : ℕ) : ℝ))
        = ∑ p ∈ Ioc 0 N with p.Prime, log p / p := by
      rw [show ((1 : ℝ) / (1 : ℕ)) = 1 by norm_num, rpow_one, Nat.floor_natCast]
      refine sum_congr rfl fun p hp => ?_
      rw [mem_filter] at hp
      rw [pow_one, vonMangoldt_apply_prime hp.2]
    -- split off k = 1
    rw [← add_sum_Ioc_eq_sum_Icc hK1] at hdec
    rw [hone] at hdec
    -- the tail is nonnegative
    have htail_nonneg : (0 : ℝ) ≤ ∑ k ∈ Ioc 1 K,
        ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
      refine sum_nonneg fun k _ => sum_nonneg fun p _ => ?_
      exact div_nonneg vonMangoldt_nonneg (by positivity)
    -- per-layer bound for k ≥ 2
    have hlayer : ∀ k ∈ Ioc 1 K,
        (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          Λ (p ^ k) / ((p ^ k : ℕ) : ℝ))
        ≤ 4 * ((2 : ℝ)⁻¹) ^ k * ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 := by
      intro k hk
      rw [mem_Ioc] at hk
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
      -- the inner index set sits inside Ioc 0 N
      have hsub : (Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊).filter Nat.Prime
          ⊆ Ioc 0 N := by
        refine (filter_subset _ _).trans (Finset.Ioc_subset_Ioc_right ?_)
        have hfle : (N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ)) ≤ (N : ℝ) :=
          rpow_le_self_of_one_le hN1R (by
            rw [div_le_one (by positivity)]
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
        calc ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ ≤ ⌊(N : ℝ)⌋₊ :=
              Nat.floor_le_floor hfle
          _ = N := Nat.floor_natCast N
      -- termwise: log p / p^(2+j) ≤ (log p / p²) (2⁻¹)^j
      have hterm : ∀ p ∈ (Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊).filter Nat.Prime,
          Λ (p ^ (2 + j)) / ((p ^ (2 + j) : ℕ) : ℝ)
          ≤ (log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by
        intro p hp
        rw [mem_filter] at hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hΛ : Λ (p ^ (2 + j)) = log p := by
          rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp.2]
        have hcast : ((p ^ (2 + j) : ℕ) : ℝ) = (p : ℝ) ^ (2 + j) := by push_cast; rfl
        rw [hΛ, hcast]
        have hden : (p : ℝ) ^ 2 * (2 : ℝ) ^ j ≤ (p : ℝ) ^ (2 + j) := by
          rw [pow_add]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by norm_num) hp2 j) (by positivity)
        have hlogp : (0 : ℝ) ≤ log p := log_nonneg (by linarith)
        calc log p / (p : ℝ) ^ (2 + j) ≤ log p / ((p : ℝ) ^ 2 * (2 : ℝ) ^ j) := by
              gcongr
          _ = (log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by
              rw [inv_pow, ← div_div, div_eq_mul_inv]
      calc (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ with p.Prime,
            Λ (p ^ (2 + j)) / ((p ^ (2 + j) : ℕ) : ℝ))
          ≤ ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ with p.Prime,
              (log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := sum_le_sum hterm
        _ = (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ with p.Prime,
              log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by rw [sum_mul]
        _ ≤ (∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => ?_
            rw [mem_Ioc] at hn
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
            exact div_nonneg (log_nonneg this) (by positivity)
        _ = 4 * ((2 : ℝ)⁻¹) ^ (2 + j) * ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 := by
            rw [pow_add]
            ring_nf
    -- sum the layers: tail ≤ 2 B ≤ 3
    have hB := sum_log_div_sq_le N hN
    have hBnn : (0 : ℝ) ≤ ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 := by
      refine sum_nonneg fun n hn => ?_
      rw [mem_Ioc] at hn
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      exact div_nonneg (log_nonneg this) (by positivity)
    have htail_le : (∑ k ∈ Ioc 1 K,
        ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)) ≤ 3 := by
      have hIoc : (Ioc 1 K : Finset ℕ) = Icc 2 K := by
        ext x
        simp only [mem_Ioc, mem_Icc]
        omega
      calc (∑ k ∈ Ioc 1 K, ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
            Λ (p ^ k) / ((p ^ k : ℕ) : ℝ))
          ≤ ∑ k ∈ Ioc 1 K,
              4 * ((2 : ℝ)⁻¹) ^ k * ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 :=
            sum_le_sum hlayer
        _ = 4 * (∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2) * ∑ k ∈ Ioc 1 K, ((2 : ℝ)⁻¹) ^ k := by
            rw [mul_sum]
            refine sum_congr rfl fun k _ => by ring
        _ ≤ 4 * (∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2) * (2 : ℝ)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hIoc]
            have := sum_geom_tail_le K hK1
            have hpow : (0 : ℝ) < (2⁻¹ : ℝ) ^ K := by positivity
            linarith
        _ ≤ 4 * (3 / 2) * (2 : ℝ)⁻¹ := by
            have h6 : (0 : ℝ) < 3 / 2 := by norm_num
            nlinarith [hB, hBnn]
        _ = 3 := by norm_num
    -- assemble
    have hvM := abs_sum_vonMangoldt_div_sub_log_le hN
    have hlow := log_sub_one_le_sum_vonMangoldt_div hN
    rw [hfil] at hdec
    rw [abs_le] at hvM
    constructor
    · -- lower: prime sum ≥ Λ sum − 3 ≥ log N − 1 − 3 = log N − 4
      nlinarith [hdec, htail_le, hlow]
    · -- upper: prime sum ≤ Λ sum ≤ log N + log 4 + 3/2
      nlinarith [hdec, htail_nonneg, hvM.2]

/-- The upper half of Mertens's first theorem, prime form, on its own:
for `N ≥ 1`, `∑_{p ≤ N} (log p)/p − log N ≤ log 4 + 3/2 ≈ 2.886`.  This is
the side that inherits the von Mangoldt band unchanged, the prime sum
being at most the von Mangoldt sum. -/
theorem sum_log_div_prime_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N ≤ log 4 + 3 / 2 :=
  (mertens_first_bracket hN).2

/-- The lower half of Mertens's first theorem, prime form, on its own:
for `N ≥ 1`, `−4 ≤ ∑_{p ≤ N} (log p)/p − log N`.  The `4` is `1 + 3`: the
one-sided von Mangoldt bound `log N − 1 ≤ ∑ Λ(n)/n` less the prime-power
correction, which is at most `3`. -/
theorem neg_four_le_sum_log_div_prime_sub_log {N : ℕ} (hN : 1 ≤ N) :
    -4 ≤ (∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N :=
  (mertens_first_bracket hN).1

/-- **Mertens's first theorem** with the explicit constant `log 4 + 3`:
for `N ≥ 1`, `|∑_{p ≤ N} (log p)/p − log N| ≤ log 4 + 3`.

This is the symmetric weakening of `mertens_first_bracket`, kept because
it is the statement the theorem is usually quoted in.  It is strictly
weaker on both sides (`log 4 + 3 ≈ 4.386` against `2.886` above and `4`
below), so a consumer that cares about the constant should take the two
halves instead.  `4 ≤ log 4 + 3` because `1 ≤ log 4`. -/
theorem mertens_first_theorem {N : ℕ} (hN : 1 ≤ N) :
    |(∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N| ≤ log 4 + 3 := by
  have h41 : (1 : ℝ) ≤ log 4 := by
    have hlt : exp 1 ≤ (4 : ℝ) := by linarith [exp_one_lt_d9]
    calc (1 : ℝ) = log (exp 1) := (log_exp 1).symm
      _ ≤ log 4 := log_le_log (exp_pos 1) hlt
  obtain ⟨hl, hu⟩ := mertens_first_bracket hN
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩


@[expose] public section

/-!
# Mertens's second theorem (hunt r_3c1cbb, Wikidata Q1196729)

Mertens's second theorem with an explicit constant, on top of the first
theorem proved in this file:

* `mertens_second_theorem`: `|∑_{p ≤ N} 1/p − log log N| ≤ 9` for every
  natural `N` (the sum over primes `p ≤ N`; for `N ≤ 1` both sides are
  interpreted with Mathlib's `log 0 = 0` and the bound is trivial).

The proof is the classical partial summation against
`A(n) = ∑_{p ≤ n} log p / p = log n + O(1)`, where the `O(1)` band is the
first theorem taken one side at a time, as
`−4 ≤ A(n) − log n ≤ log 4 + 3/2` (`mertens_first_bracket`):

* `sum_inv_primes_eq` is the discrete Abel identity
  `∑_{p ≤ N} 1/p = A(N)/log N + ∑_{n=2}^{N−1} A(n)(1/log n − 1/log(n+1))`,
  proved by induction from `N = 2`.
* The main-term sum `∑ log n (1/log n − 1/log(n+1))` is compared with
  `log log N` termwise through the bracket
  `(v−u)/v ≤ log v − log u ≤ (v−u)/u`, the gap being controlled by
  `∑ 1/n²` (Mathlib's `sum_Ioc_inv_sq_le_sub`).

The constant `9` is explicit and still not optimal (the classical bound
for the same error is Mertens's own `≤ 4`).  It replaces the `16` this
file carried until the two steps below, and before that a `76`.

Two separate pieces of slack came out, in that order.

**The cancellation.**  The first theorem's band enters twice, once
through the boundary term `A(N)/log N` and once through the telescoped
tail, but the two contributions are `c · (1/log N)` and
`c · (1/log 2 − 1/log N)`: the `1/log N` cancels exactly, so together
they are `c/log 2`, not twice that.  The file used to weaken each of
them separately before adding.  Fixing only that, with the symmetric
`c = log 4 + 3`, gives `8.35` above and `−9.35` below, so a band of `10`.

**The asymmetry.**  `mertens_first_theorem` is a symmetric `log 4 + 3`,
but its proof gives `−4 ≤ A(n) − log n ≤ log 4 + 3/2`, and the two sides
of the second theorem use opposite halves.  Taking the halves through
`mertens_first_bracket` instead gives

    S − loglog N ≤ 1 − loglog 2 + (log 4 + 3/2)/log 2 < 1 + 1 + 4.17 = 6.17,
    S − loglog N ≥ 1 − loglog 2 − 4 − 4/log 2 > 1 + 0 − 4 − 5.78 = −8.78,

so `9`, and the lower side is now the whole of the constraint: the upper
side would allow `7`.

The slack that is left on the binding side, largest first: the `4` from
`∑ 1/n²` against the quadratic gap in the logarithm bracket; the `3`
inside the first theorem's own `−4`, which bounds a prime-power
correction whose limit is `0.7553…`; and `loglog 2`, bounded here in
`(−1, 0)` when it is `−0.3665…`.  None of those is a cancellation, so
none of them is free the way the two steps above were.
-/


open Finset Real

/-! ## The elementary logarithm bracket -/

/-- Upper half of the bracket: `log v − log u ≤ (v − u)/u` for `0 < u ≤ v`. -/
theorem log_sub_log_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    log v - log u ≤ (v - u) / u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  rw [← log_div hv.ne' hu.ne']
  calc log (v / u) ≤ v / u - 1 := log_le_sub_one_of_pos (by positivity)
    _ = (v - u) / u := by rw [sub_div, div_self hu.ne']

/-- Lower half of the bracket: `(v − u)/v ≤ log v − log u` for `0 < u ≤ v`. -/
theorem sub_div_le_log_sub_log {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (v - u) / v ≤ log v - log u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  rw [← log_div hv.ne' hu.ne']
  have h := one_sub_inv_le_log_of_pos (x := v / u) (by positivity)
  rw [show (v / u)⁻¹ = u / v by rw [inv_div]] at h
  calc (v - u) / v = 1 - u / v := by rw [sub_div, div_self hv.ne']
    _ ≤ log (v / u) := h

/-- The form the lower half takes after partial summation:
`x(x⁻¹ − y⁻¹) ≤ log y − log x` for `0 < x ≤ y`. -/
theorem mul_inv_sub_inv_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x * (x⁻¹ - y⁻¹) ≤ log y - log x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hid : x * (x⁻¹ - y⁻¹) = (y - x) / y := by
    rw [mul_sub, mul_inv_cancel₀ hx.ne', sub_div, div_self hy.ne', div_eq_mul_inv]
  rw [hid]
  exact sub_div_le_log_sub_log hx hxy

/-- The form the upper half takes after partial summation, with the
quadratic gap made explicit: for `1/2 < x ≤ y` and `(y − x)² ≤ c`,
`log y − log x ≤ x(x⁻¹ − y⁻¹) + 4c`.  The factor `4` is `1/(xy) < 4`. -/
theorem log_sub_log_le_mul_add {x y c : ℝ} (hx : 1 / 2 < x) (hxy : x ≤ y)
    (hc : (y - x) ^ 2 ≤ c) :
    log y - log x ≤ x * (x⁻¹ - y⁻¹) + 4 * c := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hy2 : (1 : ℝ) / 2 < y := by linarith
  have hc0 : (0 : ℝ) ≤ c := le_trans (sq_nonneg _) hc
  have hxy0 : (0 : ℝ) < x * y := by positivity
  have hxy4 : (1 : ℝ) ≤ 4 * (x * y) := by nlinarith
  have hbr := log_sub_log_le hx0 hxy
  have hid : x * (x⁻¹ - y⁻¹) = 1 - x / y := by
    rw [mul_sub, mul_inv_cancel₀ hx0.ne', div_eq_mul_inv]
  have hid2 : (y - x) / y = 1 - x / y := by rw [sub_div, div_self hy0.ne']
  have hgap : (y - x) / x - (y - x) / y ≤ 4 * c := by
    have heq : (y - x) / x - (y - x) / y = (y - x) ^ 2 / (x * y) := by
      rw [div_sub_div _ _ hx0.ne' hy0.ne',
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [heq, div_le_iff₀ hxy0]
    nlinarith [hc, hc0, hxy4]
  linarith [hbr, hgap, hid, hid2]

/-! ## Telescoping and the prime-filter split -/

/-- Telescoping over `Ico 2 N`. -/
theorem sum_Ico_telescope (g : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ico 2 N, (g n - g (n + 1)) = g 2 - g N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih => rw [Finset.sum_Ico_succ_top hM, ih]; ring

/-- Splitting the top point off a prime-filtered sum. -/
theorem sum_filter_prime_succ (g : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Ioc 0 (N + 1) with p.Prime, g p
      = (∑ p ∈ Ioc 0 N with p.Prime, g p)
        + if (N + 1).Prime then g (N + 1) else 0 := by
  rw [sum_filter, sum_filter, Finset.sum_Ioc_succ_top (Nat.zero_le N)]

/-! ## The Abel identity -/

/-- Discrete summation by parts specialised to the prime harmonic sum:
for `N ≥ 2`,
`∑_{p ≤ N} 1/p = A(N)/log N + ∑_{n=2}^{N−1} A(n)(1/log n − 1/log(n+1))`
with `A(n) = ∑_{p ≤ n} log p / p`.  The proof is induction on `N`: the
increment of both sides at `N + 1` is `1/(N+1)` when `N + 1` is prime
(since `(log p / p) / log p = 1/p`) and `0` otherwise. -/
theorem sum_inv_primes_eq {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Ioc 0 N with p.Prime, ((p : ℝ))⁻¹
      = (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N
        + ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
            * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h2 : (Ioc 0 2).filter Nat.Prime = {2} := by decide
    rw [h2]
    simp only [sum_singleton, Finset.Ico_self, sum_empty, add_zero]
    have hl2 : (0 : ℝ) < log ((2 : ℕ) : ℝ) := log_pos (by norm_num)
    rw [div_right_comm, div_self hl2.ne', one_div]
  | succ M hM ih =>
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hlogM : (0 : ℝ) < log (M : ℝ) := log_pos (by linarith)
    have hlogM1 : (0 : ℝ) < log ((M : ℝ) + 1) := log_pos (by linarith)
    have hM10 : ((M : ℝ) + 1) ≠ 0 := by positivity
    rw [sum_filter_prime_succ, sum_filter_prime_succ, Finset.sum_Ico_succ_top hM, ih]
    push_cast
    by_cases hp : (M + 1).Prime
    · simp only [hp, ite_true]
      field_simp
      ring
    · simp only [hp, ite_false]
      field_simp
      ring

/-! ## The `∑ 1/n²` control -/

/-- `∑_{n=2}^{N−1} 1/n² ≤ 1`, from Mathlib's partial-sum bound. -/
theorem sum_inv_sq_Ico_le_one {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹ ≤ 1 := by
  have hsub : (Ico 2 N : Finset ℕ) ⊆ Ioc 1 N := fun x hx => by
    rw [mem_Ico] at hx
    rw [mem_Ioc]
    omega
  have h1 : ∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹ ≤ ∑ n ∈ Ioc 1 N, (((n : ℝ)) ^ 2)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  have h2 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) one_ne_zero (by omega)
  have h3 : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
  push_cast at h2
  rw [inv_one] at h2
  linarith

/-! ## Mertens's second theorem -/

/-- Mertens's second theorem with the explicit constant `9`, for `N ≥ 2`:
`|∑_{p ≤ N} 1/p − log log N| ≤ 9`.  The argument gives `6.17` above and
`−8.78` below; `9` is the band that covers both, and only the lower side
needs it. -/
theorem mertens_second_theorem_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    |(∑ p ∈ Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - log (log N)| ≤ 9 := by
  -- numeric groundwork
  have hlg : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hll : log 2 < (0.6931471808 : ℝ) := log_two_lt_d9
  have hlog2 : (0 : ℝ) < log 2 := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) < log (N : ℝ) := log_pos (by linarith)
  have hmul : log 2 * (log 2)⁻¹ = 1 := mul_inv_cancel₀ hlog2.ne'
  have hinvpos : (0 : ℝ) < (log 2)⁻¹ := by positivity
  have hinv2 : (log 2)⁻¹ < 1.443 := by nlinarith
  have hinvN0 : (0 : ℝ) ≤ (log (N : ℝ))⁻¹ := by positivity
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have hcu : log 4 + 3 / 2 ≤ (2.887 : ℝ) := by rw [hlog4]; linarith
  have hL2neg : log (log 2) < 0 := log_neg hlog2 (by linarith)
  have hL2gt : (-1 : ℝ) < log (log 2) := by
    have h := one_sub_inv_le_log_of_pos hlog2
    linarith
  -- Each side of the first theorem's bracket reaches the answer exactly
  -- once, as its own constant over `log 2`.  The boundary term contributes
  -- `c/log N` and the telescoped tail `c (1/log 2 − 1/log N)`; both are
  -- carried unweakened below so that the `1/log N` cancels, and only their
  -- sum is estimated here.  The two `c`s are different, which is the point:
  -- the upper side never sees the `4` and the lower side never sees `log 4`.
  have hcu_inv2 : (log 4 + 3 / 2) * (log 2)⁻¹ ≤ 4.17 := by
    calc (log 4 + 3 / 2) * (log 2)⁻¹ ≤ 2.887 * 1.443 :=
          mul_le_mul hcu hinv2.le hinvpos.le (by norm_num)
      _ ≤ 4.17 := by norm_num
  have hcl_inv2 : (4 : ℝ) * (log 2)⁻¹ ≤ 5.78 := by
    calc (4 : ℝ) * (log 2)⁻¹ ≤ 4 * 1.443 :=
          mul_le_mul_of_nonneg_left hinv2.le (by norm_num)
      _ ≤ 5.78 := by norm_num
  -- the boundary term `A(N)/log N = 1 + O(1/log N)`, kept unweakened
  have hANu := sum_log_div_prime_sub_log_le (N := N) (by omega)
  have hANl := neg_four_le_sum_log_div_prime_sub_log (N := N) (by omega)
  have hEq : (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N - 1
      = ((∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N) * (log (N : ℝ))⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hlogN.ne', div_eq_mul_inv]
  have hHead_ub : (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N - 1
      ≤ (log 4 + 3 / 2) * (log (N : ℝ))⁻¹ := by
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hANu hinvN0
  have hHead_lb : -(4 * (log (N : ℝ))⁻¹)
      ≤ (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N - 1 := by
    rw [hEq]
    have h1 : (-4 : ℝ) * (log (N : ℝ))⁻¹
        ≤ ((∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N) * (log (N : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right hANl hinvN0
    linarith
  -- termwise upper bound on the Abel sum
  have hterm_ub : ∀ n ∈ Ico 2 N,
      (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
          * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
        ≤ (log (log ((n : ℝ) + 1)) - log (log n))
          + (log 4 + 3 / 2) * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hx : (0 : ℝ) < log (n : ℝ) := log_pos (by linarith)
    have hxy : log (n : ℝ) ≤ log ((n : ℝ) + 1) := log_le_log (by linarith) (by linarith)
    have hd0 : (0 : ℝ) ≤ (log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹ := by
      have := inv_anti₀ hx hxy
      linarith
    have hup := mul_inv_sub_inv_le hx hxy
    have hAu := sum_log_div_prime_sub_log_le (N := n) (by omega)
    have h1 := mul_le_mul_of_nonneg_right hAu hd0
    linarith [h1, hup]
  -- termwise lower bound on the Abel sum
  have hterm_lb : ∀ n ∈ Ico 2 N,
      (log (log ((n : ℝ) + 1)) - log (log n)) - 4 * (((n : ℝ)) ^ 2)⁻¹
          - 4 * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
        ≤ (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
            * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hninv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
    have hx : (0 : ℝ) < log (n : ℝ) := log_pos (by linarith)
    have hxhalf : (1 : ℝ) / 2 < log (n : ℝ) := by
      have h := log_le_log (by norm_num : (0 : ℝ) < 2) hn2
      linarith [log_two_gt_d9]
    have hxy : log (n : ℝ) ≤ log ((n : ℝ) + 1) := log_le_log (by linarith) (by linarith)
    have hd0 : (0 : ℝ) ≤ (log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹ := by
      have := inv_anti₀ hx hxy
      linarith
    have hΔ : log ((n : ℝ) + 1) - log (n : ℝ) ≤ ((n : ℝ))⁻¹ := by
      have h := log_sub_log_le hn0 (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
      rw [add_sub_cancel_left, one_div] at h
      exact h
    have hΔ0 : (0 : ℝ) ≤ log ((n : ℝ) + 1) - log (n : ℝ) := by linarith
    have hsq : (log ((n : ℝ) + 1) - log (n : ℝ)) ^ 2 ≤ (((n : ℝ)) ^ 2)⁻¹ := by
      have h1 : (((n : ℝ))⁻¹) ^ 2 = (((n : ℝ)) ^ 2)⁻¹ := by rw [inv_pow]
      nlinarith [hΔ, hΔ0, hninv0, h1]
    have hlow := log_sub_log_le_mul_add hxhalf hxy hsq
    have hAl := neg_four_le_sum_log_div_prime_sub_log (N := n) (by omega)
    have h1 := mul_le_mul_of_nonneg_right hAl hd0
    linarith [h1, hlow]
  -- the two telescoped sums
  have hLtel : ∑ n ∈ Ico 2 N, (log (log ((n : ℝ) + 1)) - log (log n))
      = log (log (N : ℝ)) - log (log 2) := by
    have h := sum_Ico_telescope (fun m => log (log (m : ℝ))) hN
    push_cast at h
    have h2 : ∑ n ∈ Ico 2 N, (log (log ((n : ℝ) + 1)) - log (log n))
        = -∑ n ∈ Ico 2 N, (log (log (n : ℝ)) - log (log ((n : ℝ) + 1))) := by
      rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl fun n _ => by ring
    rw [h2, h]
    ring
  have hdtel : ∑ n ∈ Ico 2 N, ((log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹)
      = (log 2)⁻¹ - (log (N : ℝ))⁻¹ := by
    have h := sum_Ico_telescope (fun m => (log (m : ℝ))⁻¹) hN
    push_cast at h
    exact h
  -- assembled bounds on the Abel sum
  have hB_ub : ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
        * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
      ≤ (log (log (N : ℝ)) - log (log 2))
        + (log 4 + 3 / 2) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) := by
    calc ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
          * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
        ≤ ∑ n ∈ Ico 2 N, ((log (log ((n : ℝ) + 1)) - log (log n))
            + (log 4 + 3 / 2) * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)) :=
          sum_le_sum hterm_ub
      _ = (∑ n ∈ Ico 2 N, (log (log ((n : ℝ) + 1)) - log (log n)))
          + (log 4 + 3 / 2)
            * ∑ n ∈ Ico 2 N, ((log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
          rw [sum_add_distrib, ← mul_sum]
      _ = (log (log (N : ℝ)) - log (log 2))
          + (log 4 + 3 / 2) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) := by
          rw [hLtel, hdtel]
  have hsqsum := sum_inv_sq_Ico_le_one hN
  have hB_lb : (log (log (N : ℝ)) - log (log 2)) - 4
        - 4 * ((log 2)⁻¹ - (log (N : ℝ))⁻¹)
      ≤ ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
          * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
    have hchain : ∑ n ∈ Ico 2 N, ((log (log ((n : ℝ) + 1)) - log (log n))
          - 4 * (((n : ℝ)) ^ 2)⁻¹
          - 4 * ((log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹))
        = (log (log (N : ℝ)) - log (log 2))
          - 4 * (∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹)
          - 4 * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) := by
      rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hLtel, hdtel]
    have hmono := sum_le_sum hterm_lb
    rw [hchain] at hmono
    have h4 : 4 * (∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹) ≤ 4 := by linarith
    linarith
  -- conclusion
  rw [sum_inv_primes_eq hN, abs_le]
  constructor
  · linarith [hHead_lb, hB_lb, hcl_inv2, hL2neg]
  · linarith [hHead_ub, hB_ub, hcu_inv2, hL2gt]

/-- **Mertens's second theorem**, prime-reciprocal form, with the explicit
constant `9`: for every natural `N`,
`|∑_{p ≤ N} 1/p − log log N| ≤ 9`.  The sum runs over primes `p ≤ N`.
For `N ≤ 1` the sum is empty and `log (log N) = 0` under Mathlib's
convention `log 0 = 0`, `log 1 = 0`, so the bound is trivial there. -/
theorem mertens_second_theorem (N : ℕ) :
    |(∑ p ∈ Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - log (log N)| ≤ 9 := by
  by_cases hN : 2 ≤ N
  · exact mertens_second_theorem_of_two_le hN
  · rw [not_le] at hN
    interval_cases N
    · norm_num
    · have hset : (Ioc 0 1 : Finset ℕ) = {1} := by
        ext x
        simp only [mem_Ioc, mem_singleton]
        omega
      rw [hset]
      simp [Finset.filter_singleton, Nat.not_prime_one]


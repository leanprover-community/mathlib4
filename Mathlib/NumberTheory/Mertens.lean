/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.NumberTheory.Chebyshev

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Mertens' first theorem

This file proves an explicit form of Mertens' first theorem: for every natural number `n`, the
sum of `log p / p` over primes `p ≤ n` differs from `log n` by at most `2`.
-/

public section

open scoped BigOperators
open Real Finset MeasureTheory

namespace Mertens

/-!
The first section proves an auxiliary estimate for the error term
`∑' p prime, log p / (p * (p - 1)) < 1`.

The proof splits off `p = 2, 3`, dominates the remaining primes by all odd integers, bounds that
odd tail by an integral, and finally inserts explicit logarithmic estimates.
-/

/-- The real-variable term `log (2 * x + 1) / ((2 * x + 1) * (2 * x))`
from the odd tail. -/
noncomputable def oddLogDivMulPred (x : ℝ) : ℝ :=
  log (2 * x + 1) / ((2 * x + 1) * (2 * x))

lemma oddLogDivMulPred_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ oddLogDivMulPred x :=
  div_nonneg (log_nonneg (by linarith)) (by positivity)

lemma oddLogDivMulPred_le {x : ℝ} (hx : 1 ≤ x) :
    oddLogDivMulPred x ≤ 2 * x ^ (-(3 / 2 : ℝ)) := by
  have hxpos : 0 < x := by linarith
  let a := 2 * x + 1
  let b := 2 * x
  have ha_pos : 0 < a := by linarith
  have hlog_le : log a ≤ 2 * sqrt a := by
    have h := log_le_rpow_div ha_pos.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [sqrt_eq_rpow]
    linarith
  calc
    _ = log a / (a * b) := by simp [oddLogDivMulPred, a, b]
    _ ≤ (2 * sqrt a) / (a * b) := by gcongr
    _ = 2 / (sqrt a * b) := by
      rw [show a * b = sqrt a ^ 2 * b by rw [sq_sqrt ha_pos.le]]
      field_simp [sqrt_ne_zero'.mpr ha_pos]
    _ ≤ 2 / (sqrt x * x) := by
      have hx_le_a : x ≤ a := by linarith
      have hx_le_b : x ≤ b := by linarith
      have hden_pos : 0 < sqrt x * x := mul_pos (sqrt_pos.mpr hxpos) hxpos
      exact div_le_div_of_nonneg_left (by norm_num) hden_pos (by gcongr)
    _ = 2 * x ^ (-(3 / 2 : ℝ)) := by
      rw [sqrt_eq_rpow, rpow_neg hxpos.le, show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num,
        rpow_add hxpos, rpow_one]
      ring_nf

private lemma hasDerivAt_neg_log_add_one_div :
    ∀ u ∈ Set.Ici 5, HasDerivAt (fun u ↦ -((log u + 1) / u)) (log u / u ^ 2) u := by
  intro u hu
  have hu_ne : u ≠ 0 := by grind
  have h := ((hasDerivAt_log hu_ne).add_const 1).div (hasDerivAt_id u) hu_ne
  convert h.neg using 1
  simp only [id_eq, field]
  ring

private lemma tendsto_neg_log_add_one_div_atTop :
    Filter.Tendsto (fun u ↦ -((log u + 1) / u)) Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun u ↦ log u / u) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hone : Filter.Tendsto (fun u ↦ (1 : ℝ) / u) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h : Filter.Tendsto (fun u ↦ (log u + 1) / u) Filter.atTop (nhds 0) := by
    convert hlog.add hone using 1
    · ext u
      ring
    · norm_num
  simpa using h.neg

lemma summable_primeLogDivMulPred : Summable fun p : Nat.Primes ↦ log p / (p * (p - 1)) := by
  have hmajor : Summable fun p : Nat.Primes ↦ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro ⟨n, hp⟩
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast hp.one_lt
    exact div_nonneg (log_natCast_nonneg n) (by positivity)
  · intro ⟨n, hp⟩
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hp.pos
    have hden_lower : (n ^ 2) / 2 ≤ n * ((n : ℝ) - 1) := by
      have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
      nlinarith [sq_nonneg (n - 2)]
    calc
      _ = log n / (n * (n - 1)) := by simp
      _ ≤ (2 * n ^ (1 / 2 : ℝ)) / (n ^ 2 / 2) := by
        gcongr
        have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
        linarith [log_natCast_le_rpow_div n (ε := 1 / 2) (by norm_num)]
      _ = 4 * (n ^ (1 / 2 : ℝ) / n ^ 2) := by ring
      _ = 4 * (n ^ (1 / 2 : ℝ) / n ^ (2 : ℝ)) := by norm_num [rpow_natCast]
      _ = 4 * n ^ ((1 / 2 : ℝ) - 2) := by rw [rpow_sub hn0]
      _ = 4 * n ^ (-(3 / 2 : ℝ)) := by norm_num

lemma summable_full : Summable fun n : ℕ ↦ oddLogDivMulPred (n : ℝ) := by
  have hpow : Summable fun n : ℕ ↦ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2
  refine Summable.of_norm_bounded_eventually_nat hpow ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn1 : 1 ≤ n := by lia
  have hnonneg : 0 ≤ oddLogDivMulPred n := oddLogDivMulPred_nonneg (by exact_mod_cast hn1)
  rw [norm_of_nonneg hnonneg]
  simpa using oddLogDivMulPred_le (x := n) (by exact_mod_cast hn1)

lemma summable_oddLogDivMulPred_nat_tail : Summable fun k : Set.Ici 2 ↦ oddLogDivMulPred k :=
  summable_full.subtype (Set.Ici 2)

lemma integral_oddLogDivMulPred_converges : IntegrableOn oddLogDivMulPred (Set.Ioi 2) := by
  have hmajor : IntegrableOn (fun x : ℝ ↦ 2 * x ^ (-(3 / 2 : ℝ))) (Set.Ioi 2) := by
    let F : ℝ → ℝ := fun x ↦ -4 * x ^ (-(1 / 2 : ℝ))
    have hderiv : ∀ x ∈ Set.Ici 2, HasDerivAt F (2 * x ^ (-(3 / 2 : ℝ))) x := by
      intro x hx
      have hx2 : 2 ≤ x := hx
      have hxpos : 0 < x := by linarith
      have h := (hasDerivAt_rpow_const (p := -(1 / 2)) (Or.inl (ne_of_gt hxpos))).const_mul (-4)
      have h' : HasDerivAt (fun y ↦ -4 * y ^ (-(1 / 2 : ℝ))) (2 * x ^ (-(3 / 2 : ℝ))) x := by
        convert h using 1
        ring_nf
      simpa [F] using h'
    have hpos : ∀ x ∈ Set.Ioi (2 : ℝ), 0 ≤ 2 * x ^ (-(3 / 2 : ℝ)) := by
      intro x hx
      have hx2 : 2 < x := hx
      have hxpos : 0 < x := by linarith
      exact mul_nonneg (by norm_num) (rpow_nonneg hxpos.le _)
    have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
      simpa [F] using(tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (-4)
    exact integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  refine Integrable.mono_nonneg hmajor.integrable ?_ ?_ ?_
  · unfold oddLogDivMulPred
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 2 < x := hx
    exact div_nonneg (log_nonneg (by linarith)) (show 0 < (2 * x + 1) * (2 * x) by nlinarith).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 2 < x := hx
    exact oddLogDivMulPred_le (show 1 ≤ x by linarith)

lemma tsum_primeLogDivMulPred_split_two_three : ∑' p : Nat.Primes, log p / (p * (p - 1))
    = log 2 / 2 + log 3 / 6 + ∑' p : {p : Nat.Primes // 5 ≤ (p : ℕ)}, log p / (p * (p - 1)) := by
  let p2 : Nat.Primes := ⟨2, by decide⟩
  let p3 : Nat.Primes := ⟨3, by decide⟩
  let s : Finset Nat.Primes := {p2, p3}
  have hsum : ∑ x ∈ s, log x / (x * (x - 1)) = log 2 / 2 + log 3 / 6 := by grind
  have htail : ∑' q : {q : Nat.Primes // q ∉ s}, log q / (q * (q - 1))
        = ∑' p : {p : Nat.Primes // 5 ≤ (p : ℕ)}, log p / (p * (p - 1)) := by
    have hmem_iff (q : Nat.Primes): q ∉ s ↔ 5 ≤ (q : ℕ) := by
      simp only [mem_insert, mem_singleton, not_or, s, p2, p3]
      constructor
      · rintro ⟨hnot2, hnot3⟩
        have hnot2' : (q : ℕ) ≠ 2 := fun h ↦ hnot2 (Subtype.ext h)
        have hnot3' : (q : ℕ) ≠ 3 := fun h ↦ hnot3 (Subtype.ext h)
        have hnot4 : (q : ℕ) ≠ 4 := by
          intro h4
          have hq4 : Nat.Prime 4 := by simpa [h4] using q.property
          exact (by decide : ¬ Nat.Prime 4) hq4
        have h2le : 2 ≤ (q : ℕ) := q.property.two_le
        lia
      · grind
    let e : {q : Nat.Primes // q ∉ s} ≃ {p : Nat.Primes // 5 ≤ (p : ℕ)} :=
      Equiv.subtypeEquiv (Equiv.refl Nat.Primes) hmem_iff
    exact e.tsum_eq (fun p ↦ log p / (p * (p - 1)))
  rw [← summable_primeLogDivMulPred.sum_add_tsum_subtype_compl s, hsum, htail]

lemma prime_tail_lt_odd_tail : ∑' p : {p : Nat.Primes // 5 ≤ p.1}, log p / (p * (p - 1))
    < ∑' k : Set.Ici 2, oddLogDivMulPred k := by
  let P := {p : Nat.Primes // 5 ≤ (p : ℕ)}
  let e : P → Set.Ici 2 := fun p ↦ ⟨(p : ℕ) / 2, by grind⟩
  let k4 : Set.Ici 2 := ⟨4, by grind⟩
  have heinj : Function.Injective e := by
    intro p q hpq
    ext
    have hpodd : Odd (p : ℕ) := p.1.property.odd_of_ne_two (by lia)
    have hqodd : Odd (q : ℕ) := q.1.property.odd_of_ne_two (by lia)
    exact Subtype.ext (by grind)
  have hek4 : ∀ p : P, e p ≠ k4 := by
    intro p hp
    have hdiv : (p : ℕ) / 2 = 4 := congrArg (fun k : Set.Ici 2 ↦ (k : ℕ)) hp
    have hpodd : Odd (p : ℕ) := p.1.property.odd_of_ne_two (by lia)
    have hp9 : (p : ℕ) = 9 := by grind
    have hnot : ¬ Nat.Prime (p : ℕ) := by
      rw [hp9]
      decide
    exact hnot p.1.property
  have hterm (p : P) : log p / (p * (p - 1)) = oddLogDivMulPred ((e p : Set.Ici 2) : ℕ) := by
    unfold oddLogDivMulPred e
    have hpodd : Odd (p : ℕ) := p.1.property.odd_of_ne_two (by lia)
    have hpeq_real : 2 * (p / 2 : ℕ) + 1 = (p : ℝ) := by norm_cast; grind
    have hppred_real : 2 * ((p / 2 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      calc
        _ = (((p : ℕ) - 1 : ℕ) : ℝ) := by norm_cast; grind
        _ = (p : ℝ) - 1 := by norm_num [Nat.cast_sub (by lia : 1 ≤ (p : ℕ))]
    rw [hpeq_real, hppred_real]
  have hodd_nonneg (k : Set.Ici 2) : 0 ≤ oddLogDivMulPred k :=
    oddLogDivMulPred_nonneg (by grind [Nat.one_le_cast])
  let rest := fun k ↦ if k  = k4 then 0 else oddLogDivMulPred k
  have hrest_nonneg (k : Set.Ici 2) : 0 ≤ rest k := by grind
  have hrest_le (k : Set.Ici 2) : rest k ≤ oddLogDivMulPred k := by
    by_cases h : k = k4
    · subst k
      simpa [rest] using hodd_nonneg k4
    · simp [rest, h]
  have hrest_summable : Summable rest :=
    Summable.of_nonneg_of_le hrest_nonneg hrest_le summable_oddLogDivMulPred_nat_tail
  have hleRest : ∑' p : P, log p / (p * (p - 1)) ≤ ∑' k : Set.Ici 2, rest k :=
    Summable.tsum_le_tsum_of_inj e heinj (fun c _hc ↦ hrest_nonneg c)
      (fun p ↦ by simpa [rest, hek4 p] using Std.le_of_eq (hterm p))
      (summable_primeLogDivMulPred.subtype fun q ↦ 5 ≤ (q : ℕ)) hrest_summable
  have hk4_pos : 0 < oddLogDivMulPred ((k4 : ℕ) : ℝ) := by
    have hlog : 0 < log 9 := log_pos (by norm_num)
    grind [oddLogDivMulPred]
  rw [summable_oddLogDivMulPred_nat_tail.tsum_eq_add_tsum_ite k4]
  exact lt_of_le_of_lt hleRest (by linarith)

lemma oddLogDivMulPred_strictAntiOn : StrictAntiOn oddLogDivMulPred (Set.Ici 2) := by
  intro x hx y hy hxy
  have : 2 ≤ x := hx
  have hxarg : exp 1 ≤ 2 * x + 1 := by linarith [exp_one_lt_three]
  have hyarg : exp 1 ≤ 2 * y + 1 := by linarith [exp_one_lt_three]
  have hlogdiv : log (2 * y + 1) / (2 * y + 1) ≤ log (2 * x + 1) / (2 * x + 1) :=
    log_div_self_antitoneOn hxarg hyarg (by linarith)
  have hright_pos : 0 < log (2 * x + 1) / (2 * x + 1) :=
    div_pos (log_pos (by linarith)) (by linarith)
  have hleft2_nonneg : 0 ≤ (2 * y)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ = (log (2 * y + 1) / (2 * y + 1)) * (2 * y)⁻¹ := by simp [oddLogDivMulPred, field]
    _ < (log (2 * x + 1) / (2 * x + 1)) * (2 * x)⁻¹ :=
      mul_lt_mul' hlogdiv (by gcongr) hleft2_nonneg hright_pos
    _ = oddLogDivMulPred x := by simp [oddLogDivMulPred, field]

lemma oddLogDivMulPred_three_lt_integral_two_three :
    oddLogDivMulPred 3 < ∫ x in 2..3, oddLogDivMulPred x := by
  let c : ℝ → ℝ := fun _ ↦ oddLogDivMulPred 3
  have hconst_int : (∫ x in 2..3, c x) = oddLogDivMulPred 3 := by norm_num [c]
  rw [← hconst_int]
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num) continuousOn_const ?_ ?_ ?_
  · refine ContinuousOn.div ?_ ?_ ?_
    · refine ((continuous_const.mul continuous_id).add continuous_const).continuousOn.log ?_
      intro x hx
      have hpos : 0 < 2 * x + 1 := by linarith [hx.1]
      exact hpos.ne'
    · exact (((continuous_const.mul continuous_id).add continuous_const).mul
        (continuous_const.mul continuous_id)).continuousOn
    · grind [mul_eq_zero, OfNat.ofNat_ne_zero]
  · intro x hx
    exact oddLogDivMulPred_strictAntiOn.antitoneOn hx.1.le (by norm_num) hx.2
  · refine ⟨2, by norm_num, ?_⟩
    exact oddLogDivMulPred_strictAntiOn (by norm_num) (by norm_num) (by norm_num)

lemma tsum_oddLogDivMulPred_nat_tail_lt_integral : ∑' n : ℕ, oddLogDivMulPred (n + 3 : ℕ)
    < ∫ x in Set.Ioi 2, oddLogDivMulPred x := by
  have hpartial (n : ℕ) : ∑ i ∈ range n, oddLogDivMulPred (i + 3 : ℕ)
    ≤ oddLogDivMulPred 3 + ∫ x in Set.Ioi 3, oddLogDivMulPred x := by
    rcases n with rfl | m
    · rw [sum_range_zero]
      refine add_nonneg (oddLogDivMulPred_nonneg (by norm_num)) ?_
      refine setIntegral_nonneg measurableSet_Ioi fun x hx ↦ ?_
      exact oddLogDivMulPred_nonneg (by grind)
    · calc
        _ = oddLogDivMulPred 3 + ∑ i ∈ range m, oddLogDivMulPred ((i + 4 : ℕ) : ℝ) := by
          rw [sum_range_succ']
          simp [Nat.add_assoc, add_comm]
        _ ≤ oddLogDivMulPred 3 + ∫ x in 3..((m + 3 : ℕ) : ℝ), oddLogDivMulPred x := by
          refine add_le_add_right ?_ (oddLogDivMulPred 3)
          rw [range_eq_Ico, sum_Ico_add' (fun j ↦ oddLogDivMulPred (j + 1 : ℕ)) 0 m 3]
          refine AntitoneOn.sum_le_integral_Ico (by lia) ?_
          exact oddLogDivMulPred_strictAntiOn.antitoneOn.mono fun x hx ↦ le_trans (by norm_num) hx.1
        _ ≤ _ := by
          have : (∫ x in 3..(m + 3 : ℕ), oddLogDivMulPred x)
              + ∫ x in Set.Ioi ((m + 3 : ℕ) : ℝ), oddLogDivMulPred x =
              ∫ x in Set.Ioi 3, oddLogDivMulPred x :=
            intervalIntegral.integral_interval_add_Ioi
              (integral_oddLogDivMulPred_converges.mono_set (by grind))
              (integral_oddLogDivMulPred_converges.mono_set (by grind))
          have : 0 ≤ ∫ x in Set.Ioi (((m + 3 : ℕ) : ℝ)), oddLogDivMulPred x :=
            setIntegral_nonneg measurableSet_Ioi fun x hx ↦ oddLogDivMulPred_nonneg (by grind)
          linarith
  calc
  _ ≤ oddLogDivMulPred 3 + ∫ x in Set.Ioi 3, oddLogDivMulPred x :=
    tsum_le_of_sum_range_le (fun n ↦ oddLogDivMulPred_nonneg (by grind)) hpartial
  _ < (∫ x in 2..3, oddLogDivMulPred x) + ∫ x in Set.Ioi 3, oddLogDivMulPred x :=
    add_lt_add_left oddLogDivMulPred_three_lt_integral_two_three _
  _ = _ :=
    intervalIntegral.integral_interval_add_Ioi integral_oddLogDivMulPred_converges
      (integral_oddLogDivMulPred_converges.mono_set (by grind))

lemma half_integral_log_div_mul_pred_le : 1 / 2 * ∫ u in Set.Ioi 5, log u / (u * (u - 1))
    ≤ 5 / 8 * ∫ u in Set.Ioi 5, log u / u ^ 2 := by
  have hbound_int : IntegrableOn (fun u ↦ 5 / 4 * (log u / u ^ 2)) (Set.Ioi 5) := by
    refine (integrableOn_Ioi_deriv_of_nonneg' hasDerivAt_neg_log_add_one_div ?_
      tendsto_neg_log_add_one_div_atTop).const_mul (5 / 4)
    exact fun u hu ↦ div_nonneg (log_nonneg (by grind)) (sq_nonneg u)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioi 5) : log u / (u * (u - 1)) ≤ 5 / 4 * (log u / u ^ 2) := by
    have hu5 : 5 < u := hu
    calc
      log u / (u * (u - 1)) = log u * (1 / (u * (u - 1))) := by rw [div_eq_mul_one_div]
      _ ≤ log u * (5 / (4 * u ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by bound)
        rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
        nlinarith
      _ = 5 / 4 * (log u / u ^ 2) := by field_simp
  have hpred_int : IntegrableOn (fun u ↦ log u / (u * (u - 1))) (Set.Ioi 5) := by
    refine Integrable.mono_nonneg hbound_int.integrable ?_ ?_ ?_
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun _ _ ↦ ?_
      exact div_nonneg (by grind [log_nonneg]) (by grind [mul_nonneg])
    · exact (ae_restrict_mem measurableSet_Ioi).mono hpoint
  have hmono : ∫ u in Set.Ioi 5, log u / (u * (u - 1))
      ≤ ∫ u in Set.Ioi 5, 5 / 4 * (log u / u ^ 2) :=
    setIntegral_mono_on hpred_int hbound_int measurableSet_Ioi hpoint
  convert mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1
  rw [integral_const_mul]
  ring

lemma integral_oddLogDivMulPred_le_log_five_add_one_div_eight :
    ∫ x in Set.Ioi 2, oddLogDivMulPred x ≤ (log 5 + 1) / 8 := by
  set g := fun u ↦ log u / (u * (u - 1)) with hg
  calc
    _ = ∫ x in Set.Ioi 2, g (2 * x + 1) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by simp [oddLogDivMulPred, hg]
    _ = (2 : ℝ)⁻¹ * ∫ y in Set.Ioi (2 * 2), g (y + 1) :=
      integral_comp_mul_left_Ioi (fun y ↦ g (y + 1)) 2 (by norm_num)
    _ = (1 / 2) * ∫ y in Set.Ioi 4, g (y + 1) := by norm_num
    _ = (1 / 2) * ∫ u in Set.Ioi 5, g u := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
        ← show (4 : ℝ) + 1 = 5 by norm_num,
        ← integral_add_right_eq_self (fun u ↦ Set.indicator (Set.Ioi (4 + 1)) g u) 1]
      congr 2; ext y
      by_cases hy : 4 < y
      <;> simp [Set.mem_Ioi, hy]
    _ = 1 / 2 * ∫ u in Set.Ioi 5, log u / (u * (u - 1)) := by rw [hg]
    _ ≤ 5 / 8 * ∫ u in Set.Ioi 5, log u / u ^ 2 := half_integral_log_div_mul_pred_le
    _ ≤ _ := by
      have : ∀ u ∈ Set.Ioi 5, 0 ≤ log u / u ^ 2 :=
        fun u hu ↦ div_nonneg (log_nonneg (by grind)) (sq_nonneg u)
      have : ∫ u in Set.Ioi 5, log u / u ^ 2 = (log 5 + 1) / 5 := by
        simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hasDerivAt_neg_log_add_one_div this
          tendsto_neg_log_add_one_div_atTop
      simp [this, field]

lemma odd_tail_lt_seven_log_five_add_five_div_forty :
    ∑' k : Set.Ici 2, oddLogDivMulPred k < (7 * log 5 + 5) / 40 := by
  have htail : ∑' k : Set.Ici 2, oddLogDivMulPred k
      < log 5 / 20 + ∫ x in Set.Ioi 2, oddLogDivMulPred x := by
    let K := Set.Ici 2
    let e : ℕ ≃ K :=
      { toFun n := ⟨n + 2, by grind⟩
        invFun k := k - 2
        left_inv n := Nat.add_sub_cancel n 2
        right_inv k := by ext; exact Nat.sub_add_cancel k.property }
    have hsummable_shift : Summable ((fun k : K ↦ oddLogDivMulPred k) ∘ e) :=
      (e.summable_iff).mpr summable_oddLogDivMulPred_nat_tail
    calc
      _ = ∑' n : ℕ, ((fun k : K ↦ oddLogDivMulPred k) ∘ e) n :=
        (e.tsum_eq (fun k ↦ oddLogDivMulPred k)).symm
      _ = oddLogDivMulPred 2 + ∑' n : ℕ, oddLogDivMulPred ((n + 3 : ℕ) : ℝ) := by
        simpa [Function.comp, e, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hsummable_shift.tsum_eq_zero_add
      _ < oddLogDivMulPred 2 + ∫ x in Set.Ioi 2, oddLogDivMulPred x := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_lt_add_left tsum_oddLogDivMulPred_nat_tail_lt_integral (oddLogDivMulPred 2)
      _ = _ := by norm_num [oddLogDivMulPred]
  linarith [integral_oddLogDivMulPred_le_log_five_add_one_div_eight]

lemma log_factorial_eq_sum_prime_factorization {n : ℕ} : log (n.factorial) =
    ∑ p ∈ Ioc 0 n with p.Prime, (Nat.factorization n.factorial p) * log p := by
  rw [log_nat_eq_sum_factorization n.factorial, n.factorial.factorization.sum_of_support_subset]
  · intro p hp
    rw [mem_filter, mem_Ioc]
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ n.factorial := Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hp)
    exact ⟨⟨hpPrime.pos, (Nat.Prime.dvd_factorial hpPrime).mp hpDvd⟩, hpPrime⟩
  · simp

lemma factorial_prime_exponent_lower {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    (n : ℝ) / p - 1 < Nat.factorization n.factorial p := calc
  _ < ((n / p : ℕ) : ℝ) := by
    have hdiv_lt : (n : ℝ) / p < (n / p : ℕ) + 1 := by
      simpa [Nat.floor_div_natCast] using Nat.lt_floor_add_one ((n : ℝ) / p)
    linarith
  _ ≤ _ := by
    norm_cast
    have hmem : 1 ∈ Ico 1 n.succ := by
      rw [mem_Ico]
      exact ⟨le_rfl, Nat.lt_succ_of_le (le_trans hp.one_le hpn)⟩
    simpa [Nat.factorization_factorial hp <| Nat.lt_succ_of_le <| p.log_le_self n]
      using (single_le_sum (fun k _ ↦ Nat.zero_le (n / p ^ k)) hmem)

lemma primeLogSum_sub_log_lt_theta_div {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ Ioc 0 n with p.Prime, log p / p - log n ≤ Chebyshev.theta n / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (by lia : n ≠ 0)
  have hlt : n * (∑ p ∈ Ioc 0 n with p.Prime, log p / p) - Chebyshev.theta n ≤ n * log n := by
    calc
      _ = ∑ p ∈ Ioc 0 n with p.Prime, (n / p - 1) * log p := by
        simp only [Chebyshev.theta, Nat.floor_natCast, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun p hp ↦ by field_simp
      _ ≤ ∑ p ∈ Ioc 0 n with p.Prime, (Nat.factorization n.factorial p) * log p := by
        refine sum_le_sum fun p hp ↦ ?_
        rw [mem_filter, mem_Ioc] at hp
        exact mul_le_mul_of_nonneg_right (le_of_lt (factorial_prime_exponent_lower hp.2 hp.1.2))
          (log_natCast_nonneg p)
      _ = _ := by rw [log_factorial_eq_sum_prime_factorization]
      _ ≤ log (n ^ n) := log_le_log (by positivity) (by exact_mod_cast n.factorial_le_pow)
      _ = n * log n := by rw [log_pow]
  rw [le_div_iff₀ hnpos]
  linarith

lemma factorial_prime_exponent_upper_split {n p : ℕ} (hp : p.Prime) :
    (Nat.factorization n.factorial p : ℝ) ≤ n / p + n / (p * (p - 1)) := by
  calc
    (Nat.factorization n.factorial p : ℝ) ≤ (n / (p - 1) : ℕ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hp n
    _ ≤ n / (p - 1 : ℕ) := Nat.cast_div_le
    _ = n / (p - 1) := by norm_num [Nat.cast_sub hp.one_le]
    _ = n / p + n / (p * (p - 1)) := by
      have hpgt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hpred0 : (p : ℝ) - 1 ≠ 0 := by linarith
      simp [field]

lemma log_factorial_le_mul_primeLogSum_add_error {n : ℕ} : log (n.factorial) ≤
    n * ∑ p ∈ Ioc 0 n with p.Prime, log p / p +
    n * ∑ p ∈ Ioc 0 n with p.Prime, log p / (p * (p - 1)) := by
  rw [log_factorial_eq_sum_prime_factorization]
  calc
    _ ≤ ∑ p ∈ Ioc 0 n with p.Prime, (n / p + n / (p * (p - 1))) * log p := by
      refine sum_le_sum fun p hp ↦ ?_
      rw [mem_filter] at hp
      gcongr
      exact factorial_prime_exponent_upper_split hp.2
    _ = (n : ℝ) * (∑ p ∈ Iic n with p.Prime, log p / p) +
        (n : ℝ) * ∑ p ∈ Iic n with p.Prime, log p / (p * (p - 1)) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun p hp ↦ by field_simp

lemma finite_primeLogDivMulPred_lt_one {n : ℕ} :
    ∑ p ∈ Ioc 0 n with p.Prime, log p / (p * (p - 1)) < 1 := by
  let s : Finset Nat.Primes := ((Ioc 0 n).filter Nat.Prime).attach.map
    ⟨fun p ↦ ⟨p.1, (mem_filter.mp p.2).2⟩, by
      exact fun p q hpq ↦ Subtype.ext (congrArg (fun p : Nat.Primes ↦ (p : ℕ)) hpq)⟩
  calc
    _ = ∑ p ∈ s, log p / (p * (p - 1)) := by
      rw [sum_map]
      exact (Finset.sum_attach ((Ioc 0 n).filter Nat.Prime) fun p ↦ log p / (p * (p - 1))).symm
    _ ≤ ∑' p : Nat.Primes, log p / (p * (p - 1)) := by
      refine summable_primeLogDivMulPred.sum_le_tsum s fun p _ ↦
      have hp1 : 1 < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.one_lt
      div_nonneg (log_natCast_nonneg (p : ℕ)) (by positivity)
    _ < _ := by
      rw [tsum_primeLogDivMulPred_split_two_three]
      linarith [log_two_lt_d9, log_three_lt_d9, prime_tail_lt_odd_tail,
        odd_tail_lt_seven_log_five_add_five_div_forty, log_five_lt_d9]

/-- **Mertens' first theorem**: for every natural number `n`, the sum of `log p / p` over
primes `p ≤ n` differs from `log n` by at most `2`. -/
theorem mertens_first_theorem_nat {n : ℕ} :
    |∑ p ∈ Ioc 0 n with p.Prime, log p / p - log n| < 2 := by
  by_cases hn : n = 0
  · simp_all
  have hn : n ≥ 1 := by lia
  rw [abs_lt]
  constructor
  · have hfactorial_lower : n * log n - n < log (n.factorial) := by
      have hn0 : n ≠ 0 := by lia
      have : 0 < log (2 * π) := log_pos (by nlinarith [pi_gt_three])
      linarith [log_natCast_nonneg n, Stirling.le_log_factorial_stirling hn0]
    have hnpos : (0 : ℝ) < n := by norm_cast
    nlinarith [mul_lt_mul_of_pos_left (finite_primeLogDivMulPred_lt_one (n := n)) hnpos,
      log_factorial_le_mul_primeLogSum_add_error (n := n), hfactorial_lower]
  · calc
      _ ≤ Chebyshev.theta n / n := primeLogSum_sub_log_lt_theta_div hn
      _ ≤ log 4 := by
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (by lia)
        simpa [div_le_iff₀ hnpos, mul_comm] using Chebyshev.theta_le_log4_mul_x (by positivity)
      _ < _ := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num)]
        linarith [log_two_lt_d9]

end Mertens

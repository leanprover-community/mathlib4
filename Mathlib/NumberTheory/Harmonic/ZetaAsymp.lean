/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Asymptotics of `ζ s` as `s → 1`

The goal of this file is to evaluate the limit of `ζ s - 1 / (s - 1)` as `s → 1`.

### Main results

* `tendsto_riemannZeta_sub_one_div`: the limit of `ζ s - 1 / (s - 1)`, at the filter of punctured
  neighbourhoods of 1 in `ℂ`, exists and is equal to the Euler-Mascheroni constant `γ`.
* `riemannZeta_one_ne_zero`: with our definition of `ζ 1` (which is characterised as the limit of
  `ζ s - 1 / (s - 1) / Gammaℝ s` as `s → 1`), we have `ζ 1 ≠ 0`.

### Outline of arguments

We consider the sum `F s = ∑' n : ℕ, f (n + 1) s`, where `s` is a real variable and
`f n s = ∫ x in n..(n + 1), (x - n) / x ^ (s + 1)`. We show that `F s` is continuous on `[1, ∞)`,
that `F 1 = 1 - γ`, and that `F s = 1 / (s - 1) - ζ s / s` for `1 < s`.

By combining these formulae, one deduces that the limit of `ζ s - 1 / (s - 1)` at `𝓝[>] (1 : ℝ)`
exists and is equal to `γ`. Finally, using this and the Riemann removable singularity criterion
we obtain the limit along punctured neighbourhoods of 1 in `ℂ`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

@[inherit_doc] local notation "γ" => eulerMascheroniConstant

namespace ZetaAsymptotics
-- since the intermediate lemmas are of little interest in themselves we put them in a namespace

/-!
## Definitions
-/

/-- Auxiliary function used in studying zeta-function asymptotics. -/
noncomputable def term (n : ℕ) (s : ℝ) : ℝ := ∫ x : ℝ in n..(n + 1), (x - n) / x ^ (s + 1)

/-- Sum of finitely many `term`s. -/
noncomputable def term_sum (s : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, term (n + 1) s

/-- Topological sum of `term`s. -/
noncomputable def term_tsum (s : ℝ) : ℝ := ∑' n, term (n + 1) s

lemma term_nonneg (n : ℕ) (s : ℝ) : 0 ≤ term n s := by
  rw [term, intervalIntegral.integral_of_le (by simp)]
  refine setIntegral_nonneg measurableSet_Ioc (fun x hx ↦ ?_)
  refine div_nonneg ?_ (rpow_nonneg ?_ _)
  all_goals linarith [hx.1]

lemma term_welldef {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun x : ℝ ↦ (x - n) / x ^ (s + 1)) volume n (n + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  refine (continuousOn_of_forall_continuousAt fun x hx ↦ ContinuousAt.div ?_ ?_ ?_).integrableOn_Icc
  · fun_prop
  · apply continuousAt_id.rpow_const (Or.inr <| by linarith)
  · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr hn).trans_le hx.1) _).ne'

section s_eq_one

/-!
## Evaluation of the sum for `s = 1`
-/

lemma term_one {n : ℕ} (hn : 0 < n) :
    term n 1 = (log (n + 1) - log n) - 1 / (n + 1) := by
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right, zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n 1
    _ = ∫ x : ℝ in n..(n + 1), (x - n) / x ^ 2 := by
      simp_rw [term, one_add_one_eq_two, ← Nat.cast_two (R := ℝ), rpow_natCast]
    _ = ∫ x : ℝ in n..(n + 1), (1 / x - n / x ^ 2) :=
      intervalIntegral.integral_congr (fun x hx ↦ by field)
    _ = (∫ x : ℝ in n..(n + 1), 1 / x) - n * ∫ x : ℝ in n..(n + 1), 1 / x ^ 2 := by
      simp_rw [← mul_one_div (n : ℝ)]
      rw [intervalIntegral.integral_sub]
      · simp_rw [intervalIntegral.integral_const_mul]
      · exact intervalIntegral.intervalIntegrable_one_div (fun x hx ↦ (hv x hx).ne') (by fun_prop)
      · exact (intervalIntegral.intervalIntegrable_one_div
          (fun x hx ↦ (sq_pos_of_pos (hv x hx)).ne') (by fun_prop)).const_mul _
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : ℝ in n..(n + 1), 1 / x ^ 2 := by
      congr 1
      rw [integral_one_div_of_pos, log_div]
      all_goals positivity
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : ℝ in n..(n + 1), x ^ (-2 : ℝ) := by
      congr 2
      refine intervalIntegral.integral_congr (fun x hx ↦ ?_)
      rw [rpow_neg, one_div, ← Nat.cast_two (R := ℝ), rpow_natCast]
      exact (hv x hx).le
    _ = log (↑n + 1) - log ↑n - n * (1 / n - 1 / (n + 1)) := by
      rw [integral_rpow]
      · simp_rw [sub_div, (by norm_num : (-2 : ℝ) + 1 = -1), div_neg, div_one, neg_sub_neg,
          rpow_neg_one, ← one_div]
      · refine Or.inr ⟨by simp, notMem_uIcc_of_lt ?_ ?_⟩
        all_goals positivity
    _ = log (↑n + 1) - log ↑n - 1 / (↑n + 1) := by
      congr 1
      simp [field]

lemma term_sum_one (N : ℕ) : term_sum 1 N = log (N + 1) - harmonic (N + 1) + 1 := by
  induction N with
  | zero =>
    simp_rw [term_sum, Finset.sum_range_zero, harmonic_succ, harmonic_zero,
      Nat.cast_zero, zero_add, Nat.cast_one, inv_one, Rat.cast_one, log_one, sub_add_cancel]
  | succ N hN =>
    unfold term_sum at hN ⊢
    rw [Finset.sum_range_succ, hN, harmonic_succ (N + 1),
      term_one (by positivity : 0 < N + 1)]
    push_cast
    ring_nf

/-- The topological sum of `ZetaAsymptotics.term (n + 1) 1` over all `n : ℕ` is `1 - γ`. This is
proved by directly evaluating the sum of the first `N` terms and using the limit definition of `γ`.
-/
lemma term_tsum_one : HasSum (fun n ↦ term (n + 1) 1) (1 - γ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ term_nonneg (n + 1) 1)]
  change Tendsto (fun N ↦ term_sum 1 N) atTop _
  simp_rw [term_sum_one, sub_eq_neg_add]
  refine Tendsto.add ?_ tendsto_const_nhds
  have := (tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).neg
  refine this.congr' (Eventually.of_forall (fun n ↦ ?_))
  simp_rw [Function.comp_apply, eulerMascheroniSeq', reduceCtorEq, if_false]
  push_cast
  abel

end s_eq_one

section s_gt_one

/-!
## Evaluation of the sum for `1 < s`
-/

lemma term_of_lt {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 1 < s) :
    term n s = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
    - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right, zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n s
    _ = ∫ x : ℝ in n..(n + 1), (x - n) / x ^ (s + 1) := by rfl
    _ = ∫ x : ℝ in n..(n + 1), (x ^ (-s) - n * x ^ (-(s + 1))) := by
      refine intervalIntegral.integral_congr (fun x hx ↦ ?_)
      rw [sub_div, rpow_add_one (hv x hx).ne', mul_comm, ← div_div, div_self (hv x hx).ne',
        rpow_neg (hv x hx).le, rpow_neg (hv x hx).le, one_div, rpow_add_one (hv x hx).ne', mul_comm,
        div_eq_mul_inv]
    _ = (∫ x : ℝ in n..(n + 1), x ^ (-s)) - n * (∫ x : ℝ in n..(n + 1), x ^ (-(s + 1))) := by
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul] <;>
      [skip; apply IntervalIntegrable.const_mul] <;>
      · refine intervalIntegral.intervalIntegrable_rpow (Or.inr <| notMem_uIcc_of_lt ?_ ?_)
        · exact_mod_cast hn
        · linarith
    _ = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
          - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
      have : 0 ∉ uIcc (n : ℝ) (n + 1) := (lt_irrefl _ <| hv _ ·)
      rw [integral_rpow (Or.inr ⟨by linarith, this⟩), integral_rpow (Or.inr ⟨by linarith, this⟩)]
      congr 1
      · rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, mul_comm, mul_one_div, neg_sub,
          rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]
      · rw [show -(s + 1) + 1 = -s by ring, div_neg, ← neg_div, neg_sub, div_mul_eq_mul_div,
          mul_div_assoc, rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]

lemma term_sum_of_lt (N : ℕ) {s : ℝ} (hs : 1 < s) :
    term_sum s N = 1 / (s - 1) * (1 - 1 / (N + 1) ^ (s - 1))
    - 1 / s * ((∑ n ∈ Finset.range N, 1 / (n + 1 : ℝ) ^ s) - N / (N + 1) ^ s) := by
  simp only [term_sum]
  conv => enter [1, 2, n]; rw [term_of_lt (by simp) hs]
  rw [Finset.sum_sub_distrib]
  congr 1
  · induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ, hN, Nat.cast_add_one]
      ring_nf
  · simp_rw [mul_comm (_ / _), ← mul_div_assoc, div_eq_mul_inv _ s, ← Finset.sum_mul, mul_one]
    congr 1
    induction N with
    | zero => simp
    | succ N hN =>
      simp_rw [Finset.sum_range_succ, hN, Nat.cast_add_one, sub_eq_add_neg, add_assoc]
      congr 1
      ring_nf

/-- For `1 < s`, the topological sum of `ZetaAsymptotics.term (n + 1) s` over all `n : ℕ` is
`1 / (s - 1) - ζ s / s`.
-/
lemma term_tsum_of_lt {s : ℝ} (hs : 1 < s) :
    term_tsum s = (1 / (s - 1) - 1 / s * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) := by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ term_nonneg (n + 1) s)]
  change Tendsto (fun N ↦ term_sum s N) atTop _
  simp_rw [term_sum_of_lt _ hs]
  apply Tendsto.sub
  · rw [show 𝓝 (1 / (s - 1)) = 𝓝 (1 / (s - 1) - 1 / (s - 1) * 0) by simp]
    simp_rw [mul_sub, mul_one]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ ?_)
    refine tendsto_const_nhds.div_atTop <| (tendsto_rpow_atTop (by linarith)).comp ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · rw [← sub_zero (tsum _)]
    apply (((Summable.hasSum ?_).tendsto_sum_nat).sub ?_).const_mul
    · exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_rpow.mpr hs)
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      · change Tendsto (fun n : ℕ ↦ (1 / ↑(n + 1) : ℝ) ^ (s - 1)) ..
        rw [show 𝓝 (0 : ℝ) = 𝓝 (0 ^ (s - 1)) by rw [zero_rpow]; linarith]
        refine Tendsto.rpow_const ?_ (Or.inr <| by linarith)
        exact (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_add_atTop_nat _)
      · intro n
        positivity
      · intro n
        dsimp only
        transitivity (n + 1) / (n + 1) ^ s
        · gcongr
          linarith
        · apply le_of_eq
          rw [rpow_sub_one, ← div_mul, div_one, mul_comm, one_div, inv_rpow, ← div_eq_mul_inv]
          · norm_cast
          all_goals positivity

/-- Reformulation of `ZetaAsymptotics.term_tsum_of_lt` which is useful for some computations
below. -/
lemma zeta_limit_aux1 {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1) = 1 - s * term_tsum s := by
  rw [term_tsum_of_lt hs]
  generalize (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) = Z
  field [(show s - 1 ≠ 0 by linarith)]

end s_gt_one

section continuity

/-!
## Continuity of the sum
-/

lemma continuousOn_term (n : ℕ) :
    ContinuousOn (fun x ↦ term (n + 1) x) (Ici 1) := by
  -- TODO: can this be shortened using the lemma
  -- `continuous_parametric_intervalIntegral_of_continuous'` from https://github.com/leanprover-community/mathlib4/pull/11185?
  simp only [term, intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : ℝ) ≤ ↑(n + 1) + 1)]
  apply continuousOn_of_dominated (bound := fun x ↦ (x - ↑(n + 1)) / x ^ (2 : ℝ))
  · exact fun s hs ↦ (term_welldef (by simp) (zero_lt_one.trans_le hs)).1.1
  · intro s (hs : 1 ≤ s)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have : 1 < x := lt_of_le_of_lt (by simp) hx.1
    rw [norm_of_nonneg (div_nonneg (sub_nonneg.mpr hx.1.le) (by positivity)), Nat.cast_add_one]
    gcongr
    · exact_mod_cast sub_nonneg.mpr hx.1.le
    · exact this.le
    · linarith
  · rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact_mod_cast term_welldef (by lia : 0 < (n + 1)) zero_lt_one
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    refine continuousOn_of_forall_continuousAt (fun s (hs : 1 ≤ s) ↦ continuousAt_const.div ?_ ?_)
    · exact continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inr (by linarith))
    · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr (by simp)).trans hx.1) _).ne'

lemma continuousOn_term_tsum : ContinuousOn term_tsum (Ici 1) := by
  -- We use dominated convergence, using `fun n ↦ term n 1` as our uniform bound (since `term` is
  -- monotone decreasing in `s`.)
  refine continuousOn_tsum (fun i ↦ continuousOn_term _) term_tsum_one.summable (fun n s hs ↦ ?_)
  rw [term, term, norm_of_nonneg]
  · simp_rw [intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : ℝ) ≤ ↑(n + 1) + 1)]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x hx ↦ ?_)
    · exact (term_welldef n.succ_pos (zero_lt_one.trans_le hs)).1
    · exact (term_welldef n.succ_pos zero_lt_one).1
    · have : 1 ≤ x := le_trans (by simp) hx.1.le
      gcongr
      · exact sub_nonneg.mpr hx.1.le
      · exact hs
  · rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_nonneg measurableSet_Ioc (fun x hx ↦ div_nonneg ?_ (rpow_nonneg ?_ _))
    all_goals linarith [hx.1]

/-- First version of the limit formula, with a limit over real numbers tending to 1 from above. -/
lemma tendsto_riemannZeta_sub_one_div_nhds_right :
    Tendsto (fun s : ℝ ↦ riemannZeta s - 1 / (s - 1)) (𝓝[>] 1) (𝓝 γ) := by
  suffices Tendsto (fun s : ℝ ↦ (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 γ) by
    apply ((Complex.continuous_ofReal.tendsto _).comp this).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, sub_left_inj, Complex.ofReal_tsum]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    congr 1 with n
    rw [Complex.ofReal_cpow (by positivity)]
    norm_cast
  suffices aux2 : Tendsto (fun s : ℝ ↦ (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 (1 - term_tsum 1)) by
    have := term_tsum_one.tsum_eq
    rw [← term_tsum, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at this
    simpa only [this] using aux2
  apply Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with s hs using (zeta_limit_aux1 hs).symm
  · apply tendsto_const_nhds.sub
    rw [← one_mul (term_tsum 1)]
    apply (tendsto_id.mono_left nhdsWithin_le_nhds).mul
    have := continuousOn_term_tsum.continuousWithinAt self_mem_Ici
    exact Tendsto.mono_left this (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- The function `ζ s - 1 / (s - 1)` tends to `γ` as `s → 1`. -/
theorem _root_.tendsto_riemannZeta_sub_one_div :
    Tendsto (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) (𝓝[≠] 1) (𝓝 γ) := by
  -- We use the removable-singularity theorem to show that *some* limit over `𝓝[≠] (1 : ℂ)` exists,
  -- and then use the previous result to deduce that this limit must be `γ`.
  let f (s : ℂ) := riemannZeta s - 1 / (s - 1)
  suffices ∃ C, Tendsto f (𝓝[≠] 1) (𝓝 C) by
    obtain ⟨C, hC⟩ := this
    suffices Tendsto (fun s : ℝ ↦ f s) _ _
      from (tendsto_nhds_unique this tendsto_riemannZeta_sub_one_div_nhds_right) ▸ hC
    refine hC.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds ..)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      rw [mem_compl_singleton_iff, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
      exact ne_of_gt ha
  refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (differentiableAt_riemannZeta hs).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · rwa [mem_compl_singleton_iff, ← sub_ne_zero] at hs
  · refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ht'
      rw [inv_eq_zero, sub_eq_zero] at ht'
      tauto
    · simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
        (by ring_nf : 𝓝 (0 : ℂ) = 𝓝 ((1 - 1) - f 1 * (1 - 1)))]
      apply Tendsto.sub
      · simp_rw [mul_comm (f _), f, mul_sub]
        apply riemannZeta_residue_one.sub
        refine Tendsto.congr' ?_ (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with x hx
        field [sub_ne_zero.mpr <| mem_compl_singleton_iff.mp hx]
      · exact ((tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).const_mul _

lemma _root_.isBigO_riemannZeta_sub_one_div {F : Type*} [Norm F] [One F] [NormOneClass F] :
    (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) =O[𝓝 1] (fun _ ↦ 1 : ℂ → F) := by
  simpa only [Asymptotics.isBigO_one_nhds_ne_iff] using
     tendsto_riemannZeta_sub_one_div.isBigO_one (F := F)

end continuity

section val_at_one

open Complex

lemma tendsto_Gamma_term_aux : Tendsto (fun s ↦ 1 / (s - 1) - 1 / Gammaℝ s / (s - 1)) (𝓝[≠] 1)
    (𝓝 (-(γ + Complex.log (4 * ↑π)) / 2)) := by
  have h := hasDerivAt_Gammaℝ_one
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, Gammaℝ_one] at h
  have := h.div (hasDerivAt_Gammaℝ_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Gammaℝ_one.trans_ne one_ne_zero)
  rw [Gammaℝ_one, div_one] at this
  refine this.congr' ?_
  have : {z | 0 < re z} ∈ 𝓝 (1 : ℂ) := by
    apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    simp only [mem_preimage, one_re, mem_Ioi, zero_lt_one]
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [this] with a ha _
  rw [Pi.div_apply, ← sub_div, div_right_comm, sub_div' (Gammaℝ_ne_zero_of_re_pos ha), one_mul]

lemma tendsto_riemannZeta_sub_one_div_Gammaℝ :
    Tendsto (fun s ↦ riemannZeta s - 1 / Gammaℝ s / (s - 1)) (𝓝[≠] 1)
    (𝓝 ((γ - Complex.log (4 * ↑π)) / 2)) := by
  have := tendsto_riemannZeta_sub_one_div.add tendsto_Gamma_term_aux
  simp_rw [sub_add_sub_cancel] at this
  convert this using 2
  ring_nf

/-- Formula for `ζ 1`. Note that mathematically `ζ 1` is undefined, but our construction ascribes
this particular value to it. -/
lemma _root_.riemannZeta_one : riemannZeta 1 = (γ - Complex.log (4 * ↑π)) / 2 := by
  have := (HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one 0).mono_left
    <| nhdsWithin_le_nhds (s := {1}ᶜ)
  simp only [HurwitzZeta.hurwitzZetaEven_zero, div_right_comm _ _ (Gammaℝ _)] at this
  exact tendsto_nhds_unique this tendsto_riemannZeta_sub_one_div_Gammaℝ

/-- Formula for `Λ 1`. Note that mathematically `Λ 1` is undefined, but our construction ascribes
this particular value to it. -/
lemma _root_.completedRiemannZeta_one :
    completedRiemannZeta 1 = (γ - Complex.log (4 * ↑π)) / 2 :=
  (riemannZeta_one ▸ div_one (_ : ℂ) ▸ Gammaℝ_one ▸ riemannZeta_def_of_ne_zero one_ne_zero).symm

/-- Formula for `Λ₀ 1`, where `Λ₀` is the entire function satisfying
`Λ₀ s = π ^ (-s / 2) Γ(s / 2) ζ(s) + 1 / s + 1 / (1 - s)` away from `s = 0, 1`.

Note that `s = 1` is _not_ a pole of `Λ₀`, so this statement (unlike `riemannZeta_one`) is
a mathematically meaningful statement and is not dependent on Mathlib's particular conventions for
division by zero. -/
lemma _root_.completedRiemannZeta₀_one :
    completedRiemannZeta₀ 1 = (γ - Complex.log (4 * ↑π)) / 2 + 1 := by
  have := completedRiemannZeta_eq 1
  rw [sub_self, div_zero, div_one, sub_zero, eq_sub_iff_add_eq] at this
  rw [← this, completedRiemannZeta_one]

/-- With Mathlib's particular conventions, we have `ζ 1 ≠ 0`. -/
lemma _root_.riemannZeta_one_ne_zero : riemannZeta 1 ≠ 0 := by
  -- This one's for you, Kevin.
  suffices (γ - (4 * π).log) / 2 ≠ 0 by
    simpa only [riemannZeta_one, ← ofReal_ne_zero, ofReal_log (by positivity : 0 ≤ 4 * π),
      push_cast]
  refine div_ne_zero (sub_lt_zero.mpr (lt_trans ?_ ?_ (b := 1))).ne two_ne_zero
  · exact Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  · rw [lt_log_iff_exp_lt (by positivity)]
    exact (lt_trans Real.exp_one_lt_d9 (by norm_num)).trans_le
      <| mul_le_mul_of_nonneg_left two_le_pi (by simp)

lemma _root_.riemannZeta_eventually_ne_zero_nhds_one : ∀ᶠ s in 𝓝 1, riemannZeta s ≠ 0 := by
  filter_upwards [eventually_nhdsWithin_iff.1 <| riemannZeta_residue_one.eventually_ne one_ne_zero]
  grind [riemannZeta_one_ne_zero]

end val_at_one

end ZetaAsymptotics

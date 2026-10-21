/-
Copyright (c) 2022 Kexing Ying, 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Pavel Zorin-Kranich
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Doob's martingale maximal inequality

For a non-negative submartingale `f`, the maximal function is defined by
`f* n ω = max_{k ≤ n}, f k ω`

Doob's maximal inequalities provide estimates for superlevel sets and moments
of the maximal function.

### Main results

* `MeasureTheory.maximal_ineq`: Doob's maximal inequality for superlevel sets:
for all `ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n`
* `MeasureTheory.maximal_ineq_Lp`: Doob's maximal inequality for Lp norms:
for all `p > 1`, we have `eLpNorm' (f* n) p μ ≤ (p/(p-1)) * eLpNorm' (f n) p μ`

-/

public section


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {τ π : Ω → WithTop ℕ}

section Maximal

open Finset


def maximal_process (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :=
  (range (n + 1)).sup' nonempty_range_add_one (f · ω)

theorem smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : ℝ≥0}
    (n : ℕ) : ε • μ {ω | (ε : ℝ) ≤ maximal_process f n ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ maximal_process f n ω},
      stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have : ∀ ω, ((ε : ℝ) ≤ maximal_process f n ω) →
      (ε : ℝ) ≤ stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω := by
    intro ω hω
    rw [maximal_process] at hω
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hω
    refine stoppedValue_hittingBtwn_mem (s := {y : ℝ | ε ≤ y}) ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_ofPred_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hω
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ ↦ (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this (Integrable.integrableOn (hsub.integrable_stoppedValue
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (mod_cast hittingBtwn_le)))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.
-/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0}
    (n : ℕ) : ε * μ {ω | (ε : ℝ) ≤ maximal_process f n ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ maximal_process f n ω},
        f n ω ∂μ) := by
  suffices ε • μ {ω | (ε : ℝ) ≤ maximal_process f n ω} +
      ENNReal.ofReal
        (∫ ω in {ω | (maximal_process f n ω) < ε},
          f n ω ∂μ) ≤
      ENNReal.ofReal (μ[f n]) by
    have hadd : ENNReal.ofReal (∫ ω, f n ω ∂μ) =
      ENNReal.ofReal
        (∫ ω in {ω | ε ≤ maximal_process f n ω}, f n ω ∂μ) +
      ENNReal.ofReal
        (∫ ω in {ω | (maximal_process f n ω) < ε},
          f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ]
        convert rfl
        ext ω
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      exacts [(hsub.integrable _).integrableOn, (hsub.integrable _).integrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this
  calc
    _ ≤ ENNReal.ofReal
          (∫ ω in {ω | (ε : ℝ) ≤ maximal_process f n ω},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) +
        ENNReal.ofReal
          (∫ ω in {ω | (maximal_process f n ω) < ε},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      gcongr with ω hω
      · exact smul_le_stoppedValue_hittingBtwn hsub n
      · exact (hsub.integrable n).integrableOn
      · refine Integrable.integrableOn ?_
        refine hsub.integrable_stoppedValue ?_ (mod_cast hittingBtwn_le)
        exact hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
      · exact nullMeasurableSet_lt (measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable aemeasurable_const
      rw [Set.mem_ofPred_eq] at hω
      have : hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω = n := by
        simp only [hittingBtwn, Set.mem_ofPred_eq, ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact False.elim
          ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp only [stoppedValue, this, ge_iff_le]
      refine le_of_eq ?_
      congr
    _ = ENNReal.ofReal
        (∫ ω, stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ (μ := μ)]
        convert rfl
        ext ω
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ)
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (mod_cast hittingBtwn_le))
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (mod_cast hittingBtwn_le))
      exacts [integral_nonneg fun x ↦ hnonneg _ _, integral_nonneg fun x ↦ hnonneg _ _]
    _ ≤ ENNReal.ofReal (μ[f n]) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f n]
      refine hsub.expected_stoppedValue_mono
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (isStoppingTime_const _ _) (fun ω ↦ ?_) (fun _ ↦ le_rfl)
      simp [hittingBtwn_le]

lemma maximal_process_of_nonneg_is_nonneg (hnonneg : 0 ≤ f)
  : maximal_process f ≥ 0 := by
  intro n ω
  calc
  _ ≥ (f · ω) n := by
      rewrite [maximal_process]
      rewrite [ge_iff_le]
      exact (le_sup' (f · ω) (self_mem_range_succ n))
  _ ≥ 0 := (hnonneg n ω)

lemma maximal_process_strongly_adapted (hsa : StronglyAdapted 𝒢 f) (n : ℕ)
  : Measurable[𝒢 n] (maximal_process f n) := by
  let : MeasurableSpace Ω := 𝒢 n
  apply Finset.measurable_range_sup''
  intro k hk
  apply StronglyMeasurable.measurable
  exact StronglyMeasurable.mono (hsa k) (𝒢.mono hk)

private lemma maximal_ineq_Lp_stage0 [IsFiniteMeasure μ]
  (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
  (p : ℝ) (hp : p > 1) (n : ℕ) :
  ∫⁻ ω, ENNReal.ofReal (maximal_process f n ω) ^ p ∂μ ≤
  ENNReal.ofReal (p/(p-1))
  * ∫⁻ ω, ENNReal.ofReal (maximal_process f n ω) ^ (p-1) * ENNReal.ofReal (f n ω) ∂μ
  := by
  let M_n := maximal_process f n
  have M_n_measurable: Measurable (M_n)
  := Measurable.le (𝒢.le' n)
    (maximal_process_strongly_adapted hsub.1 n)
  have M_n_nonneg: 0 ≤ (M_n)
  := maximal_process_of_nonneg_is_nonneg hnonneg n
  have superlevel_set_measurable (t : ℝ) : MeasurableSet {ω | t ≤ M_n ω} := by
    apply (𝒢.le' n)
    exact measurableSet_le measurable_const
      (maximal_process_strongly_adapted hsub.stronglyAdapted n)
  have p_pos : 0 < p := by linarith
  have p_nonneg : 0 ≤ p := le_of_lt p_pos
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (M_n ω  ^ p) ∂μ
    := by
      congr
      funext ω
      apply ENNReal.ofReal_rpow_of_nonneg (M_n_nonneg _) (p_nonneg)
    _ = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
      μ {ω : Ω | t ≤ M_n ω} * ENNReal.ofReal (t ^ (p - 1))
    := lintegral_rpow_eq_lintegral_meas_le_mul
       (f_nn := Filter.Eventually.of_forall M_n_nonneg)
       (f_mble := Measurable.aemeasurable M_n_measurable)
       (p_pos := p_pos)
    _ =
    ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
      (t.toNNReal) * μ {ω : Ω | t ≤ M_n ω} * ENNReal.ofReal (t ^ (p - 2))
    := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have hpow : t ^ (p - 1) = t * t ^ (p - 2) := by
        calc
          t ^ (p - 1) = t ^ (1 + (p - 2)) := by
            congr 1
            ring
          _ = t * t ^ (p - 2) := by
            rw [Real.rpow_add ht, Real.rpow_one]
      rw [hpow, ENNReal.ofReal_mul ht.le]
      ac_rfl
    -- apply superlevel set estimate
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (∫ ω in {ω | t ≤ M_n ω}, f n ω ∂μ)
      * ENNReal.ofReal (t ^ (p - 2))
    := by
      gcongr 1
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      gcongr 1
      rewrite (occs := .pos [2, 3]) [←(Real.coe_toNNReal t ht.le)]
      exact (maximal_ineq hsub hnonneg (ε := t.toNNReal) n)
    -- Use constant measure in nested integral
    _ = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
      (∫⁻ ω, ENNReal.ofReal (Set.indicator {ω | t ≤ M_n ω} (f n) ω)
      * ENNReal.ofReal (t ^ (p - 2)) ∂μ)
    := by
      congr
      funext t
      rw [ofReal_integral_eq_lintegral_ofReal
        (hsub.integrable n).integrableOn
        (Filter.Eventually.of_forall (hnonneg n))]
      rw [←lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      rw [←lintegral_indicator (superlevel_set_measurable t)]
      congr 1
      funext ω
      by_cases h : t ≤ M_n ω <;> simp [h]
    -- Swap order of integration
    _ = ENNReal.ofReal p * ∫⁻ ω,  (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Set.indicator {ω | t ≤ M_n ω} (f n) ω)
      * ENNReal.ofReal (t ^ (p - 2))) ∂μ
    := by
      congr 1
      apply lintegral_lintegral_swap
      -- show measurability required for swapping order of integration
      apply Measurable.aemeasurable
      change Measurable (fun z : ℝ × Ω ↦
        ENNReal.ofReal
          ({z : ℝ × Ω | z.1 ≤ M_n z.2}.indicator
            (fun z ↦ f n z.2) z) *
          ENNReal.ofReal (z.1 ^ (p - 2)))
      have hset : MeasurableSet {z : ℝ × Ω | z.1 ≤ M_n z.2} :=
        measurableSet_le measurable_fst (M_n_measurable.comp measurable_snd)
      have hind := (((hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).comp
        (measurable_snd : Measurable (Prod.snd : ℝ × Ω → Ω))).indicator hset
      have hw : Measurable
          (fun z : ℝ × Ω ↦ ENNReal.ofReal (z.1 ^ (p - 2))) := by
        fun_prop
      exact hind.ennreal_ofReal.mul hw
    _ = ENNReal.ofReal p * ∫⁻ ω,
      ENNReal.ofReal ((M_n ω) ^ (p - 1) / (p-1) )
      * ENNReal.ofReal ((f n) ω) ∂μ
    := by
      congr
      funext ω
      let T := M_n ω
      have hT : 0 ≤ T := M_n_nonneg ω
      calc
        ∫⁻ (t : ℝ) in Set.Ioi 0,
          ENNReal.ofReal ({ω | t ≤ T}.indicator (f n) ω)
          * ENNReal.ofReal (t ^ (p - 2))
        = (∫⁻ t in Set.Ioc (0 : ℝ) (T), ENNReal.ofReal (t ^ (p - 2)))
          * ENNReal.ofReal (f n ω)
        := by
          rw [← lintegral_mul_const' (hr := (@ENNReal.ofReal_ne_top (f n ω)))]
          rw [← Set.Ioi_inter_Iic]
          rw [Set.inter_comm (Set.Ioi (0 : ℝ))]
          rw [← setLIntegral_indicator measurableSet_Iic]
          congr 1
          funext t
          by_cases h : t ≤ T
          <;> simp [h, mul_comm]
        _ =
          ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) (T), t ^ (p - 2) )
          * ENNReal.ofReal (f n ω)
        := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · change IntegrableOn (fun t : ℝ ↦ t ^ (p - 2)) (Set.Ioc 0 T)
            have hr : -1 < p - 2 := by linarith
            simpa [Set.uIoc_of_le hT] using
              (intervalIntegral.intervalIntegrable_rpow'
                (a := 0) (b := T) hr).1
          · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
            intro t ht
            exact Real.rpow_nonneg ht.1.le _
        _ =
          ENNReal.ofReal (∫ t : ℝ in 0..(T), t ^ (p - 2) )
          * ENNReal.ofReal (f n ω)
        := by
          rw [← intervalIntegral.integral_of_le (show 0 ≤ T by exact M_n_nonneg ω)]
        _ =
          ENNReal.ofReal ((T) ^ (p - 1) / (p-1) )
          * ENNReal.ofReal (f n ω)
        := by
          congr
          rw [integral_rpow]
          · simp [show p - 2 + 1 = p - 1 by ring]
            simp [Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
          · simp
            linarith
    _ = ENNReal.ofReal (p/(p-1))
      * ∫⁻ ω, ENNReal.ofReal (M_n ω) ^ (p-1)
      * ENNReal.ofReal (f n ω) ∂μ
    := by
      simp_rw [ENNReal.ofReal_div_of_pos (show 0 < p - 1 by linarith),
        ENNReal.ofReal_rpow_of_nonneg
          (M_n_nonneg _) (show 0 ≤ p - 1 by linarith),
        div_eq_mul_inv, mul_right_comm _ (ENNReal.ofReal (p - 1))⁻¹]
      rw [lintegral_mul_const']
      · ac_rfl
      · simpa using hp

private lemma prod_bootstrap
  (a b : ℝ≥0∞)
  (p : ℝ) (hp : p > 1)
  (hdom : a ^ p ≤ b * a ^ (p - 1))
  (hbd : a ≠ ∞) :
  a ≤ b
  := by
    by_cases h : a = 0
    · rw [h]
      simp
    rw (occs := .pos [1]) [show p = 1 + (p - 1) by ring] at hdom
    rw [ENNReal.rpow_add _ _ h hbd] at hdom
    rw [ENNReal.rpow_one] at hdom
    rw [ENNReal.mul_le_mul_iff_left
    (show a ^ (p - 1) ≠ 0 by
        exact fun hz ↦ h ((ENNReal.rpow_eq_zero_iff_of_pos (by linarith)).mp hz))
      (show a ^ (p - 1) ≠ ∞ by
        exact ENNReal.rpow_ne_top_of_ne_zero h hbd)] at hdom
    exact hdom

private lemma Lp_bootstrap
  (g : Ω → ℝ≥0∞) (h : Ω → ℝ≥0∞)
  (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
  (p : ℝ) (hp : p > 1) (C : ℝ≥0∞)
  (hdom : ∫⁻ ω, (g ω) ^ p ∂μ ≤ C * ∫⁻ ω, (g ω) ^ (p - 1) * (h ω) ∂μ)
  (hbd : eLpNorm' g p μ ≠ ∞) :
  eLpNorm' g p μ ≤ C * eLpNorm' h p μ
  := by
    have hLpNormDom : (eLpNorm' g p μ) ^ p
      ≤ C * (eLpNorm' h p μ) * (eLpNorm' g p μ) ^ (p - 1)
    := by
      rw [eLpNorm']
      rw [eLpNorm']
      rw [← ENNReal.rpow_mul]
      rw [← ENNReal.rpow_mul]
      rw [one_div_mul_cancel (show p ≠ 0 by linarith), ENNReal.rpow_one]
      simp_rw [enorm_eq_self]
      calc
        ∫⁻ (a : Ω), g a ^ p ∂μ ≤ C * ∫⁻ ω, (g ω) ^ (p - 1) * (h ω) ∂μ
        := hdom
        _ = C * ∫⁻ ω, (h * (fun ω ↦ (g ω) ^ (p - 1))) ω ∂μ
        := by
          congr
          funext ω
          simp only [Pi.mul_apply]
          exact CommSemigroup.mul_comm (g ω ^ (p - 1)) (h ω)
        _ ≤ C * (∫⁻ ω, h ω ^ p ∂μ) ^ (1 / p)
          * (∫⁻ ω, ((g ω) ^ (p - 1)) ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p-1)))
        := by
          rw [mul_assoc]
          gcongr 1
          exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ
           (Real.HolderConjugate.conjExponent hp)
           hh (hg.pow_const (p-1))
        _ = C * (∫⁻ ω, h ω ^ p ∂μ) ^ (1 / p)
          * ((∫⁻ ω, (g ω) ^ (p) ∂μ) ^ (1 / p * (p-1)))
        := by
          simp_rw [←ENNReal.rpow_mul]
          rw [show (p - 1) * (p / (p - 1)) = p by field_simp,
            show 1 / (p / (p - 1)) = 1 / p * (p - 1) by field_simp]
    exact prod_bootstrap _ _ _ hp hLpNormDom hbd

/-- **Doob's Lp maximal inequality**: Given a non-negative submartingale `f`, for all `p > 1`,
we have `eLpNorm' (f* n) p μ ≤ p/(p-1) * eLpNorm' (f n) p μ` where `f* n ω = max_{k ≤ n}, f k ω`.
-/
theorem maximal_ineq_Lp [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
  (p : ℝ) (hp : p > 1) (n : ℕ) :
  eLpNorm' (maximal_process f n) p μ
  ≤ (ENNReal.ofReal (p/(p-1))) * eLpNorm' (f n) p μ
  := by
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    have hp1 : 0 < p - 1 := sub_pos.mpr hp
    have hpENNreal1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
    have hC : ENNReal.ofReal (p / (p - 1)) ≠ 0
      := ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos hp0 hp1))
    -- Deal with infinte right-hand side
    by_cases hterminal : eLpNorm' (f n) p μ = ∞
    · simp [hterminal, ENNReal.mul_top hC]
    -- Show that the left-hand side is finite (with a bad bound)
    have norm_eq_norm' (u : Ω → ℝ) (hu : AEStronglyMeasurable u μ) :
        eLpNorm u (ENNReal.ofReal p) μ = eLpNorm' u p μ := by
      rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hu,
        ENNReal.toReal_ofReal hp0.le]
    have h_n_Lp : MemLp (f n) (ENNReal.ofReal p) μ := by
      change eLpNorm (f n) (ENNReal.ofReal p) μ < ∞
      rw [norm_eq_norm' _ ((hsub.stronglyMeasurable n).mono (𝒢.le n)).aestronglyMeasurable]
      exact lt_top_iff_ne_top.mpr hterminal
    have h_k_Lp (k : ℕ) (hk : k ≤ n) : MemLp (f k) (ENNReal.ofReal p) μ := by
      apply (h_n_Lp.condExp (m := 𝒢 k) hpENNreal1).mono'
      · exact ((hsub.stronglyMeasurable k).mono (𝒢.le k)).aestronglyMeasurable
      filter_upwards [hsub.ae_le_condExp hk] with ω hω
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg k ω)] using hω
    have h_sum_Lp := memLp_finsetSum (Finset.range (n + 1))
      (fun k hk ↦ h_k_Lp k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    have hmaxMeas : AEStronglyMeasurable (maximal_process f n) μ :=
      (((maximal_process_strongly_adapted hsub.stronglyAdapted n).le
        (𝒢.le n)).stronglyMeasurable).aestronglyMeasurable
    have hmaxLp : MemLp (maximal_process f n) (ENNReal.ofReal p) μ := by
      apply h_sum_Lp.mono' hmaxMeas
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (maximal_process_of_nonneg_is_nonneg hnonneg n ω)]
      apply Finset.sup'_le
      intro k hk
      exact Finset.single_le_sum (fun j _ ↦ hnonneg j ω) hk
    let maximal_process_ennreal := (fun ω ↦ ENNReal.ofReal (maximal_process f n ω))
    have hfinite : eLpNorm' maximal_process_ennreal p μ ≠ ∞ := by
      have hmaxFinite : eLpNorm' (maximal_process f n) p μ ≠ ∞ := by
        rw [← norm_eq_norm' _ hmaxMeas]
        exact hmaxLp.eLpNorm_ne_top
      simpa only [maximal_process_ennreal, eLpNorm', enorm_eq_self,
        Real.enorm_of_nonneg (maximal_process_of_nonneg_is_nonneg hnonneg n _)]
        using hmaxFinite
    -- Bootstrap to the claimed bound
    have h := Lp_bootstrap
      maximal_process_ennreal
      (fun ω ↦ ENNReal.ofReal (f n ω))
      (((maximal_process_strongly_adapted hsub.stronglyAdapted n).le
        (𝒢.le n)).aemeasurable.ennreal_ofReal)
      (((hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable.ennreal_ofReal)
      p hp (ENNReal.ofReal (p/(p-1)))
      (maximal_ineq_Lp_stage0 hsub hnonneg p hp n)
      hfinite
    simpa only [eLpNorm', enorm_eq_self,
      Real.enorm_of_nonneg (maximal_process_of_nonneg_is_nonneg hnonneg n _),
      Real.enorm_of_nonneg (hnonneg n _)] using h

end Maximal

end MeasureTheory

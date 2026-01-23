import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
## Cartan / minimum-modulus infrastructure for Hadamard factorization

This file provides the “probabilistic radius” / averaging lemmas used in Tao’s proof of Hadamard
factorization. The key analytic input is the pointwise bound

`log⁺ (1 / |1 - t|) ≤ sqrt (2 / |1 - t|)`,

which yields an integrable majorant for the logarithmic singularity when averaging on dyadic
intervals.
-/

noncomputable section

namespace Complex
namespace CartanBound

open Real MeasureTheory intervalIntegral

open scoped Topology ENNReal

/-! ### A radial majorant for the logarithmic singularity on a circle -/

lemma posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub_norm (w : ℂ) (hw : ‖w‖ ≠ (1 : ℝ)) :
    Real.posLog (1 / ‖(1 : ℂ) - w‖) ≤ Real.posLog (1 / |1 - ‖w‖|) := by
  -- Reverse triangle: `|1 - ‖w‖| = |‖1‖ - ‖w‖| ≤ ‖1 - w‖`.
  have hrev : |(‖(1 : ℂ)‖ : ℝ) - ‖w‖| ≤ ‖(1 : ℂ) - w‖ :=
    abs_norm_sub_norm_le (1 : ℂ) w
  have hrev' : |1 - ‖w‖| ≤ ‖(1 : ℂ) - w‖ := by
    simpa using hrev
  have h0 : |1 - ‖w‖| ≠ 0 := by
    have : (1 : ℝ) - ‖w‖ ≠ 0 := by
      intro h
      have : ‖w‖ = (1 : ℝ) := by linarith
      exact hw this
    simpa [abs_eq_zero] using this
  have hpos : 0 < |1 - ‖w‖| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
  have hdiv :
      (1 / ‖(1 : ℂ) - w‖ : ℝ) ≤ (1 / |1 - ‖w‖| : ℝ) :=
    one_div_le_one_div_of_le hpos hrev'
  exact Real.posLog_le_posLog (by positivity) hdiv

lemma posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub
    {t : ℝ} (ht : t ≠ 1) (w : ℂ) (hw : ‖w‖ = t) :
    Real.posLog (1 / ‖(1 : ℂ) - w‖) ≤ Real.posLog (1 / |1 - t|) := by
  have hw' : ‖w‖ ≠ (1 : ℝ) := by
    simpa [hw] using ht
  simpa [hw] using (posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub_norm w hw')

/-! ### A coarse dyadic-interval bound for the singularity average -/

/-- The one-dimensional logarithmic singularity used in the Cartan/dyadic averaging argument. -/
def φ (t : ℝ) : ℝ :=
  log⁺ (1 / |1 - t|)

lemma measurable_phi : Measurable φ := by
  unfold φ
  -- `log⁺ x = max 0 (log x)`, so measurability is reduced to measurability of `log` and `abs`.
  simpa [Real.posLog_def, Real.posLog] using
    (by
      fun_prop : Measurable fun t : ℝ => max 0 (Real.log (1 / |1 - t|)))

lemma phi_le_log_two_of_le_half {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) : φ t ≤ Real.log 2 := by
  have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
  have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
    have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
    simpa [abs_of_nonneg hnonneg] using this
  have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
    have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have := one_div_le_one_div_of_le hhalfpos hden
    simpa [one_div, div_eq_mul_inv] using this
  have hposLog : log⁺ (1 / |1 - t|) ≤ log⁺ (2 : ℝ) :=
    Real.posLog_le_posLog (by positivity) hfrac
  have habs : (1 : ℝ) ≤ |(2 : ℝ)| := by
    simp
  have hposLog2 : (log⁺ (2 : ℝ)) = Real.log 2 := by
    simpa using (Real.posLog_eq_log habs)
  simpa [φ, hposLog2] using hposLog

lemma phi_eq_zero_of_one_le_abs_one_sub {t : ℝ} (ht : (1 : ℝ) ≤ |1 - t|) : φ t = 0 := by
  have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) ht
  have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 ht
  have habs : |(1 / |1 - t| : ℝ)| ≤ 1 := by
    have hnonneg : 0 ≤ (1 / |1 - t| : ℝ) := by positivity
    simpa [abs_of_nonneg hnonneg] using hfrac
  have : log⁺ (1 / |1 - t|) = 0 := (Real.posLog_eq_zero_iff _).2 habs
  simpa [φ] using this

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by
  simpa [φ] using (Real.posLog_nonneg (x := (1 / |1 - t|)))

lemma φ_le_sqrt (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
  simpa [φ] using (Real.posLog_one_div_abs_one_sub_le_sqrt_two_div t)

lemma ae_restrict_norm_phi_le_of_forall_mem {A B : ℝ} (hAB : A ≤ B) {g : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (h : ∀ t ∈ Set.Icc A B, φ t ≤ g t) :
    (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] fun t => ‖g t‖ := by
  refine
    MeasureTheory.ae_restrict_of_forall_mem (μ := (volume : MeasureTheory.Measure ℝ))
    (s := Set.uIoc A B)
      (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A B))) ?_
  intro t ht
  have htIoc : t ∈ Set.Ioc A B := by
    simpa [Set.uIoc_of_le hAB] using ht
  have htIcc : t ∈ Set.Icc A B := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hle : φ t ≤ g t := h t htIcc
  have hφ0 : 0 ≤ φ t := φ_nonneg t
  have hg0 : 0 ≤ g t := hg t
  simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hg0] using hle


/-!
### Bridge lemma: from the 1D singularity `φ` to a complex lower bound

On a circle `‖u‖ = r`, the quantity `log ‖1 - u/a‖` is bounded below in terms of `φ(r/‖a‖)`.
This is the local estimate used in Tao's probabilistic-radius argument.
-/

lemma log_norm_one_sub_div_ge_neg_phi {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -φ (r / ‖a‖) := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have hnorm_ge : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [habs]
      exact hdiv
    rwa [hnorm_eq]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have hlogx :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖) := by
    have := Real.neg_posLog_inv_le_log (x := |1 - (r / ‖a‖)|)
    simpa [φ, one_div, inv_inv, abs_sub_comm, sub_eq_add_neg] using this
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) hnorm_ge
  linarith [hlog_mono, hlogx]

/-- The integral of the square-root majorant for `φ` on `[1/4, 4]`. -/
noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume

lemma K_nonneg : 0 ≤ K := by
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro _t _ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg
    (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)

/-- A convenient explicit constant controlling dyadic averages of `φ`. -/
noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1

lemma Cφ_pos : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := K_nonneg
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_Icc :
    IntervalIntegrable
      (fun t : ℝ => Real.sqrt (2 / |1 - t|))
      volume (1 / 4 : ℝ) (4 : ℝ) := by
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)
  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    have hpow :
        IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact
      (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm)
        hpow2
  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)
  have hleft :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have htmp' :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) :=
      htmp.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    have htmp'' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using htmp'
    simpa [f] using htmp''
  have hright :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have htmp' : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using htmp
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|))
          (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t _ht
      simp [f, abs_sub_comm]
    exact
      (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr)
        htmp'
  exact hleft.trans hright

lemma intervalIntegrable_phi_dyadic {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  classical
  by_cases hA0 : A = 0
  · subst hA0
    simp
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hA_le : A ≤ 2 * A := by nlinarith
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      have hφ_le : ∀ t ∈ Set.Icc A (2 * A), φ t ≤ Real.log 2 := by
        intro t ht
        have ht_le : t ≤ (1 / 2 : ℝ) := by
          have : t ≤ 2 * A := ht.2
          exact this.trans (by nlinarith [hsmall])
        exact phi_le_log_two_of_le_half ht_le
      have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
        intervalIntegral.intervalIntegrable_const
      have hmeas :
          AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
        (measurable_phi.aestronglyMeasurable : _)
      have hdom :
          (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun _ =>
            ‖(Real.log 2 : ℝ)‖ := by
        refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
          (g := fun _ => (Real.log 2 : ℝ)) (hg := fun _ => ?_) ?_
        · have : (1 : ℝ) ≤ 2 := by norm_num
          simpa using (Real.log_nonneg this)
        · intro t ht
          simpa using hφ_le t ht
      exact IntervalIntegrable.mono_fun hconst hmeas hdom
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht2 : (2 : ℝ) ≤ t := le_trans hbig (le_of_lt htIoc.1)
            have hden : (1 : ℝ) ≤ |1 - t| := by
              have : (1 : ℝ) ≤ t - 1 := by linarith
              have : (1 : ℝ) ≤ |t - 1| := by
                simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
              simpa [abs_sub_comm] using this
            simpa using (phi_eq_zero_of_one_le_abs_one_sub (t := t) hden)
          have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
            intervalIntegral.intervalIntegrable_const
          exact (IntervalIntegrable.congr (a := A) (b := (2 * A))
            (μ := (volume : MeasureTheory.Measure ℝ))
            (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
              intro t ht
              simpa using (hEq (x := t) ht).symm)) hz
      | inr hA_le_two =>
          have hsqrt_big :
              IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|))
                (volume : MeasureTheory.Measure ℝ) (1 / 4 : ℝ) (4 : ℝ) :=
            intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
          have hsqrt :
              IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
            refine hsqrt_big.mono_set ?_
            refine Set.uIcc_subset_uIcc ?_ ?_
            · exact (Set.mem_uIcc).2 (Or.inl ⟨hge_quarter, by nlinarith [hA_le_two]⟩)
            · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hge_quarter], by nlinarith [hA_le_two]⟩)
          have hmeas :
              AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
            (measurable_phi.aestronglyMeasurable : _)
          have hdom :
              (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
                fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
            refine
              ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
                (g := fun t => Real.sqrt (2 / |1 - t|)) (hg := fun _ => Real.sqrt_nonneg _) ?_
            intro t _ht
            exact φ_le_sqrt t
          exact IntervalIntegrable.mono_fun hsqrt hmeas hdom

lemma intervalIntegrable_phi_div {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hRa_nonneg : 0 ≤ R / a := by
    exact div_nonneg hR (le_of_lt ha)
  have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
    intervalIntegrable_phi_dyadic (A := (R / a)) hRa_nonneg
  have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
  have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
    field_simp [ha0]
  simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this

lemma integral_phi_le_Cφ_mul {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  classical
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hA_le : A ≤ 2 * A := by nlinarith
  have hCφ_nn : 0 ≤ Cφ := le_of_lt Cφ_pos
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      have hφ_le : ∀ t ∈ Set.Icc A (2 * A), φ t ≤ Real.log 2 := by
        intro t ht
        have ht_le : t ≤ (1 / 2 : ℝ) := by
          have : t ≤ 2 * A := ht.2
          have : t ≤ (1 / 2 : ℝ) := this.trans (by nlinarith [hsmall])
          exact this
        exact phi_le_log_two_of_le_half ht_le
      have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
        intervalIntegral.intervalIntegrable_const
      have hmeas :
          AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
        (measurable_phi.aestronglyMeasurable : _)
      have hdom :
          (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
            fun _ => ‖(Real.log 2 : ℝ)‖ := by
        refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
          (g := fun _ => (Real.log 2 : ℝ)) (hg := fun _ => ?_) ?_
        · have : (1 : ℝ) ≤ 2 := by norm_num
          simpa using (Real.log_nonneg this)
        · intro t ht
          simpa using hφ_le t ht
      have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
        IntervalIntegrable.mono_fun hconst hmeas hdom
      have hle_int :
          (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
            ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
        refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ))
          hA_le hφ_int hconst ?_
        intro t ht
        exact hφ_le t ht
      have hRHS : (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
        simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
      have hcoef : A * Real.log 2 ≤ Cφ * A := by
        have hlog_le : Real.log 2 ≤ Cφ := by
          dsimp [Cφ]
          have hK : 0 ≤ K := K_nonneg
          linarith [hK]
        have := mul_le_mul_of_nonneg_left hlog_le hA
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      calc
        (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
            ≤ A * Real.log 2 := by simpa [hRHS] using hle_int
        _ ≤ Cφ * A := hcoef
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
            intro t ht
            have ht' : t ∈ Set.Icc A (2 * A) := by
              simpa [Set.uIcc_of_le hA_le] using ht
            have htA : A ≤ t := ht'.1
            have ht2 : 2 ≤ t := le_trans hbig htA
            have hden : 1 ≤ |1 - t| := by
              have : (1 : ℝ) ≤ t - 1 := by linarith
              have : (1 : ℝ) ≤ |t - 1| := by
                simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
              simpa [abs_sub_comm] using this
            simpa using (phi_eq_zero_of_one_le_abs_one_sub (t := t) hden)
          have : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
            simpa using
              intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
          have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg hCφ_nn hA
          simpa [this] using hnonneg
      | inr hA_le_two =>
          have hA_lower : (1 / 4 : ℝ) ≤ A := hge_quarter
          have hA_upper : (2 * A : ℝ) ≤ 4 := by nlinarith [hA_le_two]
          let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
          have hsqrt_big :
              IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) :=
            intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
          have hsqrt :
              IntervalIntegrable s volume A (2 * A) := by
            refine hsqrt_big.mono_set ?_
            refine Set.uIcc_subset_uIcc ?_ ?_
            · exact (Set.mem_uIcc).2 (Or.inl ⟨hA_lower, by nlinarith [hA_le_two]⟩)
            · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hA_lower], hA_upper⟩)
          have hmeasφ :
              AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
            (measurable_phi.aestronglyMeasurable : _)
          have hdomφ : (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
              fun t => ‖s t‖ := by
            refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
              (g := s) (hg := fun _ => Real.sqrt_nonneg _) ?_
            intro t _ht
            exact φ_le_sqrt t
          have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
            IntervalIntegrable.mono_fun hsqrt hmeasφ hdomφ
          have hle_int :
              (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
                ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
            refine intervalIntegral.integral_mono_on
              (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hsqrt ?_
            intro t _ht
            exact φ_le_sqrt t
          have hle_K :
              (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
                ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
            refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
              (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
              hA_lower hA_le hA_upper ?_ hsqrt_big
            exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
          have hKdef : (∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume) = K := by
            rfl
          have hK : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ K := by
            simpa [hKdef, K, s] using hle_K
          have : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ (4 * K + 1) * A := by
            have hA_le4 : A ≤ 4 := le_trans hA_le_two (by norm_num)
            -- crude: `∫ ≤ K` and `K ≤ (4K+1)*A` for `A ≥ 1/4`
            have : K ≤ (4 * K + 1) * A := by
              have hcoef : 1 ≤ 4 * A := by nlinarith [hA_lower]
              have hK' : 0 ≤ K := K_nonneg
              nlinarith [hK', hcoef]
            exact le_trans hK this
          have hlog2 : (Real.log 2) * A ≤ Cφ * A := by
            have hlog_le : Real.log 2 ≤ Cφ := by
              dsimp [Cφ]
              have hK : 0 ≤ K := K_nonneg
              linarith [hK]
            have := mul_le_mul_of_nonneg_left hlog_le hA
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
          calc
            (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
                ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := hle_int
            _ ≤ (4 * K + 1) * A := this
            _ ≤ Cφ * A := by
                  -- `4*K+1 ≤ log2 + 4*K + 1 = Cφ`
                  have : (4 * K + 1 : ℝ) ≤ Cφ := by
                    dsimp [Cφ]
                    have hlog_nonneg : 0 ≤ Real.log 2 := by
                      exact Real.log_nonneg (by norm_num)
                    linarith [hlog_nonneg]
                  exact mul_le_mul_of_nonneg_right this hA

/-!
### A “good radius” lemma (probabilistic-radius / Cartan averaging)

This is the abstract selection principle used in the dyadic averaging: if an averaged singularity
kernel has controlled integral on `[R,2R]`, then there exists a radius `r ∈ (R,2R]` where the
pointwise sum is controlled.
-/

open scoped BigOperators

lemma integral_phi_div_le_Cφ_mul {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume) ≤ Cφ * R := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrew :
      (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume)
        = a * (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) := by
    simp [smul_eq_mul, mul_left_comm, mul_comm, div_eq_mul_inv, ha0]
  rw [hrew]
  have hA : 0 ≤ R / a := by
    exact div_nonneg hR ha.le
  have hle : (∫ (t : ℝ) in (R / a)..(2 * (R / a)), φ t ∂volume) ≤ Cφ * (R / a) :=
    integral_phi_le_Cφ_mul (A := R / a) hA
  have hEq : (2 * R / a) = 2 * (R / a) := by ring
  have hle' :
      (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) ≤ Cφ * (R / a) := by
    simpa [hEq] using hle
  have ha_nonneg : 0 ≤ a := ha.le
  have := mul_le_mul_of_nonneg_left hle' ha_nonneg
  have hRHS : a * (Cφ * (R / a)) = Cφ * R := by
    field_simp [ha0]
  simpa [hRHS, mul_assoc, mul_left_comm, mul_comm] using this

lemma exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
  classical
  by_contra hbad
  have hforall :
      ∀ r ∈ Set.Ioc R (2 * R), Cφ * (∑ i ∈ s, w i) < (∑ i ∈ s, w i * φ (r / a i)) := by
    intro r hr
    have : ¬(∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
      intro hle
      exact hbad ⟨r, hr, hle⟩
    exact lt_of_not_ge this
  let g : ℝ → ℝ := ∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)
  have hg_int : IntervalIntegrable g volume R (2 * R) := by
    have : IntervalIntegrable (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) volume R (2 * R) := by
      refine IntervalIntegrable.sum (μ := volume) (a := R) (b := 2 * R)
        (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) ?_
      intro i hi
      have hai : 0 < a i := ha i hi
      have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
        intervalIntegrable_phi_div (a := a i) (R := R) hai hR.le
      simpa [mul_assoc] using hφi.const_mul (w i)
    simpa [g] using this
  have hconst_int :
      IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) :=
    intervalIntegral.intervalIntegrable_const
  have hIoc_meas : (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * R - R := by nlinarith [hR]
    simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
  have hlt_meas :
      (volume.restrict (Set.Ioc R (2 * R))) {r | (Cφ * (∑ i ∈ s, w i)) < g r} ≠ 0 := by
    have hall : Set.Ioc R (2 * R) ⊆ {r | (Cφ * (∑ i ∈ s, w i)) < g r} := by
      intro r hr
      simpa [g] using hforall r hr
    have hpos' :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R)) ≠ 0 := by
      simpa [MeasureTheory.Measure.restrict_apply, measurableSet_Ioc, Set.inter_self] using
        hIoc_meas
    have hle :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R))
          ≤ (volume.restrict (Set.Ioc R (2 * R))) {r | (Cφ * (∑ i ∈ s, w i)) < g r} :=
      MeasureTheory.measure_mono hall
    intro hzero
    have : (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R)) = 0 :=
      le_antisymm (le_trans hle (le_of_eq hzero)) (zero_le _)
    exact hpos' this
  have hlt_int :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume)
        < ∫ r in R..(2 * R), g r ∂volume := by
    have hab : R ≤ 2 * R := by nlinarith [hR.le]
    refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero (μ := volume)
      (a := R) (b := 2 * R) (f := fun _ => (Cφ * (∑ i ∈ s, w i))) (g := g)
      hab hconst_int hg_int ?_ hlt_meas
    refine MeasureTheory.ae_restrict_of_forall_mem (by simp) ?_
    intro r hr
    simpa [g] using le_of_lt (hforall r hr)
  have hconst_eval :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume) = Cφ * (∑ i ∈ s, w i) * R := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, mul_comm]
    ring
  have hg_le :
      (∫ r in R..(2 * R), g r ∂volume) ≤ Cφ * (∑ i ∈ s, w i) * R := by
    have hint : ∀ i ∈ s, IntervalIntegrable (fun r : ℝ => w i * φ (r / a i)) volume R (2 * R) := by
      intro i hi
      have hai : 0 < a i := ha i hi
      have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
        intervalIntegrable_phi_div (a := a i) (R := R) hai hR.le
      simpa [mul_assoc] using hφi.const_mul (w i)
    have hsum_int :
        (∫ r in R..(2 * R), g r ∂volume)
          = ∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume := by
      simpa [g] using
        (intervalIntegral.integral_finset_sum (μ := volume) (a := R) (b := 2 * R)
          (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) hint)
    rw [hsum_int]
    have hterm : ∀ i ∈ s,
        (∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume) ≤ (w i) * (Cφ * R) := by
      intro i hi
      have hw' : 0 ≤ w i := hw i hi
      have hai : 0 < a i := ha i hi
      have hphi :
          (∫ r in R..(2 * R), φ (r / a i) ∂volume) ≤ Cφ * R :=
        integral_phi_div_le_Cφ_mul (a := a i) (R := R) hai hR.le
      have := mul_le_mul_of_nonneg_left hphi hw'
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hsum_le : (∑ i ∈ s,
        (∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume))
        ≤ ∑ i ∈ s, (w i) * (Cφ * R) := by
      exact Finset.sum_le_sum (fun i hi => hterm i hi)
    refine le_trans hsum_le ?_
    have hEqFinal :
        (∑ i ∈ s, (w i) * (Cφ * R)) = Cφ * (∑ i ∈ s, w i) * R := by
      calc
        (∑ i ∈ s, (w i) * (Cφ * R)) = (∑ i ∈ s, w i) * (Cφ * R) := by
          simp [Finset.sum_mul]
        _ = Cφ * (∑ i ∈ s, w i) * R := by
          ac_rfl
    exact le_of_eq hEqFinal
  have : ¬(Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R) := lt_irrefl _
  have hcontra : Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R := by
    have := hlt_int
    simpa [hconst_eval] using (this.trans_le hg_le)
  exact this hcontra

lemma exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i)
    (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
      (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
  classical
  by_contra hbad
  have hforall :
      ∀ r ∈ Set.Ioc R (2 * R), r ∉ bad →
        Cφ * (∑ i ∈ s, w i) < (∑ i ∈ s, w i * φ (r / a i)) := by
    intro r hr hrbad
    have : ¬(∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
      intro hle
      exact hbad ⟨r, hr, hrbad, hle⟩
    exact lt_of_not_ge this
  let g : ℝ → ℝ := ∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)
  have hg_int : IntervalIntegrable g volume R (2 * R) := by
    have : IntervalIntegrable (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) volume R (2 * R) := by
      refine IntervalIntegrable.sum (μ := volume) (a := R) (b := 2 * R)
        (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) ?_
      intro i hi
      have hai : 0 < a i := ha i hi
      have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
        intervalIntegrable_phi_div (a := a i) (R := R) hai hR.le
      simpa [mul_assoc] using hφi.const_mul (w i)
    simpa [g] using this
  have hconst_int :
      IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) :=
    intervalIntegral.intervalIntegrable_const
  have hIoc_meas : (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * R - R := by nlinarith [hR]
    simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
  have hbad_meas : (volume : MeasureTheory.Measure ℝ) (bad : Set ℝ) = 0 := by
    simpa using (bad.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)))
  have hIoc_diff_meas :
      (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
    have : (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
        = (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) := by
      simpa [Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
        (MeasureTheory.measure_diff_null (s := Set.Ioc R (2 * R)) (t := (bad : Set ℝ)) hbad_meas)
    simpa [this] using hIoc_meas
  have hlt_meas :
      (volume.restrict (Set.Ioc R (2 * R)))
        {r | Cφ * (∑ i ∈ s, w i) < g r} ≠ 0 := by
    have hall : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ {r | Cφ * (∑ i ∈ s, w i) < g r} := by
      intro r hr
      have hrIoc : r ∈ Set.Ioc R (2 * R) := hr.1
      have hrbad : r ∉ bad := by simpa using hr.2
      simpa [g] using hforall r hrIoc hrbad
    have hle :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
          ≤ (volume.restrict (Set.Ioc R (2 * R))) {r | Cφ * (∑ i ∈ s, w i) < g r} :=
      MeasureTheory.measure_mono hall
    have hpos' :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
      have hsubset : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ Set.Ioc R (2 * R) := by
        intro r hr
        exact hr.1
      have hinter :
          (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ∩ Set.Ioc R (2 * R)
            = (Set.Ioc R (2 * R) \ (bad : Set ℝ)) := by
        exact Set.inter_eq_left.mpr hsubset
      simpa [MeasureTheory.Measure.restrict_apply, measurableSet_Ioc, hinter] using hIoc_diff_meas
    intro hzero
    have : (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) = 0 :=
      le_antisymm (le_trans hle (le_of_eq hzero)) (zero_le _)
    exact hpos' this
  have hlt_int :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume)
        < ∫ r in R..(2 * R), g r ∂volume := by
    have hab : R ≤ 2 * R := by nlinarith [hR.le]
    refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero (μ := volume)
      (a := R) (b := 2 * R) (f := fun _ => (Cφ * (∑ i ∈ s, w i))) (g := g)
      hab hconst_int hg_int ?_ hlt_meas
    have hmem : ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∈ Set.Ioc R (2 * R) :=
      MeasureTheory.ae_restrict_mem (by simp)
    have hnotBad :
        ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∉ (bad : Set ℝ) := by
      simpa using
        (bad.finite_toSet.countable.ae_notMem (μ := (volume.restrict (Set.Ioc R (2 * R)))))
    filter_upwards [hmem, hnotBad] with r hrIoc hrNotBad
    have hrNotBad' : r ∉ bad := by simpa using hrNotBad
    exact le_of_lt (by simpa [g] using hforall r hrIoc hrNotBad')
  have hconst_eval :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume) = Cφ * (∑ i ∈ s, w i) * R := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, mul_comm]
    ring
  have hg_le :
      (∫ r in R..(2 * R), g r ∂volume) ≤ Cφ * (∑ i ∈ s, w i) * R := by
    have hint : ∀ i ∈ s, IntervalIntegrable (fun r : ℝ => w i * φ (r / a i)) volume R (2 * R) := by
      intro i hi
      have hai : 0 < a i := ha i hi
      have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
        intervalIntegrable_phi_div (a := a i) (R := R) hai hR.le
      simpa [mul_assoc] using hφi.const_mul (w i)
    have hsum_int :
        (∫ r in R..(2 * R), g r ∂volume)
          = ∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume := by
      simpa [g] using
        (intervalIntegral.integral_finset_sum (μ := volume) (a := R) (b := 2 * R)
          (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) hint)
    rw [hsum_int]
    have hsum_le :
        (∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume)
          ≤ ∑ i ∈ s, w i * (Cφ * R) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hw' : 0 ≤ w i := hw i hi
      have hai : 0 < a i := ha i hi
      have hphi :
          (∫ r in R..(2 * R), φ (r / a i) ∂volume) ≤ Cφ * R :=
        integral_phi_div_le_Cφ_mul (a := a i) (R := R) hai hR.le
      have := mul_le_mul_of_nonneg_left hphi hw'
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    refine le_trans hsum_le ?_
    have : (∑ i ∈ s, w i * (Cφ * R)) = Cφ * (∑ i ∈ s, w i) * R := by
      calc
        (∑ i ∈ s, w i * (Cφ * R)) = (∑ i ∈ s, w i) * (Cφ * R) := by
          simp [Finset.sum_mul]
        _ = Cφ * (∑ i ∈ s, w i) * R := by ac_rfl
    exact le_of_eq this
  have : ¬(Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R) := lt_irrefl _
  have hcontra : Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R := by
    have := hlt_int
    simpa [hconst_eval] using (this.trans_le hg_le)
  exact this hcontra

end CartanBound
end Complex

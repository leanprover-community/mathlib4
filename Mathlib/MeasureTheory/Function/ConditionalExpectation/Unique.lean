/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

/-!
# Uniqueness of the conditional expectation

Two Lp functions `f, g` which are almost everywhere strongly measurable with respect to a σ-algebra
`m` and verify `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ` for all `m`-measurable sets `s` are equal
almost everywhere. This proves the uniqueness of the conditional expectation, which is not yet
defined in this file but is introduced in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`.

## Main statements

* `Lp.ae_eq_of_forall_setIntegral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_setIntegral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[SigmaFinite (μ.trim hm)]`.

-/


open scoped ENNReal MeasureTheory

namespace MeasureTheory

variable {α E' F' 𝕜 : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [CompleteSpace F']

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/

theorem lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn (f : Lp E' p μ) s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, (f : Lp E' p μ) x ∂μ = 0) :
    f =ᵐ[μ] (0 : α → E') := by
  obtain ⟨g, hg_sm, hfg⟩ := lpMeas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine hfg.trans ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hm ?_ ?_ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [IntegrableOn, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs

variable (𝕜)

include 𝕜 in
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' (hm : m ≤ m0) (f : Lp E' p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf_meas : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] 0 := by
  let f_meas : lpMeas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp [f_meas]
  refine hf_f_meas.trans ?_
  exact lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    hm f_meas hp_ne_zero hp_ne_top hf_int_finite hf_zero

include 𝕜 in
/-- **Uniqueness of the conditional expectation** -/
theorem Lp.ae_eq_of_forall_setIntegral_eq' (hm : m ≤ m0) (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf_meas : AEStronglyMeasurable[m] f μ) (hg_meas : AEStronglyMeasurable[m] g μ) :
    f =ᵐ[μ] g := by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0 by
    rw [← sub_ae_eq_zero]; exact (Lp.coeFn_sub f g).symm.trans h_sub
  have hfg' : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' 𝕜 hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
    <| (hf_meas.sub hg_meas).congr (Lp.coeFn_sub f g).symm

variable {𝕜}

theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  rw [← ae_eq_trim_iff_of_aestronglyMeasurable hm hfm hgm]
  have hf_mk_int_finite (s) :
      MeasurableSet[m] s → μ.trim hm s < ∞ → @IntegrableOn _ _ m _ _ (hfm.mk f) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    -- Porting note: `rw [IntegrableOn]` fails with
    -- synthesized type class instance is not definitionally equal to expression inferred by typing
    -- rules, synthesized m0 inferred m
    unfold IntegrableOn
    rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hfm.stronglyMeasurable_mk
    exact Integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite (s) :
      MeasurableSet[m] s → μ.trim hm s < ∞ → @IntegrableOn _ _ m _ _ (hgm.mk g) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    -- Porting note: `rw [IntegrableOn]` fails with
    -- synthesized type class instance is not definitionally equal to expression inferred by typing
    -- rules, synthesized m0 inferred m
    unfold IntegrableOn
    rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hgm.stronglyMeasurable_mk
    exact Integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    ∀ s : Set α,
      MeasurableSet[m] s →
        μ.trim hm s < ∞ → ∫ x in s, hfm.mk f x ∂μ.trim hm = ∫ x in s, hgm.mk g x ∂μ.trim hm := by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.stronglyMeasurable_mk, ←
      integral_trim hm hgm.stronglyMeasurable_mk,
      integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

end UniquenessOfConditionalExpectation

section IntegralNormLE

variable {s : Set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` an `m0`-measurable function and `g` an `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ` on all `m`-measurable sets with finite measure. -/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeasurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) : (∫ x in s, ‖g x‖ ∂μ) ≤ ∫ x in s, ‖f x‖ ∂μ := by
  rw [integral_norm_eq_pos_sub_neg hgi, integral_norm_eq_pos_sub_neg hfi]
  have h_meas_nonneg_g : MeasurableSet[m] {x | 0 ≤ g x} :=
    (@stronglyMeasurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet {x | 0 ≤ f x} :=
    stronglyMeasurable_const.measurableSet_le hf
  have h_meas_nonpos_g : MeasurableSet[m] {x | g x ≤ 0} :=
    hg.measurableSet_le (@stronglyMeasurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet {x | f x ≤ 0} :=
    hf.measurableSet_le stronglyMeasurable_const
  refine sub_le_sub ?_ ?_
  · rw [Measure.restrict_restrict (hm _ h_meas_nonneg_g), Measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      Measure.restrict_restrict h_meas_nonneg_f]
    exact setIntegral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [Measure.restrict_restrict (hm _ h_meas_nonpos_g), Measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      Measure.restrict_restrict h_meas_nonpos_f]
    exact setIntegral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi

/-- Let `m` be a sub-σ-algebra of `m0`, `f` an `m0`-measurable function and `g` an `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ‖g x‖ₑ ∂μ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ` on all `m`-measurable sets with finite
measure. -/
theorem lintegral_enorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeasurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) : (∫⁻ x in s, ‖g x‖ₑ ∂μ) ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi, ←
    ofReal_integral_norm_eq_lintegral_enorm hgi, ENNReal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · positivity

end IntegralNormLE

end MeasureTheory

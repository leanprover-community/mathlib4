/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.conditional_expectation.unique
! leanprover-community/mathlib commit d8bbb04e2d2a44596798a9207ceefc0fb236e41e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.AeEqOfIntegral
import Mathbin.MeasureTheory.Function.ConditionalExpectation.AeMeasurable

/-!
# Uniqueness of the conditional expectation

Two Lp functions `f, g` which are almost everywhere strongly measurable with respect to a σ-algebra
`m` and verify `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ` for all `m`-measurable sets `s` are equal
almost everywhere. This proves the uniqueness of the conditional expectation, which is not yet
defined in this file but is introduced in `measure_theory.function.conditional_expectation.basic`.

## Main statements

* `Lp.ae_eq_of_forall_set_integral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[sigma_finite (μ.trim hm)]`.

-/


open scoped ENNReal MeasureTheory

namespace MeasureTheory

variable {α E' F' 𝕜 : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/


theorem lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  by
  obtain ⟨g, hg_sm, hfg⟩ := Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine' hfg.trans _
  refine' ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integrable_on, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
#align measure_theory.Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero MeasureTheory.lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero

include 𝕜

variable (𝕜)

theorem Lp.ae_eq_zero_of_forall_set_integral_eq_zero' (hm : m ≤ m0) (f : Lp E' p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf_meas : AeStronglyMeasurable' m f μ) : f =ᵐ[μ] 0 :=
  by
  let f_meas : Lp_meas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp only [coeFn_coe_base', Subtype.coe_mk]
  refine' hf_f_meas.trans _
  refine' Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integrable_on, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
#align measure_theory.Lp.ae_eq_zero_of_forall_set_integral_eq_zero' MeasureTheory.Lp.ae_eq_zero_of_forall_set_integral_eq_zero'

/-- **Uniqueness of the conditional expectation** -/
theorem Lp.ae_eq_of_forall_set_integral_eq' (hm : m ≤ m0) (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf_meas : AeStronglyMeasurable' m f μ) (hg_meas : AeStronglyMeasurable' m g μ) : f =ᵐ[μ] g :=
  by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0
  · rw [← sub_ae_eq_zero]; exact (Lp.coe_fn_sub f g).symm.trans h_sub
  have hfg' : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0 :=
    by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on (⇑(f - g)) s μ :=
    by
    intro s hs hμs
    rw [integrable_on, integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  have hfg_meas : ae_strongly_measurable' m (⇑(f - g)) μ :=
    ae_strongly_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm
  exact
    Lp.ae_eq_zero_of_forall_set_integral_eq_zero' 𝕜 hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
      hfg_meas
#align measure_theory.Lp.ae_eq_of_forall_set_integral_eq' MeasureTheory.Lp.ae_eq_of_forall_set_integral_eq'

variable {𝕜}

omit 𝕜

theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hfm : AeStronglyMeasurable' m f μ) (hgm : AeStronglyMeasurable' m g μ) : f =ᵐ[μ] g :=
  by
  rw [← ae_eq_trim_iff_of_ae_strongly_measurable' hm hfm hgm]
  have hf_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ (hfm.mk f) s (μ.trim hm) :=
    by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs 
    rw [integrable_on, restrict_trim hm _ hs]
    refine' integrable.trim hm _ hfm.strongly_measurable_mk
    exact integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ (hgm.mk g) s (μ.trim hm) :=
    by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs 
    rw [integrable_on, restrict_trim hm _ hs]
    refine' integrable.trim hm _ hgm.strongly_measurable_mk
    exact integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    ∀ s : Set α,
      measurable_set[m] s →
        μ.trim hm s < ∞ → ∫ x in s, hfm.mk f x ∂μ.trim hm = ∫ x in s, hgm.mk g x ∂μ.trim hm :=
    by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs 
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.strongly_measurable_mk, ←
      integral_trim hm hgm.strongly_measurable_mk,
      integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq
#align measure_theory.ae_eq_of_forall_set_integral_eq_of_sigma_finite' MeasureTheory.ae_eq_of_forall_set_integral_eq_of_sigma_finite'

end UniquenessOfConditionalExpectation

section IntegralNormLe

variable {s : Set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ` on all `m`-measurable sets with finite measure. -/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : strongly_measurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) : ∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ :=
  by
  rw [integral_norm_eq_pos_sub_neg hgi, integral_norm_eq_pos_sub_neg hfi]
  have h_meas_nonneg_g : measurable_set[m] {x | 0 ≤ g x} :=
    (@strongly_measurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet {x | 0 ≤ f x} :=
    strongly_measurable_const.measurable_set_le hf
  have h_meas_nonpos_g : measurable_set[m] {x | g x ≤ 0} :=
    hg.measurable_set_le (@strongly_measurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet {x | f x ≤ 0} :=
    hf.measurable_set_le strongly_measurable_const
  refine' sub_le_sub _ _
  · rw [measure.restrict_restrict (hm _ h_meas_nonneg_g), measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      measure.restrict_restrict h_meas_nonneg_f]
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [measure.restrict_restrict (hm _ h_meas_nonpos_g), measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      measure.restrict_restrict h_meas_nonpos_f]
    exact set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi
#align measure_theory.integral_norm_le_of_forall_fin_meas_integral_eq MeasureTheory.integral_norm_le_of_forall_fin_meas_integral_eq

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ‖g x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
theorem lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : strongly_measurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) : ∫⁻ x in s, ‖g x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ :=
  by
  rw [← of_real_integral_norm_eq_lintegral_nnnorm hfi, ←
    of_real_integral_norm_eq_lintegral_nnnorm hgi, ENNReal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · exact integral_nonneg fun x => norm_nonneg _
#align measure_theory.lintegral_nnnorm_le_of_forall_fin_meas_integral_eq MeasureTheory.lintegral_nnnorm_le_of_forall_fin_meas_integral_eq

end IntegralNormLe

end MeasureTheory


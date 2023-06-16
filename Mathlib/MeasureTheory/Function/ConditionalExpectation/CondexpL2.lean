/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.conditional_expectation.condexp_L2
! leanprover-community/mathlib commit d8bbb04e2d2a44596798a9207ceefc0fb236e41e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.MeasureTheory.Function.ConditionalExpectation.Unique

/-! # Conditional expectation in L2

This file contains one step of the construction of the conditional expectation, which is completed
in `measure_theory.function.conditional_expectation.basic`. See that file for a description of the
full process.

We build the conditional expectation of an `L²` function, as an element of `L²`. This is the
orthogonal projection on the subspace of almost everywhere `m`-measurable functions.

## Main definitions

* `condexp_L2`: Conditional expectation of a function in L2 with respect to a sigma-algebra: it is
the orthogonal projection on the subspace `Lp_meas`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : is_R_or_C`:
* `condexp_L2` is defined only for an `inner_product_space` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `normed_space 𝕜 F`.

-/


open TopologicalSpace Filter ContinuousLinearMap

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E E' F G G' 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E for an inner product space
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

local notation "⟪" x ", " y "⟫₂" => @inner 𝕜 (α →₂[μ] E) _ x y

variable (𝕜)

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
noncomputable def condexpL2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] lpMeas E 𝕜 m 2 μ :=
  @orthogonalProjection 𝕜 (α →₂[μ] E) _ _ _ (lpMeas E 𝕜 m 2 μ)
    haveI : Fact (m ≤ m0) := ⟨hm⟩
    inferInstance
#align measure_theory.condexp_L2 MeasureTheory.condexpL2

variable {𝕜}

theorem aEStronglyMeasurable'_condexpL2 (hm : m ≤ m0) (f : α →₂[μ] E) :
    AEStronglyMeasurable' m (condexpL2 𝕜 hm f) μ :=
  lpMeas.aeStronglyMeasurable' _
#align measure_theory.ae_strongly_measurable'_condexp_L2 MeasureTheory.aEStronglyMeasurable'_condexpL2

theorem integrableOn_condexpL2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (condexpL2 𝕜 hm f) s μ :=
  integrableOn_Lp_of_measure_ne_top (condexpL2 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim hμs
#align measure_theory.integrable_on_condexp_L2_of_measure_ne_top MeasureTheory.integrableOn_condexpL2_of_measure_ne_top

theorem integrable_condexpL2_of_isFiniteMeasure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (condexpL2 𝕜 hm f) μ :=
  integrableOn_univ.mp <| integrableOn_condexpL2_of_measure_ne_top hm (measure_ne_top _ _) f
#align measure_theory.integrable_condexp_L2_of_is_finite_measure MeasureTheory.integrable_condexpL2_of_isFiniteMeasure

theorem norm_condexpL2_le_one (hm : m ≤ m0) : ‖@condexpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ ≤ 1 :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  orthogonalProjection_norm_le _
#align measure_theory.norm_condexp_L2_le_one MeasureTheory.norm_condexpL2_le_one

theorem norm_condexpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ‖condexpL2 𝕜 hm f‖ ≤ ‖f‖ :=
  ((@condexpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condexpL2_le_one hm))
#align measure_theory.norm_condexp_L2_le MeasureTheory.norm_condexpL2_le

theorem snorm_condexpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    snorm (condexpL2 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
  by
  rw [Lp_meas_coe, ← ENNReal.toReal_le_toReal (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ←
    Lp.norm_def, ← Lp.norm_def, Submodule.norm_coe]
  exact norm_condexp_L2_le hm f
#align measure_theory.snorm_condexp_L2_le MeasureTheory.snorm_condexpL2_le

theorem norm_condexpL2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖(condexpL2 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f‖ :=
  by
  rw [Lp.norm_def, Lp.norm_def, ← Lp_meas_coe]
  refine' (ENNReal.toReal_le_toReal _ (Lp.snorm_ne_top _)).mpr (snorm_condexp_L2_le hm f)
  exact Lp.snorm_ne_top _
#align measure_theory.norm_condexp_L2_coe_le MeasureTheory.norm_condexpL2_coe_le

theorem inner_condexpL2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, (condexpL2 𝕜 hm g : α →₂[μ] E)⟫₂ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  inner_orthogonalProjection_left_eq_right _ f g
#align measure_theory.inner_condexp_L2_left_eq_right MeasureTheory.inner_condexpL2_left_eq_right

theorem condexpL2_indicator_of_measurable (hm : m ≤ m0) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞)
    (c : E) :
    (condexpL2 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) =
      indicatorConstLp 2 (hm s hs) hμs c :=
  by
  rw [condexp_L2]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicator_const_Lp 2 (hm s hs) hμs c ∈ Lp_meas E 𝕜 m 2 μ :=
    mem_Lp_meas_indicator_const_Lp hm hs hμs
  let ind := (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicator_const_Lp 2 (hm s hs) hμs c := by rfl
  have h_orth_mem := orthogonalProjection_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]
#align measure_theory.condexp_L2_indicator_of_measurable MeasureTheory.condexpL2_indicator_of_measurable

theorem inner_condexpL2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable' m g μ) : ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ :=
  by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2]
  simp only [mem_Lp_meas_iff_ae_strongly_measurable'.mpr hg, orthogonalProjection_inner_eq_zero]
#align measure_theory.inner_condexp_L2_eq_inner_fun MeasureTheory.inner_condexpL2_eq_inner_fun

section Real

variable {hm : m ≤ m0}

theorem integral_condexpL2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condexpL2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
  by
  rw [← L2.inner_indicator_const_Lp_one (hm s hs) hμs]
  have h_eq_inner :
    ∫ x in s, condexp_L2 𝕜 hm f x ∂μ =
      inner (indicator_const_Lp 2 (hm s hs) hμs (1 : 𝕜)) (condexp_L2 𝕜 hm f) :=
    by
    rw [L2.inner_indicator_const_Lp_one (hm s hs) hμs]
    congr
  rw [h_eq_inner, ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable hm hs hμs]
#align measure_theory.integral_condexp_L2_eq_of_fin_meas_real MeasureTheory.integral_condexpL2_eq_of_fin_meas_real

theorem lintegral_nnnorm_condexpL2_le (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (f : Lp ℝ 2 μ) :
    ∫⁻ x in s, ‖condexpL2 ℝ hm f x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ :=
  by
  let h_meas := Lp_meas.ae_strongly_measurable' (condexp_L2 ℝ hm f)
  let g := h_meas.some
  have hg_meas : strongly_measurable[m] g := h_meas.some_spec.1
  have hg_eq : g =ᵐ[μ] condexp_L2 ℝ hm f := h_meas.some_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexp_L2 ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq :
    (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x => (‖condexp_L2 ℝ hm f x‖₊ : ℝ≥0∞) :=
    by
    refine' hg_eq_restrict.mono fun x hx => _
    dsimp only
    rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine'
    lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (Lp.strongly_measurable f) _ _ _ _ hs hμs
  · exact integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [integrable_on, integrable_congr hg_eq_restrict]
    exact integrable_on_condexp_L2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condexp_L2_eq_of_fin_meas_real f ht hμt.ne]
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)
#align measure_theory.lintegral_nnnorm_condexp_L2_le MeasureTheory.lintegral_nnnorm_condexpL2_le

theorem condexpL2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {f : Lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condexpL2 ℝ hm f =ᵐ[μ.restrict s] 0 :=
  by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖condexp_L2 ℝ hm f x‖₊ ∂μ = 0
  · rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero 
    refine' h_nnnorm_eq_zero.mono fun x hx => _
    dsimp only at hx 
    rw [Pi.zero_apply] at hx ⊢
    · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx 
    · refine' Measurable.coe_nnreal_ennreal (Measurable.nnnorm _)
      rw [Lp_meas_coe]
      exact (Lp.strongly_measurable _).Measurable
  refine' le_antisymm _ (zero_le _)
  refine' (lintegral_nnnorm_condexp_L2_le hs hμs f).trans (le_of_eq _)
  rw [lintegral_eq_zero_iff]
  · refine' hf.mono fun x hx => _
    dsimp only
    rw [hx]
    simp
  · exact (Lp.strongly_measurable _).ennnorm
#align measure_theory.condexp_L2_ae_eq_zero_of_ae_eq_zero MeasureTheory.condexpL2_ae_eq_zero_of_ae_eq_zero

theorem lintegral_nnnorm_condexpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ ≤ μ (s ∩ t) :=
  by
  refine' (lintegral_nnnorm_condexp_L2_le ht hμt _).trans (le_of_eq _)
  have h_eq :
    ∫⁻ x in t, ‖(indicator_const_Lp 2 hs hμs (1 : ℝ)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun x => (1 : ℝ≥0∞)) x ∂μ :=
    by
    refine' lintegral_congr_ae (ae_restrict_of_ae _)
    refine' (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono fun x hx => _
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, measure.restrict_apply]
#align measure_theory.lintegral_nnnorm_condexp_L2_indicator_le_real MeasureTheory.lintegral_nnnorm_condexpL2_indicator_le_real

end Real

/-- `condexp_L2` commutes with taking inner products with constants. See the lemma
`condexp_L2_comp_continuous_linear_map` for a more general result about commuting with continuous
linear maps. -/
theorem condexpL2_const_inner (hm : m ≤ m0) (f : Lp E 2 μ) (c : E) :
    condexpL2 𝕜 hm (((Lp.memℒp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ] fun a =>
      ⟪c, condexpL2 𝕜 hm f a⟫ :=
  by
  rw [Lp_meas_coe]
  have h_mem_Lp : mem_ℒp (fun a => ⟪c, condexp_L2 𝕜 hm f a⟫) 2 μ := by
    refine' mem_ℒp.const_inner _ _; rw [Lp_meas_coe]; exact Lp.mem_ℒp _
  have h_eq : h_mem_Lp.to_Lp _ =ᵐ[μ] fun a => ⟪c, condexp_L2 𝕜 hm f a⟫ := h_mem_Lp.coe_fn_to_Lp
  refine' eventually_eq.trans _ h_eq
  refine'
    Lp.ae_eq_of_forall_set_integral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
      (fun s hs hμs => integrable_on_condexp_L2_of_measure_ne_top hm hμs.Ne _) _ _ _ _
  · intro s hs hμs
    rw [integrable_on, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [← Lp_meas_coe, integral_condexp_L2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), Lp_meas_coe, ←
      L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 (↑(condexp_L2 𝕜 hm f)) (hm s hs) c hμs.ne,
      ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable,
      L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs)
        ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono fun x hx hxs => hx)]
  · rw [← Lp_meas_coe]; exact Lp_meas.ae_strongly_measurable' _
  · refine' ae_strongly_measurable'.congr _ h_eq.symm
    exact (Lp_meas.ae_strongly_measurable' _).const_inner _
#align measure_theory.condexp_L2_const_inner MeasureTheory.condexpL2_const_inner

/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condexpL2_eq (hm : m ≤ m0) (f : Lp E' 2 μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condexpL2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
  by
  rw [← sub_eq_zero, Lp_meas_coe, ←
    integral_sub' (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine' integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ _ _
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub (↑(condexp_L2 𝕜 hm f)) f).symm)]
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)
  rw [← Lp_meas_coe, sub_eq_zero, ←
    set_integral_congr_ae (hm s hs) ((condexp_L2_const_inner hm f c).mono fun x hx _ => hx), ←
    set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condexp_L2_eq_of_fin_meas_real _ hs hμs
#align measure_theory.integral_condexp_L2_eq MeasureTheory.integral_condexpL2_eq

variable {E'' 𝕜' : Type _} [IsROrC 𝕜'] [NormedAddCommGroup E''] [InnerProductSpace 𝕜' E'']
  [CompleteSpace E''] [NormedSpace ℝ E'']

variable (𝕜 𝕜')

theorem condexpL2_comp_continuousLinearMap (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condexpL2 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ] T.compLp (condexpL2 𝕜 hm f : α →₂[μ] E') :=
  by
  refine'
    Lp.ae_eq_of_forall_set_integral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
      (fun s hs hμs => integrable_on_condexp_L2_of_measure_ne_top hm hμs.Ne _)
      (fun s hs hμs => integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.Ne) _ _
      _
  · intro s hs hμs
    rw [T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm
        (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne),
      ← Lp_meas_coe, ← Lp_meas_coe, integral_condexp_L2_eq hm f hs hμs.ne,
      integral_condexp_L2_eq hm (T.comp_Lp f) hs hμs.ne, T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm
        (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · rw [← Lp_meas_coe]; exact Lp_meas.ae_strongly_measurable' _
  · have h_coe := T.coe_fn_comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E')
    rw [← eventually_eq] at h_coe 
    refine' ae_strongly_measurable'.congr _ h_coe.symm
    exact (Lp_meas.ae_strongly_measurable' (condexp_L2 𝕜 hm f)).continuous_comp T.continuous
#align measure_theory.condexp_L2_comp_continuous_linear_map MeasureTheory.condexpL2_comp_continuousLinearMap

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

theorem condexpL2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') :
    condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  by
  rw [indicator_const_Lp_eq_to_span_singleton_comp_Lp hs hμs x]
  have h_comp :=
    condexp_L2_comp_continuous_linear_map ℝ 𝕜 hm (to_span_singleton ℝ x)
      (indicator_const_Lp 2 hs hμs (1 : ℝ))
  rw [← Lp_meas_coe] at h_comp 
  refine' h_comp.trans _
  exact (to_span_singleton ℝ x).coeFn_compLp _
#align measure_theory.condexp_L2_indicator_ae_eq_smul MeasureTheory.condexpL2_indicator_ae_eq_smul

theorem condexpL2_indicator_eq_toSpanSingleton_comp (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') :
    (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
      (toSpanSingleton ℝ x).compLp (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) :=
  by
  ext1
  rw [← Lp_meas_coe]
  refine' (condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _
  have h_comp :=
    (to_span_singleton ℝ x).coeFn_compLp
      (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) : α →₂[μ] ℝ)
  rw [← eventually_eq] at h_comp 
  refine' eventually_eq.trans _ h_comp.symm
  refine' eventually_of_forall fun y => _
  rfl
#align measure_theory.condexp_L2_indicator_eq_to_span_singleton_comp MeasureTheory.condexpL2_indicator_eq_toSpanSingleton_comp

variable {𝕜}

theorem set_lintegral_nnnorm_condexpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a‖₊ ∂μ ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a‖₊ ∂μ =
        ∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x‖₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha hat => by rw [ha])
    _ = (∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ) * ‖x‖₊ :=
      by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.strongly_measurable _).ennnorm
    _ ≤ μ (s ∩ t) * ‖x‖₊ :=
      mul_le_mul_right' (lintegral_nnnorm_condexpL2_indicator_le_real hs hμs ht hμt) _
#align measure_theory.set_lintegral_nnnorm_condexp_L2_indicator_le MeasureTheory.set_lintegral_nnnorm_condexpL2_indicator_le

theorem lintegral_nnnorm_condexpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') [SigmaFinite (μ.trim hm)] :
    ∫⁻ a, ‖condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a‖₊ ∂μ ≤ μ s * ‖x‖₊ :=
  by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ fun t ht hμt => _
  · rw [Lp_meas_coe]
    exact (Lp.ae_strongly_measurable _).ennnorm
  refine' (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _
  exact mul_le_mul_right' (measure_mono (Set.inter_subset_left _ _)) _
#align measure_theory.lintegral_nnnorm_condexp_L2_indicator_le MeasureTheory.lintegral_nnnorm_condexpL2_indicator_le

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexpL2_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    Integrable (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ :=
  by
  refine'
    integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) (ENNReal.mul_lt_top hμs ENNReal.coe_ne_top) _
      _
  · rw [Lp_meas_coe]; exact Lp.ae_strongly_measurable _
  · refine' fun t ht hμt =>
      (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _
    exact mul_le_mul_right' (measure_mono (Set.inter_subset_left _ _)) _
#align measure_theory.integrable_condexp_L2_indicator MeasureTheory.integrable_condexpL2_indicator

end CondexpL2Indicator

section CondexpIndSmul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
noncomputable def condexpIndSmul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    Lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))
#align measure_theory.condexp_ind_smul MeasureTheory.condexpIndSmul

theorem aEStronglyMeasurable'_condexpIndSmul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : AEStronglyMeasurable' m (condexpIndSmul hm hs hμs x) μ :=
  by
  have h : ae_strongly_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ :=
    ae_strongly_measurable'_condexp_L2 _ _
  rw [condexp_ind_smul]
  suffices
    ae_strongly_measurable' m
      (to_span_singleton ℝ x ∘ condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ
    by
    refine' ae_strongly_measurable'.congr this _
    refine' eventually_eq.trans _ (coe_fn_comp_LpL _ _).symm
    rw [Lp_meas_coe]
  exact ae_strongly_measurable'.continuous_comp (to_span_singleton ℝ x).Continuous h
#align measure_theory.ae_strongly_measurable'_condexp_ind_smul MeasureTheory.aEStronglyMeasurable'_condexpIndSmul

theorem condexpIndSmul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndSmul hm hs hμs (x + y) = condexpIndSmul hm hs hμs x + condexpIndSmul hm hs hμs y := by
  simp_rw [condexp_ind_smul]; rw [to_span_singleton_add, add_comp_LpL, add_apply]
#align measure_theory.condexp_ind_smul_add MeasureTheory.condexpIndSmul_add

theorem condexpIndSmul_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  simp_rw [condexp_ind_smul]; rw [to_span_singleton_smul, smul_comp_LpL, smul_apply]
#align measure_theory.condexp_ind_smul_smul MeasureTheory.condexpIndSmul_smul

theorem condexpIndSmul_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  rw [condexp_ind_smul, condexp_ind_smul, to_span_singleton_smul',
    (to_span_singleton ℝ x).smul_compLpL c, smul_apply]
#align measure_theory.condexp_ind_smul_smul' MeasureTheory.condexpIndSmul_smul'

theorem condexpIndSmul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndSmul hm hs hμs x =ᵐ[μ] fun a =>
      condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  (toSpanSingleton ℝ x).coeFn_compLpL _
#align measure_theory.condexp_ind_smul_ae_eq_smul MeasureTheory.condexpIndSmul_ae_eq_smul

theorem set_lintegral_nnnorm_condexpIndSmul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x‖₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexpIndSmul_ae_eq_smul hm hs hμs x).mono fun a ha hat => by rw [ha])
    _ = (∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ) * ‖x‖₊ :=
      by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.strongly_measurable _).ennnorm
    _ ≤ μ (s ∩ t) * ‖x‖₊ :=
      mul_le_mul_right' (lintegral_nnnorm_condexpL2_indicator_le_real hs hμs ht hμt) _
#align measure_theory.set_lintegral_nnnorm_condexp_ind_smul_le MeasureTheory.set_lintegral_nnnorm_condexpIndSmul_le

theorem lintegral_nnnorm_condexpIndSmul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ ≤ μ s * ‖x‖₊ :=
  by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ fun t ht hμt => _
  · exact (Lp.ae_strongly_measurable _).ennnorm
  refine' (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _
  exact mul_le_mul_right' (measure_mono (Set.inter_subset_left _ _)) _
#align measure_theory.lintegral_nnnorm_condexp_ind_smul_le MeasureTheory.lintegral_nnnorm_condexpIndSmul_le

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexpIndSmul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : Integrable (condexpIndSmul hm hs hμs x) μ :=
  by
  refine'
    integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) (ENNReal.mul_lt_top hμs ENNReal.coe_ne_top) _
      _
  · exact Lp.ae_strongly_measurable _
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _
    exact mul_le_mul_right' (measure_mono (Set.inter_subset_left _ _)) _
#align measure_theory.integrable_condexp_ind_smul MeasureTheory.integrable_condexpIndSmul

theorem condexpIndSmul_empty {x : G} :
    condexpIndSmul hm MeasurableSet.empty ((@measure_empty _ _ μ).le.trans_lt ENNReal.coe_lt_top).Ne
        x =
      0 :=
  by
  rw [condexp_ind_smul, indicator_const_empty]
  simp only [coeFn_coeBase, Submodule.coe_zero, ContinuousLinearMap.map_zero]
#align measure_theory.condexp_ind_smul_empty MeasureTheory.condexpIndSmul_empty

theorem set_integral_condexpL2_indicator (hs : measurable_set[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    ∫ x in s, (condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ))) x ∂μ = (μ (t ∩ s)).toReal :=
  calc
    ∫ x in s, (condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ))) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : ℝ) x ∂μ :=
      @integral_condexpL2_eq α _ ℝ _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) hs hμs
    _ = (μ (t ∩ s)).toReal • 1 := (set_integral_indicatorConstLp (hm s hs) ht hμt (1 : ℝ))
    _ = (μ (t ∩ s)).toReal := by rw [smul_eq_mul, mul_one]
#align measure_theory.set_integral_condexp_L2_indicator MeasureTheory.set_integral_condexpL2_indicator

theorem set_integral_condexpIndSmul (hs : measurable_set[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (x : G') :
    ∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ =
        ∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a • x ∂μ :=
      set_integral_congr_ae (hm s hs)
        ((condexpIndSmul_ae_eq_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = (μ (t ∩ s)).toReal • x := by rw [set_integral_condexp_L2_indicator hs ht hμs hμt]
#align measure_theory.set_integral_condexp_ind_smul MeasureTheory.set_integral_condexpIndSmul

theorem condexpL2_indicator_nonneg (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    [SigmaFinite (μ.trim hm)] : 0 ≤ᵐ[μ] condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) :=
  by
  have h : ae_strongly_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ :=
    ae_strongly_measurable'_condexp_L2 _ _
  refine' eventually_le.trans_eq _ h.ae_eq_mk.symm
  refine' @ae_le_of_ae_le_trim _ _ _ _ _ _ hm _ _ _
  refine' ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite _ _
  · intro t ht hμt
    refine' @integrable.integrable_on _ _ m _ _ _ _ _
    refine' integrable.trim hm _ _
    · rw [integrable_congr h.ae_eq_mk.symm]
      exact integrable_condexp_L2_indicator hm hs hμs _
    · exact h.strongly_measurable_mk
  · intro t ht hμt
    rw [← set_integral_trim hm h.strongly_measurable_mk ht]
    have h_ae :
      ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) x :=
      by
      filter_upwards [h.ae_eq_mk] with x hx
      exact fun _ => hx.symm
    rw [set_integral_congr_ae (hm t ht) h_ae,
      set_integral_condexp_L2_indicator ht hs ((le_trim hm).trans_lt hμt).Ne hμs]
    exact ENNReal.toReal_nonneg
#align measure_theory.condexp_L2_indicator_nonneg MeasureTheory.condexpL2_indicator_nonneg

theorem condexpIndSmul_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    0 ≤ᵐ[μ] condexpIndSmul hm hs hμs x :=
  by
  refine' eventually_le.trans_eq _ (condexp_ind_smul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condexp_L2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx
#align measure_theory.condexp_ind_smul_nonneg MeasureTheory.condexpIndSmul_nonneg

end CondexpIndSmul

end MeasureTheory


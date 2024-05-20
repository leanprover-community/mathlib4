/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.L2Space

#align_import measure_theory.function.conditional_expectation.condexp_L2 from "leanprover-community/mathlib"@"d8bbb04e2d2a44596798a9207ceefc0fb236e41e"

/-! # Conditional expectation in L2

This file contains one step of the construction of the conditional expectation, which is completed
in `MeasureTheory.Function.ConditionalExpectation.Basic`. See that file for a description of the
full process.

We build the conditional expectation of an `L²` function, as an element of `L²`. This is the
orthogonal projection on the subspace of almost everywhere `m`-measurable functions.

## Main definitions

* `condexpL2`: Conditional expectation of a function in L2 with respect to a sigma-algebra: it is
the orthogonal projection on the subspace `lpMeas`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : RCLike`:
* `condexpL2` is defined only for an `InnerProductSpace` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `NormedSpace 𝕜 F`.

-/

set_option linter.uppercaseLean3 false

open TopologicalSpace Filter ContinuousLinearMap

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E E' F G G' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
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

-- Porting note: the argument `E` of `condexpL2` is not automatically filled in Lean 4.
-- To avoid typing `(E := _)` every time it is made explicit.
variable (E 𝕜)

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
noncomputable def condexpL2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] lpMeas E 𝕜 m 2 μ :=
  @orthogonalProjection 𝕜 (α →₂[μ] E) _ _ _ (lpMeas E 𝕜 m 2 μ)
    haveI : Fact (m ≤ m0) := ⟨hm⟩
    inferInstance
#align measure_theory.condexp_L2 MeasureTheory.condexpL2

variable {E 𝕜}

theorem aeStronglyMeasurable'_condexpL2 (hm : m ≤ m0) (f : α →₂[μ] E) :
    AEStronglyMeasurable' (β := E) m (condexpL2 E 𝕜 hm f) μ :=
  lpMeas.aeStronglyMeasurable' _
#align measure_theory.ae_strongly_measurable'_condexp_L2 MeasureTheory.aeStronglyMeasurable'_condexpL2

theorem integrableOn_condexpL2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (E := E) (condexpL2 E 𝕜 hm f) s μ :=
  integrableOn_Lp_of_measure_ne_top (condexpL2 E 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim
    hμs
#align measure_theory.integrable_on_condexp_L2_of_measure_ne_top MeasureTheory.integrableOn_condexpL2_of_measure_ne_top

theorem integrable_condexpL2_of_isFiniteMeasure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (β := E) (condexpL2 E 𝕜 hm f) μ :=
  integrableOn_univ.mp <| integrableOn_condexpL2_of_measure_ne_top hm (measure_ne_top _ _) f
#align measure_theory.integrable_condexp_L2_of_is_finite_measure MeasureTheory.integrable_condexpL2_of_isFiniteMeasure

theorem norm_condexpL2_le_one (hm : m ≤ m0) : ‖@condexpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ ≤ 1 :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  orthogonalProjection_norm_le _
#align measure_theory.norm_condexp_L2_le_one MeasureTheory.norm_condexpL2_le_one

theorem norm_condexpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ‖condexpL2 E 𝕜 hm f‖ ≤ ‖f‖ :=
  ((@condexpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condexpL2_le_one hm))
#align measure_theory.norm_condexp_L2_le MeasureTheory.norm_condexpL2_le

theorem snorm_condexpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    snorm (F := E) (condexpL2 E 𝕜 hm f) 2 μ ≤ snorm f 2 μ := by
  rw [lpMeas_coe, ← ENNReal.toReal_le_toReal (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ←
    Lp.norm_def, ← Lp.norm_def, Submodule.norm_coe]
  exact norm_condexpL2_le hm f
#align measure_theory.snorm_condexp_L2_le MeasureTheory.snorm_condexpL2_le

theorem norm_condexpL2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖(condexpL2 E 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, ← lpMeas_coe]
  refine' (ENNReal.toReal_le_toReal _ (Lp.snorm_ne_top _)).mpr (snorm_condexpL2_le hm f)
  exact Lp.snorm_ne_top _
#align measure_theory.norm_condexp_L2_coe_le MeasureTheory.norm_condexpL2_coe_le

theorem inner_condexpL2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condexpL2 E 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, (condexpL2 E 𝕜 hm g : α →₂[μ] E)⟫₂ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  inner_orthogonalProjection_left_eq_right _ f g
#align measure_theory.inner_condexp_L2_left_eq_right MeasureTheory.inner_condexpL2_left_eq_right

theorem condexpL2_indicator_of_measurable (hm : m ≤ m0) (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞)
    (c : E) :
    (condexpL2 E 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) =
      indicatorConstLp 2 (hm s hs) hμs c := by
  rw [condexpL2]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c ∈ lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := rfl
  have h_orth_mem := orthogonalProjection_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]
#align measure_theory.condexp_L2_indicator_of_measurable MeasureTheory.condexpL2_indicator_of_measurable

theorem inner_condexpL2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable' m g μ) :
    ⟪(condexpL2 E 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ := by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condexpL2]
  simp only [mem_lpMeas_iff_aeStronglyMeasurable'.mpr hg, orthogonalProjection_inner_eq_zero f g]
#align measure_theory.inner_condexp_L2_eq_inner_fun MeasureTheory.inner_condexpL2_eq_inner_fun

section Real

variable {hm : m ≤ m0}  -- should assumption really be implicit?

theorem integral_condexpL2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, (condexpL2 𝕜 𝕜 hm f : α → 𝕜) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hm s hs) hμs f]
  have h_eq_inner : ∫ x in s, (condexpL2 𝕜 𝕜 hm f : α → 𝕜) x ∂μ =
      inner (indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜)) (condexpL2 𝕜 𝕜 hm f) := by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
  rw [h_eq_inner, ← inner_condexpL2_left_eq_right, condexpL2_indicator_of_measurable hm hs hμs]
#align measure_theory.integral_condexp_L2_eq_of_fin_meas_real MeasureTheory.integral_condexpL2_eq_of_fin_meas_real

theorem lintegral_nnnorm_condexpL2_le (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (f : Lp ℝ 2 μ) :
    ∫⁻ x in s, ‖(condexpL2 ℝ ℝ hm f : α → ℝ) x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ := by
  let h_meas := lpMeas.aeStronglyMeasurable' (condexpL2 ℝ ℝ hm f)
  let g := h_meas.choose
  have hg_meas : StronglyMeasurable[m] g := h_meas.choose_spec.1
  have hg_eq : g =ᵐ[μ] condexpL2 ℝ ℝ hm f := h_meas.choose_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexpL2 ℝ ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x =>
      (‖(condexpL2 ℝ ℝ hm f : α → ℝ) x‖₊ : ℝ≥0∞) := by
    refine' hg_eq_restrict.mono fun x hx => _
    dsimp only
    simp_rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine'
    lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (Lp.stronglyMeasurable f) _ _ _ _ hs hμs
  · exact integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOn_condexpL2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condexpL2_eq_of_fin_meas_real (hm := hm) f ht hμt.ne]
    exact setIntegral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)
#align measure_theory.lintegral_nnnorm_condexp_L2_le MeasureTheory.lintegral_nnnorm_condexpL2_le

theorem condexpL2_ae_eq_zero_of_ae_eq_zero (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) {f : Lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condexpL2 ℝ ℝ hm f =ᵐ[μ.restrict s] (0 : α → ℝ) := by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖(condexpL2 ℝ ℝ hm f : α → ℝ) x‖₊ ∂μ = 0 by
    rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    · refine' h_nnnorm_eq_zero.mono fun x hx => _
      dsimp only at hx
      rw [Pi.zero_apply] at hx ⊢
      · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine' Measurable.coe_nnreal_ennreal (Measurable.nnnorm _)
      rw [lpMeas_coe]
      exact (Lp.stronglyMeasurable _).measurable
  refine' le_antisymm _ (zero_le _)
  refine' (lintegral_nnnorm_condexpL2_le hs hμs f).trans (le_of_eq _)
  rw [lintegral_eq_zero_iff]
  · refine' hf.mono fun x hx => _
    dsimp only
    rw [hx]
    simp
  · exact (Lp.stronglyMeasurable _).ennnorm
#align measure_theory.condexp_L2_ae_eq_zero_of_ae_eq_zero MeasureTheory.condexpL2_ae_eq_zero_of_ae_eq_zero

theorem lintegral_nnnorm_condexpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖(condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ ≤ μ (s ∩ t) := by
  refine' (lintegral_nnnorm_condexpL2_le ht hμt _).trans (le_of_eq _)
  have h_eq :
    ∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : ℝ)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
    refine' lintegral_congr_ae (ae_restrict_of_ae _)
    refine' (@indicatorConstLp_coeFn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono fun x hx => _
    dsimp only
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]
#align measure_theory.lintegral_nnnorm_condexp_L2_indicator_le_real MeasureTheory.lintegral_nnnorm_condexpL2_indicator_le_real

end Real

/-- `condexpL2` commutes with taking inner products with constants. See the lemma
`condexpL2_comp_continuousLinearMap` for a more general result about commuting with continuous
linear maps. -/
theorem condexpL2_const_inner (hm : m ≤ m0) (f : Lp E 2 μ) (c : E) :
    condexpL2 𝕜 𝕜 hm (((Lp.memℒp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ]
    fun a => ⟪c, (condexpL2 E 𝕜 hm f : α → E) a⟫ := by
  rw [lpMeas_coe]
  have h_mem_Lp : Memℒp (fun a => ⟪c, (condexpL2 E 𝕜 hm f : α → E) a⟫) 2 μ := by
    refine' Memℒp.const_inner _ _; rw [lpMeas_coe]; exact Lp.memℒp _
  have h_eq : h_mem_Lp.toLp _ =ᵐ[μ] fun a => ⟪c, (condexpL2 E 𝕜 hm f : α → E) a⟫ :=
    h_mem_Lp.coeFn_toLp
  refine' EventuallyEq.trans _ h_eq
  refine' Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condexpL2_of_measure_ne_top hm hμs.ne _) _ _ _ _
  · intro s _ hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOn_condexpL2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [← lpMeas_coe, integral_condexpL2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), lpMeas_coe, ←
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 (↑(condexpL2 E 𝕜 hm f)) (hm s hs) c hμs.ne,
      ← inner_condexpL2_left_eq_right, condexpL2_indicator_of_measurable _ hs,
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 f (hm s hs) c hμs.ne,
      setIntegral_congr_ae (hm s hs)
        ((Memℒp.coeFn_toLp ((Lp.memℒp f).const_inner c)).mono fun x hx _ => hx)]
  · rw [← lpMeas_coe]; exact lpMeas.aeStronglyMeasurable' _
  · refine' AEStronglyMeasurable'.congr _ h_eq.symm
    exact (lpMeas.aeStronglyMeasurable' _).const_inner _
#align measure_theory.condexp_L2_const_inner MeasureTheory.condexpL2_const_inner

/-- `condexpL2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condexpL2_eq (hm : m ≤ m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, (condexpL2 E' 𝕜 hm f : α → E') x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← sub_eq_zero, lpMeas_coe, ←
    integral_sub' (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine' integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ _ _
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub (↑(condexpL2 E' 𝕜 hm f)) f).symm)]
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := Memℒp.coeFn_toLp (E := 𝕜) ((Lp.memℒp f).const_inner c)
  rw [← lpMeas_coe, sub_eq_zero, ←
    setIntegral_congr_ae (hm s hs) ((condexpL2_const_inner hm f c).mono fun x hx _ => hx), ←
    setIntegral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condexpL2_eq_of_fin_meas_real _ hs hμs
#align measure_theory.integral_condexp_L2_eq MeasureTheory.integral_condexpL2_eq

variable {E'' 𝕜' : Type*} [RCLike 𝕜'] [NormedAddCommGroup E''] [InnerProductSpace 𝕜' E'']
  [CompleteSpace E''] [NormedSpace ℝ E'']

variable (𝕜 𝕜')

theorem condexpL2_comp_continuousLinearMap (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condexpL2 E'' 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ]
    T.compLp (condexpL2 E' 𝕜 hm f : α →₂[μ] E') := by
  refine' Lp.ae_eq_of_forall_setIntegral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condexpL2_of_measure_ne_top hm hμs.ne _) (fun s _ hμs =>
      integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) _ _ _
  · intro s hs hμs
    rw [T.setIntegral_compLp _ (hm s hs),
      T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne),
      ← lpMeas_coe, ← lpMeas_coe, integral_condexpL2_eq hm f hs hμs.ne,
      integral_condexpL2_eq hm (T.compLp f) hs hμs.ne, T.setIntegral_compLp _ (hm s hs),
      T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · rw [← lpMeas_coe]; exact lpMeas.aeStronglyMeasurable' _
  · have h_coe := T.coeFn_compLp (condexpL2 E' 𝕜 hm f : α →₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine' AEStronglyMeasurable'.congr _ h_coe.symm
    exact (lpMeas.aeStronglyMeasurable' (condexpL2 E' 𝕜 hm f)).continuous_comp T.continuous
#align measure_theory.condexp_L2_comp_continuous_linear_map MeasureTheory.condexpL2_comp_continuousLinearMap

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

theorem condexpL2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') :
    condexpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) : α → ℝ) a • x := by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condexpL2_comp_continuousLinearMap ℝ 𝕜 hm (toSpanSingleton ℝ x)
      (indicatorConstLp 2 hs hμs (1 : ℝ))
  rw [← lpMeas_coe] at h_comp
  refine' h_comp.trans _
  exact (toSpanSingleton ℝ x).coeFn_compLp _
#align measure_theory.condexp_L2_indicator_ae_eq_smul MeasureTheory.condexpL2_indicator_ae_eq_smul

theorem condexpL2_indicator_eq_toSpanSingleton_comp (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') : (condexpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
    (toSpanSingleton ℝ x).compLp (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1)) := by
  ext1
  rw [← lpMeas_coe]
  refine' (condexpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _
  have h_comp := (toSpanSingleton ℝ x).coeFn_compLp
    (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α →₂[μ] ℝ)
  rw [← EventuallyEq] at h_comp
  refine' EventuallyEq.trans _ h_comp.symm
  filter_upwards with y using rfl
#align measure_theory.condexp_L2_indicator_eq_to_span_singleton_comp MeasureTheory.condexpL2_indicator_eq_toSpanSingleton_comp

variable {𝕜}

theorem set_lintegral_nnnorm_condexpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖(condexpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ ≤
    μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖(condexpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x‖₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const, lpMeas_coe]
      exact (Lp.stronglyMeasurable _).ennnorm
    _ ≤ μ (s ∩ t) * ‖x‖₊ :=
      mul_le_mul_right' (lintegral_nnnorm_condexpL2_indicator_le_real hs hμs ht hμt) _
#align measure_theory.set_lintegral_nnnorm_condexp_L2_indicator_le MeasureTheory.set_lintegral_nnnorm_condexpL2_indicator_le

theorem lintegral_nnnorm_condexpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') [SigmaFinite (μ.trim hm)] :
    ∫⁻ a, ‖(condexpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ ≤ μ s * ‖x‖₊ := by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ fun t ht hμt => _
  · rw [lpMeas_coe]
    exact (Lp.aestronglyMeasurable _).ennnorm
  refine' (set_lintegral_nnnorm_condexpL2_indicator_le hm hs hμs x ht hμt).trans _
  gcongr
  apply Set.inter_subset_left
#align measure_theory.lintegral_nnnorm_condexp_L2_indicator_le MeasureTheory.lintegral_nnnorm_condexpL2_indicator_le

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexpL2_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    Integrable (β := E') (condexpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ := by
  refine' integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs ENNReal.coe_ne_top) _ _
  · rw [lpMeas_coe]; exact Lp.aestronglyMeasurable _
  · refine' fun t ht hμt =>
      (set_lintegral_nnnorm_condexpL2_indicator_le hm hs hμs x ht hμt).trans _
    gcongr
    apply Set.inter_subset_left
#align measure_theory.integrable_condexp_L2_indicator MeasureTheory.integrable_condexpL2_indicator

end CondexpL2Indicator

section CondexpIndSMul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
noncomputable def condexpIndSMul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    Lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))
#align measure_theory.condexp_ind_smul MeasureTheory.condexpIndSMul

theorem aeStronglyMeasurable'_condexpIndSMul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : AEStronglyMeasurable' m (condexpIndSMul hm hs hμs x) μ := by
  have h : AEStronglyMeasurable' m (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) μ :=
    aeStronglyMeasurable'_condexpL2 _ _
  rw [condexpIndSMul]
  suffices AEStronglyMeasurable' m
      (toSpanSingleton ℝ x ∘ condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1)) μ by
    refine' AEStronglyMeasurable'.congr this _
    refine' EventuallyEq.trans _ (coeFn_compLpL _ _).symm
    rfl
  exact AEStronglyMeasurable'.continuous_comp (toSpanSingleton ℝ x).continuous h
#align measure_theory.ae_strongly_measurable'_condexp_ind_smul MeasureTheory.aeStronglyMeasurable'_condexpIndSMul

theorem condexpIndSMul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndSMul hm hs hμs (x + y) = condexpIndSMul hm hs hμs x + condexpIndSMul hm hs hμs y := by
  simp_rw [condexpIndSMul]; rw [toSpanSingleton_add, add_compLpL, add_apply]
#align measure_theory.condexp_ind_smul_add MeasureTheory.condexpIndSMul_add

theorem condexpIndSMul_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndSMul hm hs hμs (c • x) = c • condexpIndSMul hm hs hμs x := by
  simp_rw [condexpIndSMul]; rw [toSpanSingleton_smul, smul_compLpL, smul_apply]
#align measure_theory.condexp_ind_smul_smul MeasureTheory.condexpIndSMul_smul

theorem condexpIndSMul_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndSMul hm hs hμs (c • x) = c • condexpIndSMul hm hs hμs x := by
  rw [condexpIndSMul, condexpIndSMul, toSpanSingleton_smul',
    (toSpanSingleton ℝ x).smul_compLpL c, smul_apply]
#align measure_theory.condexp_ind_smul_smul' MeasureTheory.condexpIndSMul_smul'

theorem condexpIndSMul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndSMul hm hs hμs x =ᵐ[μ] fun a =>
      (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x :=
  (toSpanSingleton ℝ x).coeFn_compLpL _
#align measure_theory.condexp_ind_smul_ae_eq_smul MeasureTheory.condexpIndSMul_ae_eq_smul

theorem set_lintegral_nnnorm_condexpIndSMul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ‖condexpIndSMul hm hs hμs x a‖₊ ∂μ) ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖condexpIndSMul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x‖₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const, lpMeas_coe]
      exact (Lp.stronglyMeasurable _).ennnorm
    _ ≤ μ (s ∩ t) * ‖x‖₊ :=
      mul_le_mul_right' (lintegral_nnnorm_condexpL2_indicator_le_real hs hμs ht hμt) _
#align measure_theory.set_lintegral_nnnorm_condexp_ind_smul_le MeasureTheory.set_lintegral_nnnorm_condexpIndSMul_le

theorem lintegral_nnnorm_condexpIndSMul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖condexpIndSMul hm hs hμs x a‖₊ ∂μ ≤ μ s * ‖x‖₊ := by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ fun t ht hμt => _
  · exact (Lp.aestronglyMeasurable _).ennnorm
  refine' (set_lintegral_nnnorm_condexpIndSMul_le hm hs hμs x ht hμt).trans _
  gcongr
  apply Set.inter_subset_left
#align measure_theory.lintegral_nnnorm_condexp_ind_smul_le MeasureTheory.lintegral_nnnorm_condexpIndSMul_le

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : Integrable (condexpIndSMul hm hs hμs x) μ := by
  refine'
    integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) (ENNReal.mul_lt_top hμs ENNReal.coe_ne_top) _
      _
  · exact Lp.aestronglyMeasurable _
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexpIndSMul_le hm hs hμs x ht hμt).trans _
    gcongr
    apply Set.inter_subset_left
#align measure_theory.integrable_condexp_ind_smul MeasureTheory.integrable_condexpIndSMul

theorem condexpIndSMul_empty {x : G} : condexpIndSMul hm MeasurableSet.empty
    ((measure_empty (μ := μ)).le.trans_lt ENNReal.coe_lt_top).ne x = 0 := by
  rw [condexpIndSMul, indicatorConstLp_empty]
  simp only [Submodule.coe_zero, ContinuousLinearMap.map_zero]
#align measure_theory.condexp_ind_smul_empty MeasureTheory.condexpIndSMul_empty

theorem setIntegral_condexpL2_indicator (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    ∫ x in s, (condexpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) x ∂μ = (μ (t ∩ s)).toReal :=
  calc
    ∫ x in s, (condexpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : ℝ) x ∂μ :=
      @integral_condexpL2_eq α _ ℝ _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) hs hμs
    _ = (μ (t ∩ s)).toReal • (1 : ℝ) := setIntegral_indicatorConstLp (hm s hs) ht hμt 1
    _ = (μ (t ∩ s)).toReal := by rw [smul_eq_mul, mul_one]
#align measure_theory.set_integral_condexp_L2_indicator MeasureTheory.setIntegral_condexpL2_indicator

@[deprecated]
alias set_integral_condexpL2_indicator :=
  setIntegral_condexpL2_indicator -- deprecated on 2024-04-17

theorem setIntegral_condexpIndSMul (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (x : G') :
    ∫ a in s, (condexpIndSMul hm ht hμt x) a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, (condexpIndSMul hm ht hμt x) a ∂μ =
        ∫ a in s, (condexpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) a • x ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condexpIndSMul_ae_eq_smul hm ht hμt x).mono fun x hx _ => hx)
    _ = (∫ a in s, (condexpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = (μ (t ∩ s)).toReal • x := by rw [setIntegral_condexpL2_indicator hs ht hμs hμt]
#align measure_theory.set_integral_condexp_ind_smul MeasureTheory.setIntegral_condexpIndSMul

@[deprecated]
alias set_integral_condexpIndSMul :=
  setIntegral_condexpIndSMul -- deprecated on 2024-04-17

theorem condexpL2_indicator_nonneg (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    [SigmaFinite (μ.trim hm)] : (0 : α → ℝ) ≤ᵐ[μ]
    condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) := by
  have h : AEStronglyMeasurable' m (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) μ :=
    aeStronglyMeasurable'_condexpL2 _ _
  refine' EventuallyLE.trans_eq _ h.ae_eq_mk.symm
  refine' @ae_le_of_ae_le_trim _ _ _ _ _ _ hm (0 : α → ℝ) _ _
  refine' ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite _ _
  · rintro t - -
    refine @Integrable.integrableOn _ _ m _ _ _ _ ?_
    refine' Integrable.trim hm _ _
    · rw [integrable_congr h.ae_eq_mk.symm]
      exact integrable_condexpL2_indicator hm hs hμs _
    · exact h.stronglyMeasurable_mk
  · intro t ht hμt
    rw [← setIntegral_trim hm h.stronglyMeasurable_mk ht]
    have h_ae :
      ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = (condexpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) x := by
      filter_upwards [h.ae_eq_mk] with x hx
      exact fun _ => hx.symm
    rw [setIntegral_congr_ae (hm t ht) h_ae,
      setIntegral_condexpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact ENNReal.toReal_nonneg
#align measure_theory.condexp_L2_indicator_nonneg MeasureTheory.condexpL2_indicator_nonneg

theorem condexpIndSMul_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    (0 : α → E) ≤ᵐ[μ] condexpIndSMul hm hs hμs x := by
  refine' EventuallyLE.trans_eq _ (condexpIndSMul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condexpL2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx
#align measure_theory.condexp_ind_smul_nonneg MeasureTheory.condexpIndSMul_nonneg

end CondexpIndSMul

end MeasureTheory

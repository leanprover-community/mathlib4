/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Conditional expectation in L2

This file contains one step of the construction of the conditional expectation, which is completed
in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

We build the conditional expectation of an `L²` function, as an element of `L²`. This is the
orthogonal projection on the subspace of almost everywhere `m`-measurable functions.

## Main definitions

* `condExpL2`: Conditional expectation of a function in L2 with respect to a sigma-algebra: it is
  the orthogonal projection on the subspace `lpMeas`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : RCLike`:
* `condExpL2` is defined only for an `InnerProductSpace` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `NormedSpace 𝕜 F`.

-/

@[expose] public section


open TopologicalSpace Filter ContinuousLinearMap

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E E' F G G' 𝕜 : Type*} [RCLike 𝕜]
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

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (E 𝕜)

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
noncomputable def condExpL2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] lpMeas E 𝕜 m 2 μ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  (lpMeas E 𝕜 m 2 μ).orthogonalProjection

variable {E 𝕜}

theorem aestronglyMeasurable_condExpL2 (hm : m ≤ m0) (f : α →₂[μ] E) :
    AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm f : α → E) μ :=
  lpMeas.aestronglyMeasurable _

theorem integrableOn_condExpL2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (ε := E) (condExpL2 E 𝕜 hm f) s μ :=
  integrableOn_Lp_of_measure_ne_top (condExpL2 E 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim
    hμs

theorem integrable_condExpL2_of_isFiniteMeasure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (ε := E) (condExpL2 E 𝕜 hm f) μ :=
  integrableOn_univ.mp <| integrableOn_condExpL2_of_measure_ne_top hm (measure_ne_top _ _) f

theorem norm_condExpL2_le_one (hm : m ≤ m0) : ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ ≤ 1 :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  Submodule.orthogonalProjection_norm_le _

theorem norm_condExpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ‖condExpL2 E 𝕜 hm f‖ ≤ ‖f‖ :=
  ((@condExpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condExpL2_le_one hm))

theorem eLpNorm_condExpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    eLpNorm (ε := E) (condExpL2 E 𝕜 hm f) 2 μ ≤ eLpNorm f 2 μ := by
  rw [← ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ←
    Lp.norm_def, ← Lp.norm_def, Submodule.norm_coe]
  exact norm_condExpL2_le hm f

theorem norm_condExpL2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖(condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_condExpL2_le hm f)

theorem inner_condExpL2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condExpL2 E 𝕜 hm f : α →₂[μ] E), g⟫ = ⟪f, (condExpL2 E 𝕜 hm g : α →₂[μ] E)⟫ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  Submodule.inner_starProjection_left_eq_right _ f g

theorem condExpL2_indicator_of_measurable (hm : m ≤ m0) (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞)
    (c : E) :
    (condExpL2 E 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) =
      indicatorConstLp 2 (hm s hs) hμs c := by
  rw [condExpL2]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c ∈ lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := rfl
  have h_orth_mem := Submodule.orthogonalProjection_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]

theorem inner_condExpL2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    ⟪(condExpL2 E 𝕜 hm f : α →₂[μ] E), g⟫ = ⟪f, g⟫ := by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condExpL2]
  simp only [← Submodule.starProjection_apply,
    mem_lpMeas_iff_aestronglyMeasurable.mpr hg,
    Submodule.starProjection_inner_eq_zero f g]

section Real

variable {hm : m ≤ m0}

theorem integral_condExpL2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α → 𝕜) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hm s hs) hμs f]
  have h_eq_inner : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α → 𝕜) x ∂μ =
      ⟪indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜), condExpL2 𝕜 𝕜 hm f⟫ := by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
  rw [h_eq_inner, ← inner_condExpL2_left_eq_right, condExpL2_indicator_of_measurable hm hs hμs]

theorem lintegral_nnnorm_condExpL2_le (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (f : Lp ℝ 2 μ) :
    ∫⁻ x in s, ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ := by
  let h_meas := lpMeas.aestronglyMeasurable (condExpL2 ℝ ℝ hm f)
  let g := h_meas.choose
  have hg_meas : StronglyMeasurable[m] g := h_meas.choose_spec.1
  have hg_eq : g =ᵐ[μ] condExpL2 ℝ ℝ hm f := h_meas.choose_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condExpL2 ℝ ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x =>
      (‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖₊ : ℝ≥0∞) := by
    refine hg_eq_restrict.mono fun x hx => ?_
    dsimp only
    simp_rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine lintegral_enorm_le_of_forall_fin_meas_integral_eq
    hm (Lp.stronglyMeasurable f) ?_ ?_ ?_ ?_ hs hμs
  · exact integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOn_condExpL2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condExpL2_eq_of_fin_meas_real (hm := hm) f ht hμt.ne]
    exact setIntegral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)

theorem condExpL2_ae_eq_zero_of_ae_eq_zero (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) {f : Lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condExpL2 ℝ ℝ hm f =ᵐ[μ.restrict s] (0 : α → ℝ) := by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖₊ ∂μ = 0 by
    rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    · refine h_nnnorm_eq_zero.mono fun x hx => ?_
      dsimp only at hx
      rw [Pi.zero_apply] at hx ⊢
      · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine Measurable.coe_nnreal_ennreal (Measurable.nnnorm ?_)
      exact (Lp.stronglyMeasurable _).measurable
  refine le_antisymm ?_ (zero_le _)
  refine (lintegral_nnnorm_condExpL2_le hs hμs f).trans (le_of_eq ?_)
  rw [lintegral_eq_zero_iff]
  · refine hf.mono fun x hx => ?_
    dsimp only
    rw [hx]
    simp
  · exact (Lp.stronglyMeasurable _).enorm (ε := ℝ)

theorem lintegral_nnnorm_condExpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ ≤ μ (s ∩ t) := by
  refine (lintegral_nnnorm_condExpL2_le ht hμt _).trans (le_of_eq ?_)
  have h_eq :
    ∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : ℝ)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    refine (@indicatorConstLp_coeFn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono fun x hx => ?_
    dsimp only
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq, lintegral_indicator hs, lintegral_const, Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]

end Real

/-- `condExpL2` commutes with taking inner products with constants. See the lemma
`condExpL2_comp_continuousLinearMap` for a more general result about commuting with continuous
linear maps. -/
theorem condExpL2_const_inner (hm : m ≤ m0) (f : Lp E 2 μ) (c : E) :
    condExpL2 𝕜 𝕜 hm (((Lp.memLp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ]
    fun a => ⟪c, (condExpL2 E 𝕜 hm f : α → E) a⟫ := by
  have h_mem_Lp : MemLp (fun a => ⟪c, (condExpL2 E 𝕜 hm f : α → E) a⟫) 2 μ := by
    refine MemLp.const_inner _ ?_; exact Lp.memLp _
  have h_eq : h_mem_Lp.toLp _ =ᵐ[μ] fun a => ⟪c, (condExpL2 E 𝕜 hm f : α → E) a⟫ :=
    h_mem_Lp.coeFn_toLp
  refine EventuallyEq.trans ?_ h_eq
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) ?_ ?_ ?_ ?_
  · intro s _ hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [integral_condExpL2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), ←
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 (↑(condExpL2 E 𝕜 hm f)) (hm s hs) c hμs.ne,
      ← inner_condExpL2_left_eq_right, condExpL2_indicator_of_measurable _ hs,
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 f (hm s hs) c hμs.ne,
      setIntegral_congr_ae (hm s hs)
        ((MemLp.coeFn_toLp ((Lp.memLp f).const_inner c)).mono fun x hx _ => hx)]
  · exact lpMeas.aestronglyMeasurable _
  · refine AEStronglyMeasurable.congr ?_ h_eq.symm
    exact (lpMeas.aestronglyMeasurable _).const_inner

/-- `condExpL2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condExpL2_eq (hm : m ≤ m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, (condExpL2 E' 𝕜 hm f : α → E') x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← sub_eq_zero, ←
    integral_sub' (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ ?_ ?_
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub (↑(condExpL2 E' 𝕜 hm f)) f).symm)]
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := MemLp.coeFn_toLp (E := 𝕜) ((Lp.memLp f).const_inner c)
  rw [sub_eq_zero, ←
    setIntegral_congr_ae (hm s hs) ((condExpL2_const_inner hm f c).mono fun x hx _ => hx), ←
    setIntegral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condExpL2_eq_of_fin_meas_real _ hs hμs

variable {E'' 𝕜' : Type*} [RCLike 𝕜'] [NormedAddCommGroup E''] [InnerProductSpace 𝕜' E'']
  [CompleteSpace E''] [NormedSpace ℝ E'']

variable (𝕜 𝕜')

theorem condExpL2_comp_continuousLinearMap (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condExpL2 E'' 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ]
    T.compLp (condExpL2 E' 𝕜 hm f : α →₂[μ] E') := by
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) (fun s _ hμs =>
      integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) ?_ ?_ ?_
  · intro s hs hμs
    rw [T.setIntegral_compLp _ (hm s hs),
      T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne),
      integral_condExpL2_eq hm f hs hμs.ne,
      integral_condExpL2_eq hm (T.compLp f) hs hμs.ne, T.setIntegral_compLp _ (hm s hs),
      T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · exact lpMeas.aestronglyMeasurable _
  · have h_coe := T.coeFn_compLp (condExpL2 E' 𝕜 hm f : α →₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine AEStronglyMeasurable.congr ?_ h_coe.symm
    exact T.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable (condExpL2 E' 𝕜 hm f))

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

theorem condExpL2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') :
    condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) : α → ℝ) a • x := by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condExpL2_comp_continuousLinearMap ℝ 𝕜 hm (toSpanSingleton ℝ x)
      (indicatorConstLp 2 hs hμs (1 : ℝ))
  refine h_comp.trans ?_
  exact (toSpanSingleton ℝ x).coeFn_compLp _

theorem condExpL2_indicator_eq_toSpanSingleton_comp (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') : (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
    (toSpanSingleton ℝ x).compLp (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1)) := by
  ext1
  refine (condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans ?_
  have h_comp := (toSpanSingleton ℝ x).coeFn_compLp
    (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α →₂[μ] ℝ)
  rw [← EventuallyEq] at h_comp
  refine EventuallyEq.trans ?_ h_comp.symm
  filter_upwards with y using rfl

variable {𝕜}

theorem setLIntegral_nnnorm_condExpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ ≤
    μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := ℝ)
    _ ≤ μ (s ∩ t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

theorem lintegral_nnnorm_condExpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') [SigmaFinite (μ.trim hm)] :
    ∫⁻ a, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ ≤ μ s * ‖x‖₊ := by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condExpL2_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    Integrable (ε := E') (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ := by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt =>
      (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

end CondexpL2Indicator

section CondexpIndSMul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
noncomputable def condExpIndSMul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    Lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))

theorem aestronglyMeasurable_condExpIndSMul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : AEStronglyMeasurable[m] (condExpIndSMul hm hs hμs x) μ := by
  have h : AEStronglyMeasurable[m] (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) μ :=
    aestronglyMeasurable_condExpL2 _ _
  rw [condExpIndSMul]
  exact ((toSpanSingleton ℝ x).continuous.comp_aestronglyMeasurable h).congr
    (coeFn_compLpL _ _).symm

theorem condExpIndSMul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condExpIndSMul hm hs hμs (x + y) = condExpIndSMul hm hs hμs x + condExpIndSMul hm hs hμs y := by
  simp_rw [condExpIndSMul]; rw [toSpanSingleton_add, add_compLpL, _root_.add_apply]

theorem condExpIndSMul_smul [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpIndSMul hm hs hμs (c • x) = c • condExpIndSMul hm hs hμs x := by
  simp_rw [condExpIndSMul, toSpanSingleton_smul, smul_compLpL, _root_.smul_apply]

theorem condExpIndSMul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpIndSMul hm hs hμs x =ᵐ[μ] fun a =>
      (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x :=
  (toSpanSingleton ℝ x).coeFn_compLpL _

theorem setLIntegral_nnnorm_condExpIndSMul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ) ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := ℝ)
    _ ≤ μ (s ∩ t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

theorem lintegral_nnnorm_condExpIndSMul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ ≤ μ s * ‖x‖₊ := by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : Integrable (condExpIndSMul hm hs hμs x) μ := by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt => (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

theorem condExpIndSMul_empty {x : G} : condExpIndSMul hm MeasurableSet.empty
    ((measure_empty (μ := μ)).le.trans_lt ENNReal.coe_lt_top).ne x = 0 := by
  rw [condExpIndSMul, indicatorConstLp_empty]
  simp only [Submodule.coe_zero, map_zero]

theorem setIntegral_condExpL2_indicator (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    ∫ x in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) x ∂μ = μ.real (t ∩ s) :=
  calc
    ∫ x in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : ℝ) x ∂μ :=
      @integral_condExpL2_eq α _ ℝ _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) hs hμs
    _ = μ.real (t ∩ s) • (1 : ℝ) := setIntegral_indicatorConstLp (hm s hs) ht hμt 1
    _ = μ.real (t ∩ s) := by rw [smul_eq_mul, mul_one]

theorem setIntegral_condExpIndSMul (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (x : G') :
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ = μ.real (t ∩ s) • x :=
  calc
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ =
        ∫ a in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) a • x ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpIndSMul_ae_eq_smul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (∫ a in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = μ.real (t ∩ s) • x := by rw [setIntegral_condExpL2_indicator hs ht hμs hμt]

theorem condExpL2_indicator_nonneg (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    [SigmaFinite (μ.trim hm)] : (0 : α → ℝ) ≤ᵐ[μ]
    condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) := by
  have h : AEStronglyMeasurable[m] (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) μ :=
    aestronglyMeasurable_condExpL2 _ _
  refine EventuallyLE.trans_eq ?_ h.ae_eq_mk.symm
  refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm (0 : α → ℝ) _ ?_
  refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
  · rintro t - -
    refine @Integrable.integrableOn _ _ m _ _ _ _ _ ?_
    refine Integrable.trim hm ?_ h.stronglyMeasurable_mk
    rw [integrable_congr h.ae_eq_mk.symm]
    exact integrable_condExpL2_indicator hm hs hμs _
  · intro t ht hμt
    rw [← setIntegral_trim hm h.stronglyMeasurable_mk ht]
    have h_ae :
        ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) x := by
      filter_upwards [h.ae_eq_mk] with x hx using fun _ => hx.symm
    rw [setIntegral_congr_ae (hm t ht) h_ae,
      setIntegral_condExpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact ENNReal.toReal_nonneg

theorem condExpIndSMul_nonneg {E}
    [NormedAddCommGroup E] [PartialOrder E] [NormedSpace ℝ E] [IsOrderedModule ℝ E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    (0 : α → E) ≤ᵐ[μ] condExpIndSMul hm hs hμs x := by
  refine EventuallyLE.trans_eq ?_ (condExpIndSMul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condExpL2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx

end CondexpIndSMul

end MeasureTheory

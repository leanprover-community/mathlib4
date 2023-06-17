/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.conditional_expectation.condexp_L1
! leanprover-community/mathlib commit d8bbb04e2d2a44596798a9207ceefc0fb236e41e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `measure_theory.function.conditional_expectation.basic`. See that file for a
description of the full process.

The contitional expectation of an `L²` function is defined in
`measure_theory.function.conditional_expectation.condexp_L2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).

## Main definitions

* `condexp_L1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology BigOperators MeasureTheory

namespace MeasureTheory

variable {α β F F' G G' 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condexp_ind (hm : m ≤ m0) (μ : measure α) (s : set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin

/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condexpIndSmul hm hs hμs x).toL1 _
#align measure_theory.condexp_ind_L1_fin MeasureTheory.condexpIndL1Fin

theorem condexpIndL1Fin_ae_eq_condexpIndSmul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndL1Fin hm hs hμs x =ᵐ[μ] condexpIndSmul hm hs hμs x :=
  (integrable_condexpIndSmul hm hs hμs x).coeFn_toL1
#align measure_theory.condexp_ind_L1_fin_ae_eq_condexp_ind_smul MeasureTheory.condexpIndL1Fin_ae_eq_condexpIndSmul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndL1Fin hm hs hμs (x + y) = condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm hs hμs y :=
  by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine'
    eventually_eq.trans _
      (eventually_eq.add (mem_ℒp.coe_fn_to_Lp _).symm (mem_ℒp.coe_fn_to_Lp _).symm)
  rw [condexp_ind_smul_add]
  refine' (Lp.coe_fn_add _ _).trans (eventually_of_forall fun a => _)
  rfl
#align measure_theory.condexp_ind_L1_fin_add MeasureTheory.condexpIndL1Fin_add

theorem condexpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  rw [condexp_ind_smul_smul hs hμs c x]
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]
#align measure_theory.condexp_ind_L1_fin_smul MeasureTheory.condexpIndL1Fin_smul

theorem condexpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  rw [condexp_ind_smul_smul' hs hμs c x]
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]
#align measure_theory.condexp_ind_L1_fin_smul' MeasureTheory.condexpIndL1Fin_smul'

theorem norm_condexpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condexpIndL1Fin hm hs hμs x‖ ≤ (μ s).toReal * ‖x‖ := by
  have : 0 ≤ ∫ a : α, ‖condexp_ind_L1_fin hm hs hμs x a‖ ∂μ :=
    integral_nonneg fun a => norm_nonneg _
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), ← ENNReal.toReal_mul, ←
    ENNReal.toReal_ofReal this,
    ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    of_real_integral_norm_eq_lintegral_nnnorm]
  swap; · rw [← mem_ℒp_one_iff_integrable]; exact Lp.mem_ℒp _
  have h_eq :
    ∫⁻ a, ‖condexp_ind_L1_fin hm hs hμs x a‖₊ ∂μ = ∫⁻ a, ‖condexp_ind_smul hm hs hμs x a‖₊ ∂μ := by
    refine' lintegral_congr_ae _
    refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun z hz => _
    dsimp only
    rw [hz]
  rw [h_eq, ofReal_norm_eq_coe_nnnorm]
  exact lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x
#align measure_theory.norm_condexp_ind_L1_fin_le MeasureTheory.norm_condexpIndL1Fin_le

theorem condexpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1Fin hm (hs.union ht)
        ((measure_union_le s t).trans_lt
            (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
        x =
      condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm ht hμt x := by
  ext1
  have hμst :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm (hs.union ht) hμst x).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  have hs_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x
  have ht_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm ht hμt x
  refine' eventually_eq.trans _ (eventually_eq.add hs_eq.symm ht_eq.symm)
  rw [condexp_ind_smul]
  rw [indicator_const_Lp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [(condexp_L2 ℝ hm).map_add]
  push_cast
  rw [((to_span_singleton ℝ x).compLpL 2 μ).map_add]
  refine' (Lp.coe_fn_add _ _).trans _
  refine' eventually_of_forall fun y => _
  rfl
#align measure_theory.condexp_ind_L1_fin_disjoint_union MeasureTheory.condexpIndL1Fin_disjoint_union

end CondexpIndL1Fin

open scoped Classical

section CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexpIndL1Fin hm hs.1 hs.2 x else 0
#align measure_theory.condexp_ind_L1 MeasureTheory.condexpIndL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condexpIndL1 hm μ s x = condexpIndL1Fin hm hs hμs x := by
  simp only [condexp_ind_L1, And.intro hs hμs, dif_pos, Ne.def, not_false_iff, and_self_iff]
#align measure_theory.condexp_ind_L1_of_measurable_set_of_measure_ne_top MeasureTheory.condexpIndL1_of_measurableSet_of_measure_ne_top

theorem condexpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [condexp_ind_L1, hμs, eq_self_iff_true, not_true, Ne.def, dif_neg, not_false_iff,
    and_false_iff]
#align measure_theory.condexp_ind_L1_of_measure_eq_top MeasureTheory.condexpIndL1_of_measure_eq_top

theorem condexpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condexpIndL1 hm μ s x = 0 := by
  simp only [condexp_ind_L1, hs, dif_neg, not_false_iff, false_and_iff]
#align measure_theory.condexp_ind_L1_of_not_measurable_set MeasureTheory.condexpIndL1_of_not_measurableSet

theorem condexpIndL1_add (x y : G) :
    condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condexp_ind_L1_of_not_measurable_set hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_add hs hμs x y
#align measure_theory.condexp_ind_L1_add MeasureTheory.condexpIndL1_add

theorem condexpIndL1_smul (c : ℝ) (x : G) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condexp_ind_L1_of_not_measurable_set hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_smul hs hμs c x
#align measure_theory.condexp_ind_L1_smul MeasureTheory.condexpIndL1_smul

theorem condexpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condexp_ind_L1_of_not_measurable_set hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_smul' hs hμs c x
#align measure_theory.condexp_ind_L1_smul' MeasureTheory.condexpIndL1_smul'

theorem norm_condexpIndL1_le (x : G) : ‖condexpIndL1 hm μ s x‖ ≤ (μ s).toReal * ‖x‖ := by
  by_cases hs : MeasurableSet s
  swap;
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condexp_ind_L1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x]
    exact norm_condexp_ind_L1_fin_le hs hμs x
#align measure_theory.norm_condexp_ind_L1_le MeasureTheory.norm_condexpIndL1_le

theorem continuous_condexpIndL1 : Continuous fun x : G => condexpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condexpIndL1_add condexpIndL1_smul norm_condexpIndL1_le
#align measure_theory.continuous_condexp_ind_L1 MeasureTheory.continuous_condexpIndL1

theorem condexpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1 hm μ (s ∪ t) x = condexpIndL1 hm μ s x + condexpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
  rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top ht hμt x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs.union ht) hμst x]
  exact condexp_ind_L1_fin_disjoint_union hs ht hμs hμt hst x
#align measure_theory.condexp_ind_L1_disjoint_union MeasureTheory.condexpIndL1_disjoint_union

end CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G →L[ℝ] α →₁[μ] G where
  toFun := condexpIndL1 hm μ s
  map_add' := condexpIndL1_add
  map_smul' := condexpIndL1_smul
  cont := continuous_condexpIndL1
#align measure_theory.condexp_ind MeasureTheory.condexpInd

theorem condexpInd_ae_eq_condexpIndSmul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpInd hm μ s x =ᵐ[μ] condexpIndSmul hm hs hμs x := by
  refine' eventually_eq.trans _ (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x)
  simp [condexp_ind, condexp_ind_L1, hs, hμs]
#align measure_theory.condexp_ind_ae_eq_condexp_ind_smul MeasureTheory.condexpInd_ae_eq_condexpIndSmul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aEStronglyMeasurable'_condexpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable' m (condexpInd hm μ s x) μ :=
  AEStronglyMeasurable'.congr (aEStronglyMeasurable'_condexpIndSmul hm hs hμs x)
    (condexpInd_ae_eq_condexpIndSmul hm hs hμs x).symm
#align measure_theory.ae_strongly_measurable'_condexp_ind MeasureTheory.aEStronglyMeasurable'_condexpInd

@[simp]
theorem condexpInd_empty : condexpInd hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext1
  ext1
  refine' (condexp_ind_ae_eq_condexp_ind_smul hm MeasurableSet.empty (by simp) x).trans _
  rw [condexp_ind_smul_empty]
  refine' (Lp.coe_fn_zero G 2 μ).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_zero G 1 μ).symm
  rfl
#align measure_theory.condexp_ind_empty MeasureTheory.condexpInd_empty

theorem condexpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpInd hm μ s (c • x) = c • condexpInd hm μ s x :=
  condexpIndL1_smul' c x
#align measure_theory.condexp_ind_smul' MeasureTheory.condexpInd_smul'

theorem norm_condexpInd_apply_le (x : G) : ‖condexpInd hm μ s x‖ ≤ (μ s).toReal * ‖x‖ :=
  norm_condexpIndL1_le x
#align measure_theory.norm_condexp_ind_apply_le MeasureTheory.norm_condexpInd_apply_le

theorem norm_condexpInd_le : ‖(condexpInd hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ (μ s).toReal :=
  ContinuousLinearMap.op_norm_le_bound _ ENNReal.toReal_nonneg norm_condexpInd_apply_le
#align measure_theory.norm_condexp_ind_le MeasureTheory.norm_condexpInd_le

theorem condexpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpInd hm μ (s ∪ t) x = condexpInd hm μ s x + condexpInd hm μ t x :=
  condexpIndL1_disjoint_union hs ht hμs hμt hst x
#align measure_theory.condexp_ind_disjoint_union_apply MeasureTheory.condexpInd_disjoint_union_apply

theorem condexpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) :
    (condexpInd hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexpInd hm μ s + condexpInd hm μ t := by
  ext1; push_cast ; exact condexp_ind_disjoint_union_apply hs ht hμs hμt hst x
#align measure_theory.condexp_ind_disjoint_union MeasureTheory.condexpInd_disjoint_union

variable (G)

theorem dominatedFinMeasAdditive_condexpInd (hm : m ≤ m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condexpInd hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun s t => condexpInd_disjoint_union, fun s _ _ => norm_condexpInd_le.trans (one_mul _).symm.le⟩
#align measure_theory.dominated_fin_meas_additive_condexp_ind MeasureTheory.dominatedFinMeasAdditive_condexpInd

variable {G}

theorem set_integral_condexpInd (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : ∫ a in s, condexpInd hm μ t x a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, condexpInd hm μ t x a ∂μ = ∫ a in s, condexpIndSmul hm ht hμt x a ∂μ :=
      set_integral_congr_ae (hm s hs)
        ((condexpInd_ae_eq_condexpIndSmul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (μ (t ∩ s)).toReal • x := set_integral_condexpIndSmul hs ht hμs hμt x
#align measure_theory.set_integral_condexp_ind MeasureTheory.set_integral_condexpInd

theorem condexpInd_of_measurable (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condexpInd hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  refine' eventually_eq.trans _ indicator_const_Lp_coe_fn.symm
  refine' (condexp_ind_ae_eq_condexp_ind_smul hm (hm s hs) hμs c).trans _
  refine' (condexp_ind_smul_ae_eq_smul hm (hm s hs) hμs c).trans _
  rw [Lp_meas_coe, condexp_L2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  refine' (@indicator_const_Lp_coe_fn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono fun x hx => _
  dsimp only
  rw [hx]
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]
#align measure_theory.condexp_ind_of_measurable MeasureTheory.condexpInd_of_measurable

theorem condexpInd_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) : 0 ≤ condexpInd hm μ s x := by
  rw [← coe_fn_le]
  refine' eventually_le.trans_eq _ (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm
  exact (coe_fn_zero E 1 μ).trans_le (condexp_ind_smul_nonneg hs hμs x hx)
#align measure_theory.condexp_ind_nonneg MeasureTheory.condexpInd_nonneg

end CondexpInd

section CondexpL1

variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexpL1Clm (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condexpInd F' hm μ)
#align measure_theory.condexp_L1_clm MeasureTheory.condexpL1Clm

theorem condexpL1Clm_smul (c : 𝕜) (f : α →₁[μ] F') :
    condexpL1Clm hm μ (c • f) = c • condexpL1Clm hm μ f :=
  L1.setToL1_smul (dominatedFinMeasAdditive_condexpInd F' hm μ) (fun c s x => condexpInd_smul' c x)
    c f
#align measure_theory.condexp_L1_clm_smul MeasureTheory.condexpL1Clm_smul

theorem condexpL1Clm_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) (indicatorConstLp 1 hs hμs x) = condexpInd hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condexpInd F' hm μ) hs hμs x
#align measure_theory.condexp_L1_clm_indicator_const_Lp MeasureTheory.condexpL1Clm_indicatorConstLp

theorem condexpL1Clm_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condexpInd hm μ s x := by
  rw [Lp.simple_func.coe_indicator_const]; exact condexp_L1_clm_indicator_const_Lp hs hμs x
#align measure_theory.condexp_L1_clm_indicator_const MeasureTheory.condexpL1Clm_indicatorConst

/-- Auxiliary lemma used in the proof of `set_integral_condexp_L1_clm`. -/
theorem set_integral_condexpL1Clm_of_measure_ne_top (f : α →₁[μ] F') (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condexpL1Clm hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine'
    Lp.induction ENNReal.one_ne_top
      (fun f : α →₁[μ] F' => ∫ x in s, condexp_L1_clm hm μ f x ∂μ = ∫ x in s, f x ∂μ) _ _
      (isClosed_eq _ _) f
  · intro x t ht hμt
    simp_rw [condexp_L1_clm_indicator_const ht hμt.ne x]
    rw [Lp.simple_func.coe_indicator_const, set_integral_indicator_const_Lp (hm _ hs)]
    exact set_integral_condexp_ind hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp hfg_disj hf hg
    simp_rw [(condexp_L1_clm hm μ).map_add]
    rw [set_integral_congr_ae (hm s hs)
        ((Lp.coe_fn_add (condexp_L1_clm hm μ (hf_Lp.to_Lp f))
              (condexp_L1_clm hm μ (hg_Lp.to_Lp g))).mono
          fun x hx hxs => hx)]
    rw [set_integral_congr_ae (hm s hs)
        ((Lp.coe_fn_add (hf_Lp.to_Lp f) (hg_Lp.to_Lp g)).mono fun x hx hxs => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coe_fn _).IntegrableOn (L1.integrable_coe_fn _).IntegrableOn,
      integral_add (L1.integrable_coe_fn _).IntegrableOn (L1.integrable_coe_fn _).IntegrableOn, hf,
      hg]
  · exact (continuous_set_integral s).comp (condexp_L1_clm hm μ).Continuous
  · exact continuous_set_integral s
#align measure_theory.set_integral_condexp_L1_clm_of_measure_ne_top MeasureTheory.set_integral_condexpL1Clm_of_measure_ne_top

/-- The integral of the conditional expectation `condexp_L1_clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexpL1Clm (f : α →₁[μ] F') (hs : measurable_set[m] s) :
    ∫ x in s, condexpL1Clm hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  let S := spanning_sets (μ.trim hm)
  have hS_meas : ∀ i, measurable_set[m] (S i) := measurable_spanning_sets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_iUnion, Union_spanning_sets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine' fun i => (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have hS_finite_trim := measure_spanning_sets_lt_top (μ.trim hm) i
    rwa [trim_measurable_set_eq hm (hS_meas i)] at hS_finite_trim 
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanning_sets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i ∩ s, condexp_L1_clm hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      set_integral_condexp_L1_clm_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).Ne
  have h_right : tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) at_top (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coe_fn f).IntegrableOn
    rwa [← hs_eq] at h 
  have h_left :
    tendsto (fun i => ∫ x in S i ∩ s, condexp_L1_clm hm μ f x ∂μ) at_top
      (𝓝 (∫ x in s, condexp_L1_clm hm μ f x ∂μ)) := by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coe_fn (condexp_L1_clm hm μ f)).IntegrableOn
    rwa [← hs_eq] at h 
  rw [h_eq_forall] at h_left 
  exact tendsto_nhds_unique h_left h_right
#align measure_theory.set_integral_condexp_L1_clm MeasureTheory.set_integral_condexpL1Clm

theorem aEStronglyMeasurable'_condexpL1Clm (f : α →₁[μ] F') :
    AEStronglyMeasurable' m (condexpL1Clm hm μ f) μ := by
  refine'
    Lp.induction ENNReal.one_ne_top
      (fun f : α →₁[μ] F' => ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ) _ _ _ f
  · intro c s hs hμs
    rw [condexp_L1_clm_indicator_const hs hμs.ne c]
    exact ae_strongly_measurable'_condexp_ind hs hμs.ne c
  · intro f g hf hg h_disj hfm hgm
    rw [(condexp_L1_clm hm μ).map_add]
    refine' ae_strongly_measurable'.congr _ (coe_fn_add _ _).symm
    exact ae_strongly_measurable'.add hfm hgm
  · have :
      {f : Lp F' 1 μ | ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ} =
        condexp_L1_clm hm μ ⁻¹' {f | ae_strongly_measurable' m f μ} :=
      by rfl
    rw [this]
    refine' IsClosed.preimage (condexp_L1_clm hm μ).Continuous _
    exact is_closed_ae_strongly_measurable' hm
#align measure_theory.ae_strongly_measurable'_condexp_L1_clm MeasureTheory.aEStronglyMeasurable'_condexpL1Clm

theorem condexpL1Clm_lpMeas (f : lpMeas F' ℝ m 1 μ) : condexpL1Clm hm μ (f : α →₁[μ] F') = ↑f := by
  let g := Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm f
  have hfg : f = (Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g := by
    simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine'
    @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top
      (fun g : α →₁[μ.trim hm] F' =>
        condexp_L1_clm hm μ ((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
          ↑((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g))
      _ _ _ g
  · intro c s hs hμs
    rw [Lp.simple_func.coe_indicator_const, Lp_meas_to_Lp_trim_lie_symm_indicator hs hμs.ne c,
      condexp_L1_clm_indicator_const_Lp]
    exact condexp_ind_of_measurable hs ((le_trim hm).trans_lt hμs).Ne c
  · intro f g hf hg hfg_disj hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
  · refine' isClosed_eq _ _
    · refine' (condexp_L1_clm hm μ).Continuous.comp (continuous_induced_dom.comp _)
      exact LinearIsometryEquiv.continuous _
    · refine' continuous_induced_dom.comp _
      exact LinearIsometryEquiv.continuous _
#align measure_theory.condexp_L1_clm_Lp_meas MeasureTheory.condexpL1Clm_lpMeas

theorem condexpL1Clm_of_aEStronglyMeasurable' (f : α →₁[μ] F') (hfm : AEStronglyMeasurable' m f μ) :
    condexpL1Clm hm μ f = f :=
  condexpL1Clm_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)
#align measure_theory.condexp_L1_clm_of_ae_strongly_measurable' MeasureTheory.condexpL1Clm_of_aEStronglyMeasurable'

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condexpInd hm μ) (dominatedFinMeasAdditive_condexpInd F' hm μ) f
#align measure_theory.condexp_L1 MeasureTheory.condexpL1

theorem condexpL1_undef (hf : ¬Integrable f μ) : condexpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditive_condexpInd F' hm μ) hf
#align measure_theory.condexp_L1_undef MeasureTheory.condexpL1_undef

theorem condexpL1_eq (hf : Integrable f μ) : condexpL1 hm μ f = condexpL1Clm hm μ (hf.toL1 f) :=
  setToFun_eq (dominatedFinMeasAdditive_condexpInd F' hm μ) hf
#align measure_theory.condexp_L1_eq MeasureTheory.condexpL1_eq

@[simp]
theorem condexpL1_zero : condexpL1 hm μ (0 : α → F') = 0 :=
  setToFun_zero _
#align measure_theory.condexp_L1_zero MeasureTheory.condexpL1_zero

@[simp]
theorem condexpL1_measure_zero (hm : m ≤ m0) : condexpL1 hm (0 : Measure α) f = 0 :=
  setToFun_measure_zero _ rfl
#align measure_theory.condexp_L1_measure_zero MeasureTheory.condexpL1_measure_zero

theorem aEStronglyMeasurable'_condexpL1 {f : α → F'} :
    AEStronglyMeasurable' m (condexpL1 hm μ f) μ := by
  by_cases hf : integrable f μ
  · rw [condexp_L1_eq hf]
    exact ae_strongly_measurable'_condexp_L1_clm _
  · rw [condexp_L1_undef hf]
    refine' ae_strongly_measurable'.congr _ (coe_fn_zero _ _ _).symm
    exact strongly_measurable.ae_strongly_measurable' (@strongly_measurable_zero _ _ m _ _)
#align measure_theory.ae_strongly_measurable'_condexp_L1 MeasureTheory.aEStronglyMeasurable'_condexpL1

theorem condexpL1_congr_ae (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (h : f =ᵐ[μ] g) :
    condexpL1 hm μ f = condexpL1 hm μ g :=
  setToFun_congr_ae _ h
#align measure_theory.condexp_L1_congr_ae MeasureTheory.condexpL1_congr_ae

theorem integrable_condexpL1 (f : α → F') : Integrable (condexpL1 hm μ f) μ :=
  L1.integrable_coeFn _
#align measure_theory.integrable_condexp_L1 MeasureTheory.integrable_condexpL1

/-- The integral of the conditional expectation `condexp_L1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexpL1 (hf : Integrable f μ) (hs : measurable_set[m] s) :
    ∫ x in s, condexpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  simp_rw [condexp_L1_eq hf]
  rw [set_integral_condexp_L1_clm (hf.to_L1 f) hs]
  exact set_integral_congr_ae (hm s hs) (hf.coe_fn_to_L1.mono fun x hx hxs => hx)
#align measure_theory.set_integral_condexp_L1 MeasureTheory.set_integral_condexpL1

theorem condexpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f + g) = condexpL1 hm μ f + condexpL1 hm μ g :=
  setToFun_add _ hf hg
#align measure_theory.condexp_L1_add MeasureTheory.condexpL1_add

theorem condexpL1_neg (f : α → F') : condexpL1 hm μ (-f) = -condexpL1 hm μ f :=
  setToFun_neg _ f
#align measure_theory.condexp_L1_neg MeasureTheory.condexpL1_neg

theorem condexpL1_smul (c : 𝕜) (f : α → F') : condexpL1 hm μ (c • f) = c • condexpL1 hm μ f :=
  setToFun_smul _ (fun c _ x => condexpInd_smul' c x) c f
#align measure_theory.condexp_L1_smul MeasureTheory.condexpL1_smul

theorem condexpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f - g) = condexpL1 hm μ f - condexpL1 hm μ g :=
  setToFun_sub _ hf hg
#align measure_theory.condexp_L1_sub MeasureTheory.condexpL1_sub

theorem condexpL1_of_aEStronglyMeasurable' (hfm : AEStronglyMeasurable' m f μ)
    (hfi : Integrable f μ) : condexpL1 hm μ f =ᵐ[μ] f := by
  rw [condexp_L1_eq hfi]
  refine' eventually_eq.trans _ (integrable.coe_fn_to_L1 hfi)
  rw [condexp_L1_clm_of_ae_strongly_measurable']
  exact ae_strongly_measurable'.congr hfm (integrable.coe_fn_to_L1 hfi).symm
#align measure_theory.condexp_L1_of_ae_strongly_measurable' MeasureTheory.condexpL1_of_aEStronglyMeasurable'

theorem condexpL1_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condexpL1 hm μ f ≤ᵐ[μ] condexpL1 hm μ g := by
  rw [coe_fn_le]
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condexp_ind hm μ s x :=
    fun s hs hμs x hx => condexp_ind_nonneg hs hμs.Ne x hx
  exact set_to_fun_mono (dominated_fin_meas_additive_condexp_ind E hm μ) h_nonneg hf hg hfg
#align measure_theory.condexp_L1_mono MeasureTheory.condexpL1_mono

end CondexpL1

end MeasureTheory


/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

#align_import measure_theory.function.conditional_expectation.condexp_L1 from "leanprover-community/mathlib"@"d8bbb04e2d2a44596798a9207ceefc0fb236e41e"

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `MeasureTheory.Function.ConditionalExpectation.Basic`. See that file for a
description of the full process.

The contitional expectation of an `L²` function is defined in
`MeasureTheory.Function.ConditionalExpectation.CondexpL2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexpL1Clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).

## Main definitions

* `condexpL1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology BigOperators MeasureTheory

namespace MeasureTheory

variable {α β F F' G G' 𝕜 : Type*} {p : ℝ≥0∞} [IsROrC 𝕜]
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
`condexpInd (hm : m ≤ m0) (μ : Measure α) (s : Set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin

set_option linter.uppercaseLean3 false

/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condexpIndSMul hm hs hμs x).toL1 _
#align measure_theory.condexp_ind_L1_fin MeasureTheory.condexpIndL1Fin

theorem condexpIndL1Fin_ae_eq_condexpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndL1Fin hm hs hμs x =ᵐ[μ] condexpIndSMul hm hs hμs x :=
  (integrable_condexpIndSMul hm hs hμs x).coeFn_toL1
#align measure_theory.condexp_ind_L1_fin_ae_eq_condexp_ind_smul MeasureTheory.condexpIndL1Fin_ae_eq_condexpIndSMul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

-- Porting note: this lemma fills the hole in `refine' (Memℒp.coeFn_toLp _) ...`
-- which is not automatically filled in Lean 4
private theorem q {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {x : G} :
    Memℒp (condexpIndSMul hm hs hμs x) 1 μ := by
  rw [memℒp_one_iff_integrable]; apply integrable_condexpIndSMul
  -- ⊢ Integrable ↑↑(condexpIndSMul hm hs hμs x)
                                 -- 🎉 no goals

theorem condexpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndL1Fin hm hs hμs (x + y) =
    condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm hs hμs y := by
  ext1
  -- ⊢ ↑↑(condexpIndL1Fin hm hs hμs (x + y)) =ᵐ[μ] ↑↑(condexpIndL1Fin hm hs hμs x + …
  refine' (Memℒp.coeFn_toLp q).trans _
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs (x + y)) =ᵐ[μ] ↑↑(condexpIndL1Fin hm hs hμs x +  …
  refine' EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs (x + y)) =ᵐ[μ] ↑↑(condexpIndL1Fin hm hs hμs x) + …
  refine' EventuallyEq.trans _
    (EventuallyEq.add (Memℒp.coeFn_toLp q).symm (Memℒp.coeFn_toLp q).symm)
  rw [condexpIndSMul_add]
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs x + condexpIndSMul hm hs hμs y) =ᵐ[μ] fun x_1 => …
  refine' (Lp.coeFn_add _ _).trans (eventually_of_forall fun a => _)
  -- ⊢ (↑↑(condexpIndSMul hm hs hμs x) + ↑↑(condexpIndSMul hm hs hμs y)) a = (fun x …
  rfl
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_fin_add MeasureTheory.condexpIndL1Fin_add

theorem condexpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  -- ⊢ ↑↑(condexpIndL1Fin hm hs hμs (c • x)) =ᵐ[μ] ↑↑(c • condexpIndL1Fin hm hs hμs …
  refine' (Memℒp.coeFn_toLp q).trans _
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs (c • x)) =ᵐ[μ] ↑↑(c • condexpIndL1Fin hm hs hμs x)
  refine' EventuallyEq.trans _ (Lp.coeFn_smul _ _).symm
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs (c • x)) =ᵐ[μ] c • ↑↑(condexpIndL1Fin hm hs hμs x)
  rw [condexpIndSMul_smul hs hμs c x]
  -- ⊢ ↑↑(c • condexpIndSMul hm hs hμs x) =ᵐ[μ] c • ↑↑(condexpIndL1Fin hm hs hμs x)
  refine' (Lp.coeFn_smul _ _).trans _
  -- ⊢ c • ↑↑(condexpIndSMul hm hs hμs x) =ᵐ[μ] c • ↑↑(condexpIndL1Fin hm hs hμs x)
  refine' (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x).mono fun y hy => _
  -- ⊢ (c • ↑↑(condexpIndSMul hm hs hμs x)) y = (c • ↑↑(condexpIndL1Fin hm hs hμs x …
  rw [Pi.smul_apply, Pi.smul_apply, hy]
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_fin_smul MeasureTheory.condexpIndL1Fin_smul

theorem condexpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  -- ⊢ ↑↑(condexpIndL1Fin hm hs hμs (c • x)) =ᵐ[μ] ↑↑(c • condexpIndL1Fin hm hs hμs …
  refine' (Memℒp.coeFn_toLp q).trans _
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs (c • x)) =ᵐ[μ] ↑↑(c • condexpIndL1Fin hm hs hμs x)
  refine' EventuallyEq.trans _ (Lp.coeFn_smul _ _).symm
  -- ⊢ ↑↑(condexpIndSMul hm hs hμs (c • x)) =ᵐ[μ] c • ↑↑(condexpIndL1Fin hm hs hμs x)
  rw [condexpIndSMul_smul' hs hμs c x]
  -- ⊢ ↑↑(c • condexpIndSMul hm hs hμs x) =ᵐ[μ] c • ↑↑(condexpIndL1Fin hm hs hμs x)
  refine' (Lp.coeFn_smul _ _).trans _
  -- ⊢ c • ↑↑(condexpIndSMul hm hs hμs x) =ᵐ[μ] c • ↑↑(condexpIndL1Fin hm hs hμs x)
  refine' (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x).mono fun y hy => _
  -- ⊢ (c • ↑↑(condexpIndSMul hm hs hμs x)) y = (c • ↑↑(condexpIndL1Fin hm hs hμs x …
  rw [Pi.smul_apply, Pi.smul_apply, hy]
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_fin_smul' MeasureTheory.condexpIndL1Fin_smul'

theorem norm_condexpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condexpIndL1Fin hm hs hμs x‖ ≤ (μ s).toReal * ‖x‖ := by
  have : 0 ≤ ∫ a : α, ‖condexpIndL1Fin hm hs hμs x a‖ ∂μ :=
    integral_nonneg fun a => norm_nonneg _
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), ← ENNReal.toReal_mul, ←
    ENNReal.toReal_ofReal this,
    ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_nnnorm]
  swap; · rw [← memℒp_one_iff_integrable]; exact Lp.memℒp _
  -- ⊢ Integrable fun a => ↑↑(condexpIndL1Fin hm hs hμs x) a
          -- ⊢ Memℒp (fun a => ↑↑(condexpIndL1Fin hm hs hμs x) a) 1
                                           -- 🎉 no goals
  have h_eq :
    ∫⁻ a, ‖condexpIndL1Fin hm hs hμs x a‖₊ ∂μ = ∫⁻ a, ‖condexpIndSMul hm hs hμs x a‖₊ ∂μ := by
    refine' lintegral_congr_ae _
    refine' (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x).mono fun z hz => _
    dsimp only
    rw [hz]
  rw [h_eq, ofReal_norm_eq_coe_nnnorm]
  -- ⊢ ∫⁻ (a : α), ↑‖↑↑(condexpIndSMul hm hs hμs x) a‖₊ ∂μ ≤ ↑↑μ s * ↑‖x‖₊
  exact lintegral_nnnorm_condexpIndSMul_le hm hs hμs x
  -- 🎉 no goals
#align measure_theory.norm_condexp_ind_L1_fin_le MeasureTheory.norm_condexpIndL1Fin_le

theorem condexpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm ht hμt x := by
  ext1
  -- ⊢ ↑↑(condexpIndL1Fin hm (_ : MeasurableSet (s ∪ t)) (_ : ↑↑μ (s ∪ t) ≠ ⊤) x) = …
  have hμst :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  refine' (condexpIndL1Fin_ae_eq_condexpIndSMul hm (hs.union ht) hμst x).trans _
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet (s ∪ t)) hμst x) =ᵐ[μ] ↑↑(condexpInd …
  refine' EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet (s ∪ t)) hμst x) =ᵐ[μ] ↑↑(condexpInd …
  have hs_eq := condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet (s ∪ t)) hμst x) =ᵐ[μ] ↑↑(condexpInd …
  have ht_eq := condexpIndL1Fin_ae_eq_condexpIndSMul hm ht hμt x
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet (s ∪ t)) hμst x) =ᵐ[μ] ↑↑(condexpInd …
  refine' EventuallyEq.trans _ (EventuallyEq.add hs_eq.symm ht_eq.symm)
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet (s ∪ t)) hμst x) =ᵐ[μ] fun x_1 => ↑↑ …
  rw [condexpIndSMul]
  -- ⊢ ↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) ↑(↑(condexpL2 ℝ ℝ hm) (indicatorCons …
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  -- ⊢ ↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) ↑(↑(condexpL2 ℝ ℝ hm) (indicatorCons …
  rw [(condexpL2 ℝ ℝ hm).map_add]
  -- ⊢ ↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) ↑(↑(condexpL2 ℝ ℝ hm) (indicatorCons …
  push_cast
  -- ⊢ ↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) (↑(↑(condexpL2 ℝ ℝ hm) (indicatorCon …
  rw [((toSpanSingleton ℝ x).compLpL 2 μ).map_add]
  -- ⊢ ↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) ↑(↑(condexpL2 ℝ ℝ hm) (indicatorCons …
  refine' (Lp.coeFn_add _ _).trans _
  -- ⊢ ↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) ↑(↑(condexpL2 ℝ ℝ hm) (indicatorCons …
  refine' eventually_of_forall fun y => _
  -- ⊢ (↑↑(↑(compLpL 2 μ (toSpanSingleton ℝ x)) ↑(↑(condexpL2 ℝ ℝ hm) (indicatorCon …
  rfl
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_fin_disjoint_union MeasureTheory.condexpIndL1Fin_disjoint_union

end CondexpIndL1Fin

open scoped Classical

section CondexpIndL1

set_option linter.uppercaseLean3 false

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexpIndL1Fin hm hs.1 hs.2 x else 0
#align measure_theory.condexp_ind_L1 MeasureTheory.condexpIndL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condexpIndL1 hm μ s x = condexpIndL1Fin hm hs hμs x := by
  simp only [condexpIndL1, And.intro hs hμs, dif_pos, Ne.def, not_false_iff, and_self_iff]
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_of_measurable_set_of_measure_ne_top MeasureTheory.condexpIndL1_of_measurableSet_of_measure_ne_top

theorem condexpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [condexpIndL1, hμs, eq_self_iff_true, not_true, Ne.def, dif_neg, not_false_iff,
    and_false_iff]
#align measure_theory.condexp_ind_L1_of_measure_eq_top MeasureTheory.condexpIndL1_of_measure_eq_top

theorem condexpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condexpIndL1 hm μ s x = 0 := by
  simp only [condexpIndL1, hs, dif_neg, not_false_iff, false_and_iff]
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_of_not_measurable_set MeasureTheory.condexpIndL1_of_not_measurableSet

theorem condexpIndL1_add (x y : G) :
    condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  -- ⊢ condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y
  swap; · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [zero_add]
  -- ⊢ condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y
          -- ⊢ 0 = 0 + 0
                                                          -- 🎉 no goals
  by_cases hμs : μ s = ∞
  -- ⊢ condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]; rw [zero_add]
    -- ⊢ 0 = 0 + 0
                                                  -- 🎉 no goals
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    -- ⊢ condexpIndL1Fin hm hs hμs (x + y) = condexpIndL1Fin hm hs hμs x + condexpInd …
    exact condexpIndL1Fin_add hs hμs x y
    -- 🎉 no goals
#align measure_theory.condexp_ind_L1_add MeasureTheory.condexpIndL1_add

theorem condexpIndL1_smul (c : ℝ) (x : G) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  -- ⊢ condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x
  swap; · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  -- ⊢ condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x
          -- ⊢ 0 = c • 0
                                                          -- 🎉 no goals
  by_cases hμs : μ s = ∞
  -- ⊢ condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
    -- ⊢ 0 = c • 0
                                                  -- 🎉 no goals
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    -- ⊢ condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x
    exact condexpIndL1Fin_smul hs hμs c x
    -- 🎉 no goals
#align measure_theory.condexp_ind_L1_smul MeasureTheory.condexpIndL1_smul

theorem condexpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  -- ⊢ condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x
  swap; · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  -- ⊢ condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x
          -- ⊢ 0 = c • 0
                                                          -- 🎉 no goals
  by_cases hμs : μ s = ∞
  -- ⊢ condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
    -- ⊢ 0 = c • 0
                                                  -- 🎉 no goals
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    -- ⊢ condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x
    exact condexpIndL1Fin_smul' hs hμs c x
    -- 🎉 no goals
#align measure_theory.condexp_ind_L1_smul' MeasureTheory.condexpIndL1_smul'

theorem norm_condexpIndL1_le (x : G) : ‖condexpIndL1 hm μ s x‖ ≤ (μ s).toReal * ‖x‖ := by
  by_cases hs : MeasurableSet s
  -- ⊢ ‖condexpIndL1 hm μ s x‖ ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
  swap
  -- ⊢ ‖condexpIndL1 hm μ s x‖ ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
  · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    -- ⊢ ‖0‖ ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
                                                    -- ⊢ 0 ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    -- 🎉 no goals
  by_cases hμs : μ s = ∞
  -- ⊢ ‖condexpIndL1 hm μ s x‖ ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
  · rw [condexpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    -- ⊢ 0 ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    -- 🎉 no goals
  · rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    -- ⊢ ‖condexpIndL1Fin hm hs hμs x‖ ≤ ENNReal.toReal (↑↑μ s) * ‖x‖
    exact norm_condexpIndL1Fin_le hs hμs x
    -- 🎉 no goals
#align measure_theory.norm_condexp_ind_L1_le MeasureTheory.norm_condexpIndL1_le

theorem continuous_condexpIndL1 : Continuous fun x : G => condexpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condexpIndL1_add condexpIndL1_smul norm_condexpIndL1_le
#align measure_theory.continuous_condexp_ind_L1 MeasureTheory.continuous_condexpIndL1

theorem condexpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1 hm μ (s ∪ t) x = condexpIndL1 hm μ s x + condexpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs x,
    condexpIndL1_of_measurableSet_of_measure_ne_top ht hμt x,
    condexpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condexpIndL1Fin_disjoint_union hs ht hμs hμt hst x
  -- 🎉 no goals
#align measure_theory.condexp_ind_L1_disjoint_union MeasureTheory.condexpIndL1_disjoint_union

end CondexpIndL1

-- Porting note: `G` is not automatically inferred in `condexpInd` in Lean 4;
-- to avoid repeatedly typing `(G := ...)` it is made explicit.
variable (G)

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G →L[ℝ] α →₁[μ] G where
  toFun := condexpIndL1 hm μ s
  map_add' := condexpIndL1_add
  map_smul' := condexpIndL1_smul
  cont := continuous_condexpIndL1
#align measure_theory.condexp_ind MeasureTheory.condexpInd

variable {G}

theorem condexpInd_ae_eq_condexpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpInd G hm μ s x =ᵐ[μ] condexpIndSMul hm hs hμs x := by
  refine' EventuallyEq.trans _ (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x)
  -- ⊢ ↑↑(↑(condexpInd G hm μ s) x) =ᵐ[μ] ↑↑(condexpIndL1Fin hm hs hμs x)
  simp [condexpInd, condexpIndL1, hs, hμs]; rfl
  -- ⊢ ↑↑(condexpIndL1Fin hm (_ : MeasurableSet s) (_ : ↑↑μ s ≠ ⊤) x) =ᵐ[μ] ↑↑(cond …
                                            -- 🎉 no goals
#align measure_theory.condexp_ind_ae_eq_condexp_ind_smul MeasureTheory.condexpInd_ae_eq_condexpIndSMul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aestronglyMeasurable'_condexpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable' m (condexpInd G hm μ s x) μ :=
  AEStronglyMeasurable'.congr (aeStronglyMeasurable'_condexpIndSMul hm hs hμs x)
    (condexpInd_ae_eq_condexpIndSMul hm hs hμs x).symm
#align measure_theory.ae_strongly_measurable'_condexp_ind MeasureTheory.aestronglyMeasurable'_condexpInd

@[simp]
theorem condexpInd_empty : condexpInd G hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext1 x
  -- ⊢ ↑(condexpInd G hm μ ∅) x = ↑0 x
  ext1
  -- ⊢ ↑↑(↑(condexpInd G hm μ ∅) x) =ᵐ[μ] ↑↑(↑0 x)
  refine' (condexpInd_ae_eq_condexpIndSMul hm MeasurableSet.empty (by simp) x).trans _
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet ∅) (_ : ↑↑μ ∅ ≠ ⊤) x) =ᵐ[μ] ↑↑(↑0 x)
  rw [condexpIndSMul_empty]
  -- ⊢ ↑↑0 =ᵐ[μ] ↑↑(↑0 x)
  refine' (Lp.coeFn_zero G 2 μ).trans _
  -- ⊢ 0 =ᵐ[μ] ↑↑(↑0 x)
  refine' EventuallyEq.trans _ (Lp.coeFn_zero G 1 μ).symm
  -- ⊢ 0 =ᵐ[μ] 0
  rfl
  -- 🎉 no goals
#align measure_theory.condexp_ind_empty MeasureTheory.condexpInd_empty

theorem condexpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpInd F hm μ s (c • x) = c • condexpInd F hm μ s x :=
  condexpIndL1_smul' c x
#align measure_theory.condexp_ind_smul' MeasureTheory.condexpInd_smul'

theorem norm_condexpInd_apply_le (x : G) : ‖condexpInd G hm μ s x‖ ≤ (μ s).toReal * ‖x‖ :=
  norm_condexpIndL1_le x
#align measure_theory.norm_condexp_ind_apply_le MeasureTheory.norm_condexpInd_apply_le

theorem norm_condexpInd_le : ‖(condexpInd G hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ (μ s).toReal :=
  ContinuousLinearMap.op_norm_le_bound _ ENNReal.toReal_nonneg norm_condexpInd_apply_le
#align measure_theory.norm_condexp_ind_le MeasureTheory.norm_condexpInd_le

theorem condexpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpInd G hm μ (s ∪ t) x = condexpInd G hm μ s x + condexpInd G hm μ t x :=
  condexpIndL1_disjoint_union hs ht hμs hμt hst x
#align measure_theory.condexp_ind_disjoint_union_apply MeasureTheory.condexpInd_disjoint_union_apply

theorem condexpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) : (condexpInd G hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) =
    condexpInd G hm μ s + condexpInd G hm μ t := by
  ext1 x; push_cast; exact condexpInd_disjoint_union_apply hs ht hμs hμt hst x
  -- ⊢ ↑(condexpInd G hm μ (s ∪ t)) x = ↑(condexpInd G hm μ s + condexpInd G hm μ t …
          -- ⊢ ↑(condexpInd G hm μ (s ∪ t)) x = (↑(condexpInd G hm μ s) + ↑(condexpInd G hm …
                     -- 🎉 no goals
#align measure_theory.condexp_ind_disjoint_union MeasureTheory.condexpInd_disjoint_union

variable (G)

theorem dominatedFinMeasAdditive_condexpInd (hm : m ≤ m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condexpInd G hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun _ _ => condexpInd_disjoint_union, fun _ _ _ => norm_condexpInd_le.trans (one_mul _).symm.le⟩
#align measure_theory.dominated_fin_meas_additive_condexp_ind MeasureTheory.dominatedFinMeasAdditive_condexpInd

variable {G}

theorem set_integral_condexpInd (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : ∫ a in s, condexpInd G' hm μ t x a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, condexpInd G' hm μ t x a ∂μ = ∫ a in s, condexpIndSMul hm ht hμt x a ∂μ :=
      set_integral_congr_ae (hm s hs)
        ((condexpInd_ae_eq_condexpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (μ (t ∩ s)).toReal • x := set_integral_condexpIndSMul hs ht hμs hμt x
#align measure_theory.set_integral_condexp_ind MeasureTheory.set_integral_condexpInd

theorem condexpInd_of_measurable (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condexpInd G hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  -- ⊢ ↑↑(↑(condexpInd G hm μ s) c) =ᵐ[μ] ↑↑(indicatorConstLp 1 (_ : MeasurableSet  …
  refine' EventuallyEq.trans _ indicatorConstLp_coeFn.symm
  -- ⊢ ↑↑(↑(condexpInd G hm μ s) c) =ᵐ[μ] Set.indicator s fun x => c
  refine' (condexpInd_ae_eq_condexpIndSMul hm (hm s hs) hμs c).trans _
  -- ⊢ ↑↑(condexpIndSMul hm (_ : MeasurableSet s) hμs c) =ᵐ[μ] Set.indicator s fun  …
  refine' (condexpIndSMul_ae_eq_smul hm (hm s hs) hμs c).trans _
  -- ⊢ (fun a => ↑↑↑(↑(condexpL2 ℝ ℝ hm) (indicatorConstLp 2 (_ : MeasurableSet s)  …
  rw [lpMeas_coe, condexpL2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  -- ⊢ (fun a => ↑↑(indicatorConstLp 2 (_ : MeasurableSet s) hμs 1) a • c) =ᵐ[μ] Se …
  refine' (@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono fun x hx => _
  -- ⊢ (fun a => ↑↑(indicatorConstLp 2 (_ : MeasurableSet s) hμs 1) a • c) x = Set. …
  dsimp only
  -- ⊢ ↑↑(indicatorConstLp 2 (_ : MeasurableSet s) hμs 1) x • c = Set.indicator s ( …
  rw [hx]
  -- ⊢ Set.indicator s (fun x => 1) x • c = Set.indicator s (fun x => c) x
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]
  -- ⊢ Set.indicator s (fun x => 1) x • c = Set.indicator s (fun x => c) x
                              -- 🎉 no goals
                              -- 🎉 no goals
#align measure_theory.condexp_ind_of_measurable MeasureTheory.condexpInd_of_measurable

theorem condexpInd_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) : 0 ≤ condexpInd E hm μ s x := by
  rw [← coeFn_le]
  -- ⊢ ↑↑0 ≤ᵐ[μ] ↑↑(↑(condexpInd E hm μ s) x)
  refine' EventuallyLE.trans_eq _ (condexpInd_ae_eq_condexpIndSMul hm hs hμs x).symm
  -- ⊢ ↑↑0 ≤ᵐ[μ] ↑↑(condexpIndSMul hm hs hμs x)
  exact (coeFn_zero E 1 μ).trans_le (condexpIndSMul_nonneg hs hμs x hx)
  -- 🎉 no goals
#align measure_theory.condexp_ind_nonneg MeasureTheory.condexpInd_nonneg

end CondexpInd

section CondexpL1

set_option linter.uppercaseLean3 false

variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

-- Porting note: `F'` is not automatically inferred in `condexpL1Clm` in Lean 4;
-- to avoid repeatedly typing `(F' := ...)` it is made explicit.
variable (F')

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexpL1Clm (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condexpInd F' hm μ)
#align measure_theory.condexp_L1_clm MeasureTheory.condexpL1Clm

variable {F'}

theorem condexpL1Clm_smul (c : 𝕜) (f : α →₁[μ] F') :
    condexpL1Clm F' hm μ (c • f) = c • condexpL1Clm F' hm μ f := by
  refine' L1.setToL1_smul (dominatedFinMeasAdditive_condexpInd F' hm μ) _ c f
  -- ⊢ ∀ (c : 𝕜) (s : Set α) (x : F'), ↑(condexpInd F' hm μ s) (c • x) = c • ↑(cond …
  exact fun c s x => condexpInd_smul' c x
  -- 🎉 no goals
#align measure_theory.condexp_L1_clm_smul MeasureTheory.condexpL1Clm_smul

theorem condexpL1Clm_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm F' hm μ) (indicatorConstLp 1 hs hμs x) = condexpInd F' hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condexpInd F' hm μ) hs hμs x
#align measure_theory.condexp_L1_clm_indicator_const_Lp MeasureTheory.condexpL1Clm_indicatorConstLp

theorem condexpL1Clm_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condexpInd F' hm μ s x := by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condexpL1Clm_indicatorConstLp hs hμs x
  -- ⊢ ↑(condexpL1Clm F' hm μ) (indicatorConstLp 1 hs hμs x) = ↑(condexpInd F' hm μ …
                                         -- 🎉 no goals
#align measure_theory.condexp_L1_clm_indicator_const MeasureTheory.condexpL1Clm_indicatorConst

/-- Auxiliary lemma used in the proof of `set_integral_condexpL1Clm`. -/
theorem set_integral_condexpL1Clm_of_measure_ne_top (f : α →₁[μ] F') (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condexpL1Clm F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine' @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => ∫ x in s, condexpL1Clm F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) _ _
    (isClosed_eq _ _) f
  · intro x t ht hμt
    -- ⊢ ∫ (x_1 : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) ↑(simpleFunc.indicatorConst 1 h …
    simp_rw [condexpL1Clm_indicatorConst ht hμt.ne x]
    -- ⊢ ∫ (x_1 : α) in s, ↑↑(↑(condexpInd F' hm μ t) x) x_1 ∂μ = ∫ (x_1 : α) in s, ↑ …
    rw [Lp.simpleFunc.coe_indicatorConst, set_integral_indicatorConstLp (hm _ hs)]
    -- ⊢ ∫ (x_1 : α) in s, ↑↑(↑(condexpInd F' hm μ t) x) x_1 ∂μ = ENNReal.toReal (↑↑μ …
    exact set_integral_condexpInd hs ht hμs hμt.ne x
    -- 🎉 no goals
  · intro f g hf_Lp hg_Lp _ hf hg
    -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) (Memℒp.toLp f hf_Lp + Memℒp.toLp  …
    simp_rw [(condexpL1Clm F' hm μ).map_add]
    -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) (Memℒp.toLp f hf_Lp) + ↑(condexpL …
    rw [set_integral_congr_ae (hm s hs) ((Lp.coeFn_add (condexpL1Clm F' hm μ (hf_Lp.toLp f))
      (condexpL1Clm F' hm μ (hg_Lp.toLp g))).mono fun x hx _ => hx)]
    rw [set_integral_congr_ae (hm s hs)
      ((Lp.coeFn_add (hf_Lp.toLp f) (hg_Lp.toLp g)).mono fun x hx _ => hx)]
    simp_rw [Pi.add_apply]
    -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) (Memℒp.toLp f hf_Lp)) x + ↑↑(↑(co …
    rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn,
      integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn, hf,
      hg]
  · exact (continuous_set_integral s).comp (condexpL1Clm F' hm μ).continuous
    -- 🎉 no goals
  · exact continuous_set_integral s
    -- 🎉 no goals
#align measure_theory.set_integral_condexp_L1_clm_of_measure_ne_top MeasureTheory.set_integral_condexpL1Clm_of_measure_ne_top

/-- The integral of the conditional expectation `condexpL1Clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexpL1Clm (f : α →₁[μ] F') (hs : MeasurableSet[m] s) :
    ∫ x in s, condexpL1Clm F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  let S := spanningSets (μ.trim hm)
  -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) f) x ∂μ = ∫ (x : α) in s, ↑↑f x ∂μ
  have hS_meas : ∀ i, MeasurableSet[m] (S i) := measurable_spanningSets (μ.trim hm)
  -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) f) x ∂μ = ∫ (x : α) in s, ↑↑f x ∂μ
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) f) x ∂μ = ∫ (x : α) in s, ↑↑f x ∂μ
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_iUnion, iUnion_spanningSets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine' fun i => (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have hS_finite_trim := measure_spanningSets_lt_top (μ.trim hm) i
    rwa [trim_measurableSet_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanningSets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i ∩ s, condexpL1Clm F' hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      set_integral_condexpL1Clm_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left : Tendsto (fun i => ∫ x in S i ∩ s, condexpL1Clm F' hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condexpL1Clm F' hm μ f x ∂μ)) := by
    have h := tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
      (L1.integrable_coeFn (condexpL1Clm F' hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) f) x ∂μ = ∫ (x : α) in s, ↑↑f x ∂μ
  exact tendsto_nhds_unique h_left h_right
  -- 🎉 no goals
#align measure_theory.set_integral_condexp_L1_clm MeasureTheory.set_integral_condexpL1Clm

theorem aestronglyMeasurable'_condexpL1Clm (f : α →₁[μ] F') :
    AEStronglyMeasurable' m (condexpL1Clm F' hm μ f) μ := by
  refine' @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => AEStronglyMeasurable' m (condexpL1Clm F' hm μ f) μ) _ _ _ f
  · intro c s hs hμs
    -- ⊢ AEStronglyMeasurable' m (↑↑(↑(condexpL1Clm F' hm μ) ↑(simpleFunc.indicatorCo …
    rw [condexpL1Clm_indicatorConst hs hμs.ne c]
    -- ⊢ AEStronglyMeasurable' m (↑↑(↑(condexpInd F' hm μ s) c)) μ
    exact aestronglyMeasurable'_condexpInd hs hμs.ne c
    -- 🎉 no goals
  · intro f g hf hg _ hfm hgm
    -- ⊢ AEStronglyMeasurable' m (↑↑(↑(condexpL1Clm F' hm μ) (Memℒp.toLp f hf + Memℒp …
    rw [(condexpL1Clm F' hm μ).map_add]
    -- ⊢ AEStronglyMeasurable' m (↑↑(↑(condexpL1Clm F' hm μ) (Memℒp.toLp f hf) + ↑(co …
    refine' AEStronglyMeasurable'.congr _ (coeFn_add _ _).symm
    -- ⊢ AEStronglyMeasurable' m (↑↑(↑(condexpL1Clm F' hm μ) (Memℒp.toLp f hf)) + ↑↑( …
    exact AEStronglyMeasurable'.add hfm hgm
    -- 🎉 no goals
  · have : {f : Lp F' 1 μ | AEStronglyMeasurable' m (condexpL1Clm F' hm μ f) μ} =
        condexpL1Clm F' hm μ ⁻¹' {f | AEStronglyMeasurable' m f μ} := by rfl
    rw [this]
    -- ⊢ IsClosed (↑(condexpL1Clm F' hm μ) ⁻¹' {f | AEStronglyMeasurable' m (↑↑f) μ})
    refine' IsClosed.preimage (condexpL1Clm F' hm μ).continuous _
    -- ⊢ IsClosed {f | AEStronglyMeasurable' m (↑↑f) μ}
    exact isClosed_aeStronglyMeasurable' hm
    -- 🎉 no goals
#align measure_theory.ae_strongly_measurable'_condexp_L1_clm MeasureTheory.aestronglyMeasurable'_condexpL1Clm

theorem condexpL1Clm_lpMeas (f : lpMeas F' ℝ m 1 μ) :
    condexpL1Clm F' hm μ (f : α →₁[μ] F') = ↑f := by
  let g := lpMeasToLpTrimLie F' ℝ 1 μ hm f
  -- ⊢ ↑(condexpL1Clm F' hm μ) ↑f = ↑f
  have hfg : f = (lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g := by
    simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  -- ⊢ ↑(condexpL1Clm F' hm μ) ↑(↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F' ℝ …
  refine' @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α →₁[μ.trim hm] F' =>
    condexpL1Clm F' hm μ ((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
    ↑((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g)) _ _ _ g
  · intro c s hs hμs
    -- ⊢ ↑(condexpL1Clm F' hm μ) ↑(↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F' ℝ …
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator hs hμs.ne c,
      condexpL1Clm_indicatorConstLp]
    exact condexpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
    -- 🎉 no goals
  · intro f g hf hg _ hf_eq hg_eq
    -- ⊢ ↑(condexpL1Clm F' hm μ) ↑(↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F' ℝ …
    rw [LinearIsometryEquiv.map_add]
    -- ⊢ ↑(condexpL1Clm F' hm μ) ↑(↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F' ℝ …
    push_cast
    -- ⊢ ↑(condexpL1Clm F' hm μ) (↑(↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F'  …
    rw [map_add, hf_eq, hg_eq]
    -- 🎉 no goals
  · refine' isClosed_eq _ _
    -- ⊢ Continuous fun f => ↑(condexpL1Clm F' hm μ) ↑(↑(LinearIsometryEquiv.symm (lp …
    · refine' (condexpL1Clm F' hm μ).continuous.comp (continuous_induced_dom.comp _)
      -- ⊢ Continuous fun f => ↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F' ℝ 1 μ h …
      exact LinearIsometryEquiv.continuous _
      -- 🎉 no goals
    · refine' continuous_induced_dom.comp _
      -- ⊢ Continuous fun f => ↑(LinearIsometryEquiv.symm (lpMeasToLpTrimLie F' ℝ 1 μ h …
      exact LinearIsometryEquiv.continuous _
      -- 🎉 no goals
#align measure_theory.condexp_L1_clm_Lp_meas MeasureTheory.condexpL1Clm_lpMeas

theorem condexpL1Clm_of_aestronglyMeasurable' (f : α →₁[μ] F') (hfm : AEStronglyMeasurable' m f μ) :
    condexpL1Clm F' hm μ f = f :=
  condexpL1Clm_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)
#align measure_theory.condexp_L1_clm_of_ae_strongly_measurable' MeasureTheory.condexpL1Clm_of_aestronglyMeasurable'

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condexpInd F' hm μ) (dominatedFinMeasAdditive_condexpInd F' hm μ) f
#align measure_theory.condexp_L1 MeasureTheory.condexpL1

theorem condexpL1_undef (hf : ¬Integrable f μ) : condexpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditive_condexpInd F' hm μ) hf
#align measure_theory.condexp_L1_undef MeasureTheory.condexpL1_undef

theorem condexpL1_eq (hf : Integrable f μ) : condexpL1 hm μ f = condexpL1Clm F' hm μ (hf.toL1 f) :=
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

theorem aestronglyMeasurable'_condexpL1 {f : α → F'} :
    AEStronglyMeasurable' m (condexpL1 hm μ f) μ := by
  by_cases hf : Integrable f μ
  -- ⊢ AEStronglyMeasurable' m (↑↑(condexpL1 hm μ f)) μ
  · rw [condexpL1_eq hf]
    -- ⊢ AEStronglyMeasurable' m (↑↑(↑(condexpL1Clm F' hm μ) (Integrable.toL1 f hf))) μ
    exact aestronglyMeasurable'_condexpL1Clm _
    -- 🎉 no goals
  · rw [condexpL1_undef hf]
    -- ⊢ AEStronglyMeasurable' m (↑↑0) μ
    refine AEStronglyMeasurable'.congr ?_ (coeFn_zero _ _ _).symm
    -- ⊢ AEStronglyMeasurable' m 0 μ
    exact StronglyMeasurable.aeStronglyMeasurable' (@stronglyMeasurable_zero _ _ m _ _)
    -- 🎉 no goals
#align measure_theory.ae_strongly_measurable'_condexp_L1 MeasureTheory.aestronglyMeasurable'_condexpL1

theorem condexpL1_congr_ae (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (h : f =ᵐ[μ] g) :
    condexpL1 hm μ f = condexpL1 hm μ g :=
  setToFun_congr_ae _ h
#align measure_theory.condexp_L1_congr_ae MeasureTheory.condexpL1_congr_ae

theorem integrable_condexpL1 (f : α → F') : Integrable (condexpL1 hm μ f) μ :=
  L1.integrable_coeFn _
#align measure_theory.integrable_condexp_L1 MeasureTheory.integrable_condexpL1

/-- The integral of the conditional expectation `condexpL1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexpL1 (hf : Integrable f μ) (hs : MeasurableSet[m] s) :
    ∫ x in s, condexpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  simp_rw [condexpL1_eq hf]
  -- ⊢ ∫ (x : α) in s, ↑↑(↑(condexpL1Clm F' hm μ) (Integrable.toL1 f hf)) x ∂μ = ∫  …
  rw [set_integral_condexpL1Clm (hf.toL1 f) hs]
  -- ⊢ ∫ (x : α) in s, ↑↑(Integrable.toL1 f hf) x ∂μ = ∫ (x : α) in s, f x ∂μ
  exact set_integral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)
  -- 🎉 no goals
#align measure_theory.set_integral_condexp_L1 MeasureTheory.set_integral_condexpL1

theorem condexpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f + g) = condexpL1 hm μ f + condexpL1 hm μ g :=
  setToFun_add _ hf hg
#align measure_theory.condexp_L1_add MeasureTheory.condexpL1_add

theorem condexpL1_neg (f : α → F') : condexpL1 hm μ (-f) = -condexpL1 hm μ f :=
  setToFun_neg _ f
#align measure_theory.condexp_L1_neg MeasureTheory.condexpL1_neg

theorem condexpL1_smul (c : 𝕜) (f : α → F') : condexpL1 hm μ (c • f) = c • condexpL1 hm μ f := by
  refine' setToFun_smul _ _ c f
  -- ⊢ ∀ (c : 𝕜) (s : Set α) (x : F'), ↑(condexpInd F' hm μ s) (c • x) = c • ↑(cond …
  exact fun c _ x => condexpInd_smul' c x
  -- 🎉 no goals
#align measure_theory.condexp_L1_smul MeasureTheory.condexpL1_smul

theorem condexpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f - g) = condexpL1 hm μ f - condexpL1 hm μ g :=
  setToFun_sub _ hf hg
#align measure_theory.condexp_L1_sub MeasureTheory.condexpL1_sub

theorem condexpL1_of_aestronglyMeasurable' (hfm : AEStronglyMeasurable' m f μ)
    (hfi : Integrable f μ) : condexpL1 hm μ f =ᵐ[μ] f := by
  rw [condexpL1_eq hfi]
  -- ⊢ ↑↑(↑(condexpL1Clm F' hm μ) (Integrable.toL1 f hfi)) =ᵐ[μ] f
  refine' EventuallyEq.trans _ (Integrable.coeFn_toL1 hfi)
  -- ⊢ ↑↑(↑(condexpL1Clm F' hm μ) (Integrable.toL1 f hfi)) =ᵐ[μ] ↑↑(Integrable.toL1 …
  rw [condexpL1Clm_of_aestronglyMeasurable']
  -- ⊢ AEStronglyMeasurable' m (↑↑(Integrable.toL1 f hfi)) μ
  exact AEStronglyMeasurable'.congr hfm (Integrable.coeFn_toL1 hfi).symm
  -- 🎉 no goals
#align measure_theory.condexp_L1_of_ae_strongly_measurable' MeasureTheory.condexpL1_of_aestronglyMeasurable'

theorem condexpL1_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condexpL1 hm μ f ≤ᵐ[μ] condexpL1 hm μ g := by
  rw [coeFn_le]
  -- ⊢ condexpL1 hm μ f ≤ condexpL1 hm μ g
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condexpInd E hm μ s x :=
    fun s hs hμs x hx => condexpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condexpInd E hm μ) h_nonneg hf hg hfg
  -- 🎉 no goals
#align measure_theory.condexp_L1_mono MeasureTheory.condexpL1_mono

end CondexpL1

end MeasureTheory

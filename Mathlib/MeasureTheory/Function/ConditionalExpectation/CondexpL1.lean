/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `MeasureTheory.Function.ConditionalExpectation.Basic`. See that file for a
description of the full process.

The conditional expectation of an `L²` function is defined in
`MeasureTheory.Function.ConditionalExpectation.CondexpL2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).

## Main definitions

* `condExpL1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α F F' G G' 𝕜 : Type*} [RCLike 𝕜]
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
`condExpInd (hm : m ≤ m0) (μ : Measure α) (s : Set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin


/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condExpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condExpIndSMul hm hs hμs x).toL1 _

@[deprecated (since := "2025-01-21")] noncomputable alias condexpIndL1Fin := condExpIndL1Fin

theorem condExpIndL1Fin_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpIndL1Fin hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

@[deprecated (since := "2025-01-21")]
alias condexpIndL1Fin_ae_eq_condexpIndSMul := condExpIndL1Fin_ae_eq_condExpIndSMul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

-- Porting note: this lemma fills the hole in `refine' (Memℒp.coeFn_toLp _) ...`
-- which is not automatically filled in Lean 4
private theorem q {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {x : G} :
    Memℒp (condExpIndSMul hm hs hμs x) 1 μ := by
  rw [memℒp_one_iff_integrable]; apply integrable_condExpIndSMul

theorem condExpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condExpIndL1Fin hm hs hμs (x + y) =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm hs hμs y := by
  ext1
  refine (Memℒp.coeFn_toLp q).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  refine EventuallyEq.trans ?_
    (EventuallyEq.add (Memℒp.coeFn_toLp q).symm (Memℒp.coeFn_toLp q).symm)
  rw [condExpIndSMul_add]
  refine (Lp.coeFn_add _ _).trans (Eventually.of_forall fun a => ?_)
  rfl

@[deprecated (since := "2025-01-21")] alias condexpIndL1Fin_add := condExpIndL1Fin_add

theorem condExpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  refine (Memℒp.coeFn_toLp q).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  rw [condExpIndSMul_smul hs hμs c x]
  refine (Lp.coeFn_smul _ _).trans ?_
  refine (condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x).mono fun y hy => ?_
  simp only [Pi.smul_apply, hy]

@[deprecated (since := "2025-01-21")] alias condexpIndL1Fin_smul := condExpIndL1Fin_smul

theorem condExpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  refine (Memℒp.coeFn_toLp q).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  rw [condExpIndSMul_smul' hs hμs c x]
  refine (Lp.coeFn_smul _ _).trans ?_
  refine (condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x).mono fun y hy => ?_
  simp only [Pi.smul_apply, hy]

@[deprecated (since := "2025-01-21")] alias condexpIndL1Fin_smul' := condExpIndL1Fin_smul'

theorem norm_condExpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condExpIndL1Fin hm hs hμs x‖ ≤ (μ s).toReal * ‖x‖ := by
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), ← ENNReal.toReal_mul,
    ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_nnnorm]
  swap; · rw [← memℒp_one_iff_integrable]; exact Lp.memℒp _
  have h_eq :
    ∫⁻ a, ‖condExpIndL1Fin hm hs hμs x a‖₊ ∂μ = ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ := by
    refine lintegral_congr_ae ?_
    refine (condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x).mono fun z hz => ?_
    dsimp only
    rw [hz]
  rw [h_eq, ofReal_norm_eq_coe_nnnorm]
  exact lintegral_nnnorm_condExpIndSMul_le hm hs hμs x

@[deprecated (since := "2025-01-21")] alias norm_condexpIndL1Fin_le := norm_condExpIndL1Fin_le

theorem condExpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm ht hμt x := by
  ext1
  have hμst := measure_union_ne_top hμs hμt
  refine (condExpIndL1Fin_ae_eq_condExpIndSMul hm (hs.union ht) hμst x).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  have hs_eq := condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x
  have ht_eq := condExpIndL1Fin_ae_eq_condExpIndSMul hm ht hμt x
  refine EventuallyEq.trans ?_ (EventuallyEq.add hs_eq.symm ht_eq.symm)
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [(condExpL2 ℝ ℝ hm).map_add]
  push_cast
  rw [((toSpanSingleton ℝ x).compLpL 2 μ).map_add]
  refine (Lp.coeFn_add _ _).trans ?_
  filter_upwards with y using rfl

@[deprecated (since := "2025-01-21")]
alias condexpIndL1Fin_disjoint_union := condExpIndL1Fin_disjoint_union

end CondexpIndL1Fin

open scoped Classical

section CondexpIndL1


/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condExpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condExpIndL1Fin hm hs.1 hs.2 x else 0

@[deprecated (since := "2025-01-21")] noncomputable alias condexpIndL1 := condExpIndL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condExpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm hs hμs x := by
  simp only [condExpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]

@[deprecated (since := "2025-01-21")]
alias condexpIndL1_of_measurableSet_of_measure_ne_top :=
  condExpIndL1_of_measurableSet_of_measure_ne_top

theorem condExpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hμs, eq_self_iff_true, not_true, Ne, dif_neg, not_false_iff,
    and_false]

@[deprecated (since := "2025-01-21")]
alias condexpIndL1_of_measure_eq_top := condExpIndL1_of_measure_eq_top

theorem condExpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hs, dif_neg, not_false_iff, false_and]

@[deprecated (since := "2025-01-21")]
alias condexpIndL1_of_not_measurableSet := condExpIndL1_of_not_measurableSet

theorem condExpIndL1_add (x y : G) :
    condExpIndL1 hm μ s (x + y) = condExpIndL1 hm μ s x + condExpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_add hs hμs x y

@[deprecated (since := "2025-01-21")] alias condexpIndL1_add := condExpIndL1_add

theorem condExpIndL1_smul (c : ℝ) (x : G) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul hs hμs c x

@[deprecated (since := "2025-01-21")] alias condexpIndL1_smul := condExpIndL1_smul

theorem condExpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul' hs hμs c x

@[deprecated (since := "2025-01-21")] alias condexpIndL1_smul' := condExpIndL1_smul'

theorem norm_condExpIndL1_le (x : G) : ‖condExpIndL1 hm μ s x‖ ≤ (μ s).toReal * ‖x‖ := by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condExpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    exact norm_condExpIndL1Fin_le hs hμs x

@[deprecated (since := "2025-01-21")] alias norm_condexpIndL1_le := norm_condExpIndL1_le

theorem continuous_condExpIndL1 : Continuous fun x : G => condExpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condExpIndL1_add condExpIndL1_smul norm_condExpIndL1_le

@[deprecated (since := "2025-01-21")] alias continuous_condexpIndL1 := continuous_condExpIndL1

theorem condExpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1 hm μ (s ∪ t) x = condExpIndL1 hm μ s x + condExpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x,
    condExpIndL1_of_measurableSet_of_measure_ne_top ht hμt x,
    condExpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condExpIndL1Fin_disjoint_union hs ht hμs hμt hst x

@[deprecated (since := "2025-01-21")]
alias condexpIndL1_disjoint_union := condExpIndL1_disjoint_union

end CondexpIndL1

-- Porting note: `G` is not automatically inferred in `condExpInd` in Lean 4;
-- to avoid repeatedly typing `(G := ...)` it is made explicit.
variable (G)

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condExpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G →L[ℝ] α →₁[μ] G where
  toFun := condExpIndL1 hm μ s
  map_add' := condExpIndL1_add
  map_smul' := condExpIndL1_smul
  cont := continuous_condExpIndL1

@[deprecated (since := "2025-01-21")] noncomputable alias condexpInd := condExpInd

variable {G}

theorem condExpInd_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpInd G hm μ s x =ᵐ[μ] condExpIndSMul hm hs hμs x := by
  refine EventuallyEq.trans ?_ (condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x)
  simp [condExpInd, condExpIndL1, hs, hμs]

@[deprecated (since := "2025-01-21")]
alias condexpInd_ae_eq_condexpIndSMul := condExpInd_ae_eq_condExpIndSMul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aestronglyMeasurable_condExpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable[m] (condExpInd G hm μ s x) μ :=
  (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm

@[deprecated (since := "2025-01-24")]
alias aestronglyMeasurable'_condExpInd := aestronglyMeasurable_condExpInd

@[deprecated (since := "2025-01-21")]
alias aestronglyMeasurable'_condexpInd := aestronglyMeasurable_condExpInd

@[simp]
theorem condExpInd_empty : condExpInd G hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext1 x
  ext1
  refine (condExpInd_ae_eq_condExpIndSMul hm MeasurableSet.empty (by simp) x).trans ?_
  rw [condExpIndSMul_empty]
  refine (Lp.coeFn_zero G 2 μ).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_zero G 1 μ).symm
  rfl

@[deprecated (since := "2025-01-21")] alias condexpInd_empty := condExpInd_empty

theorem condExpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condExpInd F hm μ s (c • x) = c • condExpInd F hm μ s x :=
  condExpIndL1_smul' c x

@[deprecated (since := "2025-01-21")] alias condexpInd_smul' := condExpInd_smul'

theorem norm_condExpInd_apply_le (x : G) : ‖condExpInd G hm μ s x‖ ≤ (μ s).toReal * ‖x‖ :=
  norm_condExpIndL1_le x

@[deprecated (since := "2025-01-21")] alias norm_condexpInd_apply_le := norm_condExpInd_apply_le

theorem norm_condExpInd_le : ‖(condExpInd G hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ (μ s).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg norm_condExpInd_apply_le

@[deprecated (since := "2025-01-21")] alias norm_condexpInd_le := norm_condExpInd_le

theorem condExpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpInd G hm μ (s ∪ t) x = condExpInd G hm μ s x + condExpInd G hm μ t x :=
  condExpIndL1_disjoint_union hs ht hμs hμt hst x

@[deprecated (since := "2025-01-21")]
alias condexpInd_disjoint_union_apply := condExpInd_disjoint_union_apply

theorem condExpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) : (condExpInd G hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) =
    condExpInd G hm μ s + condExpInd G hm μ t := by
  ext1 x; push_cast; exact condExpInd_disjoint_union_apply hs ht hμs hμt hst x

@[deprecated (since := "2025-01-21")] alias condexpInd_disjoint_union := condExpInd_disjoint_union

variable (G)

theorem dominatedFinMeasAdditive_condExpInd (hm : m ≤ m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condExpInd G hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun _ _ => condExpInd_disjoint_union, fun _ _ _ => norm_condExpInd_le.trans (one_mul _).symm.le⟩

@[deprecated (since := "2025-01-21")]
alias dominatedFinMeasAdditive_condexpInd := dominatedFinMeasAdditive_condExpInd

variable {G}

theorem setIntegral_condExpInd (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : ∫ a in s, condExpInd G' hm μ t x a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, condExpInd G' hm μ t x a ∂μ = ∫ a in s, condExpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpInd_ae_eq_condExpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (μ (t ∩ s)).toReal • x := setIntegral_condExpIndSMul hs ht hμs hμt x

@[deprecated (since := "2025-01-21")] alias setIntegral_condexpInd := setIntegral_condExpInd

@[deprecated (since := "2024-04-17")]
alias set_integral_condExpInd := setIntegral_condExpInd

@[deprecated (since := "2025-01-21")] alias set_integral_condexpInd := set_integral_condExpInd

theorem condExpInd_of_measurable (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condExpInd G hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  refine EventuallyEq.trans ?_ indicatorConstLp_coeFn.symm
  refine (condExpInd_ae_eq_condExpIndSMul hm (hm s hs) hμs c).trans ?_
  refine (condExpIndSMul_ae_eq_smul hm (hm s hs) hμs c).trans ?_
  rw [lpMeas_coe, condExpL2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  refine (@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono fun x hx => ?_
  dsimp only
  rw [hx]
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]

@[deprecated (since := "2025-01-21")] alias condexpInd_of_measurable := condExpInd_of_measurable

theorem condExpInd_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) : 0 ≤ condExpInd E hm μ s x := by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condExpIndSMul_nonneg hs hμs x hx)

@[deprecated (since := "2025-01-21")] alias condexpInd_nonneg := condExpInd_nonneg

end CondexpInd

section CondexpL1


variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

-- Porting note: `F'` is not automatically inferred in `condExpL1CLM` in Lean 4;
-- to avoid repeatedly typing `(F' := ...)` it is made explicit.
variable (F')

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condExpL1CLM (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condExpInd F' hm μ)

@[deprecated (since := "2025-01-21")] noncomputable alias condexpL1CLM := condExpL1CLM

variable {F'}

theorem condExpL1CLM_smul (c : 𝕜) (f : α →₁[μ] F') :
    condExpL1CLM F' hm μ (c • f) = c • condExpL1CLM F' hm μ f := by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condExpInd F' hm μ) ?_ c f
  exact fun c s x => condExpInd_smul' c x

@[deprecated (since := "2025-01-21")] alias condexpL1CLM_smul := condExpL1CLM_smul

theorem condExpL1CLM_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condExpL1CLM F' hm μ) (indicatorConstLp 1 hs hμs x) = condExpInd F' hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condExpInd F' hm μ) hs hμs x

@[deprecated (since := "2025-01-21")]
alias condexpL1CLM_indicatorConstLp := condExpL1CLM_indicatorConstLp

theorem condExpL1CLM_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condExpL1CLM F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condExpInd F' hm μ s x := by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condExpL1CLM_indicatorConstLp hs hμs x

@[deprecated (since := "2025-01-21")]
alias condexpL1CLM_indicatorConst := condExpL1CLM_indicatorConst

/-- Auxiliary lemma used in the proof of `setIntegral_condExpL1CLM`. -/
theorem setIntegral_condExpL1CLM_of_measure_ne_top (f : α →₁[μ] F') (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condExpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst, setIntegral_indicatorConstLp (hm _ hs)]
    exact setIntegral_condExpInd hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp _ hf hg
    simp_rw [(condExpL1CLM F' hm μ).map_add]
    rw [setIntegral_congr_ae (hm s hs) ((Lp.coeFn_add (condExpL1CLM F' hm μ (hf_Lp.toLp f))
      (condExpL1CLM F' hm μ (hg_Lp.toLp g))).mono fun x hx _ => hx)]
    rw [setIntegral_congr_ae (hm s hs)
      ((Lp.coeFn_add (hf_Lp.toLp f) (hg_Lp.toLp g)).mono fun x hx _ => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn,
      integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn, hf,
      hg]
  · exact (continuous_setIntegral s).comp (condExpL1CLM F' hm μ).continuous
  · exact continuous_setIntegral s

@[deprecated (since := "2025-01-21")]
alias setIntegral_condexpL1CLM_of_measure_ne_top := setIntegral_condExpL1CLM_of_measure_ne_top

@[deprecated (since := "2024-04-17")]
alias set_integral_condexpL1CLM_of_measure_ne_top :=
  setIntegral_condExpL1CLM_of_measure_ne_top

@[deprecated (since := "2025-01-21")]
alias setIntegral_condexpL1CLM := set_integral_condexpL1CLM_of_measure_ne_top

/-- The integral of the conditional expectation `condExpL1CLM` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `setIntegral_condExp`, the similar statement for
`condExp`. -/
theorem setIntegral_condExpL1CLM (f : α →₁[μ] F') (hs : MeasurableSet[m] s) :
    ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  let S := spanningSets (μ.trim hm)
  have hS_meas : ∀ i, MeasurableSet[m] (S i) := measurableSet_spanningSets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_iUnion, iUnion_spanningSets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine fun i => (measure_mono Set.inter_subset_left).trans_lt ?_
    have hS_finite_trim := measure_spanningSets_lt_top (μ.trim hm) i
    rwa [trim_measurableSet_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanningSets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i ∩ s, condExpL1CLM F' hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      setIntegral_condExpL1CLM_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left : Tendsto (fun i => ∫ x in S i ∩ s, condExpL1CLM F' hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condExpL1CLM F' hm μ f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
      (L1.integrable_coeFn (condExpL1CLM F' hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right

@[deprecated (since := "2024-04-17")]
alias set_integral_condExpL1CLM := setIntegral_condExpL1CLM

@[deprecated (since := "2025-01-21")] alias set_integral_condexpL1CLM := set_integral_condExpL1CLM

theorem aestronglyMeasurable_condExpL1CLM (f : α →₁[μ] F') :
    AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condExpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable_condExpInd hs hμs.ne c
  · intro f g hf hg _ hfm hgm
    rw [(condExpL1CLM F' hm μ).map_add]
    exact (hfm.add hgm).congr (coeFn_add ..).symm
  · have : {f : Lp F' 1 μ | AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ} =
        condExpL1CLM F' hm μ ⁻¹' {f | AEStronglyMeasurable[m] f μ} := rfl
    rw [this]
    refine IsClosed.preimage (condExpL1CLM F' hm μ).continuous ?_
    exact isClosed_aeStronglyMeasurable' hm

@[deprecated (since := "2025-01-24")]
alias aestronglyMeasurable'_condExpL1CLM := aestronglyMeasurable_condExpL1CLM

@[deprecated (since := "2025-01-21")]
alias aestronglyMeasurable_condexpL1CLM := aestronglyMeasurable_condExpL1CLM

@[deprecated (since := "2025-01-24")]
alias aestronglyMeasurable'_condexpL1CLM := aestronglyMeasurable_condexpL1CLM

theorem condExpL1CLM_lpMeas (f : lpMeas F' ℝ m 1 μ) :
    condExpL1CLM F' hm μ (f : α →₁[μ] F') = ↑f := by
  let g := lpMeasToLpTrimLie F' ℝ 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α →₁[μ.trim hm] F' =>
    condExpL1CLM F' hm μ ((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
    ↑((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g)) ?_ ?_ ?_ g
  · intro c s hs hμs
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator hs hμs.ne c,
      condExpL1CLM_indicatorConstLp]
    exact condExpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
  · intro f g hf hg _ hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
  · refine isClosed_eq ?_ ?_
    · refine (condExpL1CLM F' hm μ).continuous.comp (continuous_induced_dom.comp ?_)
      exact LinearIsometryEquiv.continuous _
    · refine continuous_induced_dom.comp ?_
      exact LinearIsometryEquiv.continuous _

@[deprecated (since := "2025-01-21")] alias condexpL1CLM_lpMeas := condExpL1CLM_lpMeas

theorem condExpL1CLM_of_aestronglyMeasurable' (f : α →₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ) :
    condExpL1CLM F' hm μ f = f :=
  condExpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)

@[deprecated (since := "2025-01-21")]
alias condexpL1CLM_of_aestronglyMeasurable' := condExpL1CLM_of_aestronglyMeasurable'

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condExp` should be used instead in most cases. -/
def condExpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condExpInd F' hm μ) (dominatedFinMeasAdditive_condExpInd F' hm μ) f

@[deprecated (since := "2025-01-21")] noncomputable alias condexpL1 := condExpL1

theorem condExpL1_undef (hf : ¬Integrable f μ) : condExpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

@[deprecated (since := "2025-01-21")] alias condexpL1_undef := condExpL1_undef

theorem condExpL1_eq (hf : Integrable f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f) :=
  setToFun_eq (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

@[deprecated (since := "2025-01-21")] alias condexpL1_eq := condExpL1_eq

@[simp]
theorem condExpL1_zero : condExpL1 hm μ (0 : α → F') = 0 :=
  setToFun_zero _

@[deprecated (since := "2025-01-21")] alias condexpL1_zero := condExpL1_zero

@[simp]
theorem condExpL1_measure_zero (hm : m ≤ m0) : condExpL1 hm (0 : Measure α) f = 0 :=
  setToFun_measure_zero _ rfl

@[deprecated (since := "2025-01-21")] alias condexpL1_measure_zero := condExpL1_measure_zero

theorem aestronglyMeasurable_condExpL1 {f : α → F'} :
    AEStronglyMeasurable[m] (condExpL1 hm μ f) μ := by
  by_cases hf : Integrable f μ
  · rw [condExpL1_eq hf]
    exact aestronglyMeasurable_condExpL1CLM _
  · rw [condExpL1_undef hf]
    exact stronglyMeasurable_zero.aestronglyMeasurable.congr (coeFn_zero ..).symm

@[deprecated (since := "2025-01-24")]
alias aestronglyMeasurable'_condExpL1 := aestronglyMeasurable_condExpL1

@[deprecated (since := "2025-01-21")]
alias aestronglyMeasurable_condexpL1 := aestronglyMeasurable_condExpL1

@[deprecated (since := "2025-01-24")]
alias aestronglyMeasurable'_condexpL1 := aestronglyMeasurable_condexpL1

theorem condExpL1_congr_ae (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (h : f =ᵐ[μ] g) :
    condExpL1 hm μ f = condExpL1 hm μ g :=
  setToFun_congr_ae _ h

@[deprecated (since := "2025-01-21")] alias condexpL1_congr_ae := condExpL1_congr_ae

theorem integrable_condExpL1 (f : α → F') : Integrable (condExpL1 hm μ f) μ :=
  L1.integrable_coeFn _

@[deprecated (since := "2025-01-21")] alias integrable_condexpL1 := integrable_condExpL1

/-- The integral of the conditional expectation `condExpL1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `setIntegral_condExp`, the similar statement for
`condExp`. -/
theorem setIntegral_condExpL1 (hf : Integrable f μ) (hs : MeasurableSet[m] s) :
    ∫ x in s, condExpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  simp_rw [condExpL1_eq hf]
  rw [setIntegral_condExpL1CLM (hf.toL1 f) hs]
  exact setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)

@[deprecated (since := "2025-01-21")] alias setIntegral_condexpL1 := setIntegral_condExpL1

@[deprecated (since := "2024-04-17")]
alias set_integral_condExpL1 := setIntegral_condExpL1

@[deprecated (since := "2025-01-21")] alias set_integral_condexpL1 := set_integral_condExpL1

theorem condExpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condExpL1 hm μ (f + g) = condExpL1 hm μ f + condExpL1 hm μ g :=
  setToFun_add _ hf hg

@[deprecated (since := "2025-01-21")] alias condexpL1_add := condExpL1_add

theorem condExpL1_neg (f : α → F') : condExpL1 hm μ (-f) = -condExpL1 hm μ f :=
  setToFun_neg _ f

@[deprecated (since := "2025-01-21")] alias condexpL1_neg := condExpL1_neg

theorem condExpL1_smul (c : 𝕜) (f : α → F') : condExpL1 hm μ (c • f) = c • condExpL1 hm μ f := by
  refine setToFun_smul _ ?_ c f
  exact fun c _ x => condExpInd_smul' c x

@[deprecated (since := "2025-01-21")] alias condexpL1_smul := condExpL1_smul

theorem condExpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condExpL1 hm μ (f - g) = condExpL1 hm μ f - condExpL1 hm μ g :=
  setToFun_sub _ hf hg

@[deprecated (since := "2025-01-21")] alias condexpL1_sub := condExpL1_sub

theorem condExpL1_of_aestronglyMeasurable' (hfm : AEStronglyMeasurable[m] f μ)
    (hfi : Integrable f μ) : condExpL1 hm μ f =ᵐ[μ] f := by
  rw [condExpL1_eq hfi]
  refine EventuallyEq.trans ?_ (Integrable.coeFn_toL1 hfi)
  rw [condExpL1CLM_of_aestronglyMeasurable']
  exact hfm.congr hfi.coeFn_toL1.symm

@[deprecated (since := "2025-01-21")]
alias condexpL1_of_aestronglyMeasurable' := condExpL1_of_aestronglyMeasurable'

theorem condExpL1_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condExpL1 hm μ f ≤ᵐ[μ] condExpL1 hm μ g := by
  rw [coeFn_le]
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condExpInd E hm μ s x :=
    fun s hs hμs x hx => condExpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condExpInd E hm μ) h_nonneg hf hg hfg

@[deprecated (since := "2025-01-21")] alias condexpL1_mono := condExpL1_mono

end CondexpL1

end MeasureTheory

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
* Extend that map to `condexpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).

## Main definitions

* `condexpL1`: Conditional expectation of a function as a linear map from `L1` to itself.

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
`condexpInd (hm : m ≤ m0) (μ : Measure α) (s : Set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin


/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condexpIndSMul hm hs hμs x).toL1 _

theorem condexpIndL1Fin_ae_eq_condexpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndL1Fin hm hs hμs x =ᵐ[μ] condexpIndSMul hm hs hμs x :=
  (integrable_condexpIndSMul hm hs hμs x).coeFn_toL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

-- Porting note: this lemma fills the hole in `refine' (Memℒp.coeFn_toLp _) ...`
-- which is not automatically filled in Lean 4
private theorem q {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {x : G} :
    Memℒp (condexpIndSMul hm hs hμs x) 1 μ := by
  rw [memℒp_one_iff_integrable]; apply integrable_condexpIndSMul

theorem condexpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndL1Fin hm hs hμs (x + y) =
    condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm hs hμs y := by
  ext1
  refine (Memℒp.coeFn_toLp q).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  refine EventuallyEq.trans ?_
    (EventuallyEq.add (Memℒp.coeFn_toLp q).symm (Memℒp.coeFn_toLp q).symm)
  rw [condexpIndSMul_add]
  refine (Lp.coeFn_add _ _).trans (Eventually.of_forall fun a => ?_)
  rfl

theorem condexpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine (Memℒp.coeFn_toLp q).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  rw [condexpIndSMul_smul hs hμs c x]
  refine (Lp.coeFn_smul _ _).trans ?_
  refine (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x).mono fun y hy => ?_
  simp only [Pi.smul_apply, hy]

theorem condexpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine (Memℒp.coeFn_toLp q).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  rw [condexpIndSMul_smul' hs hμs c x]
  refine (Lp.coeFn_smul _ _).trans ?_
  refine (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x).mono fun y hy => ?_
  simp only [Pi.smul_apply, hy]

theorem norm_condexpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condexpIndL1Fin hm hs hμs x‖ ≤ (μ s).toReal * ‖x‖ := by
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), ← ENNReal.toReal_mul,
    ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_nnnorm]
  swap; · rw [← memℒp_one_iff_integrable]; exact Lp.memℒp _
  have h_eq :
    ∫⁻ a, ‖condexpIndL1Fin hm hs hμs x a‖₊ ∂μ = ∫⁻ a, ‖condexpIndSMul hm hs hμs x a‖₊ ∂μ := by
    refine lintegral_congr_ae ?_
    refine (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x).mono fun z hz => ?_
    dsimp only
    rw [hz]
  rw [h_eq, ofReal_norm_eq_enorm]
  exact lintegral_nnnorm_condexpIndSMul_le hm hs hμs x

theorem condexpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condexpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm ht hμt x := by
  ext1
  have hμst := measure_union_ne_top hμs hμt
  refine (condexpIndL1Fin_ae_eq_condexpIndSMul hm (hs.union ht) hμst x).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  have hs_eq := condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x
  have ht_eq := condexpIndL1Fin_ae_eq_condexpIndSMul hm ht hμt x
  refine EventuallyEq.trans ?_ (EventuallyEq.add hs_eq.symm ht_eq.symm)
  rw [condexpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [(condexpL2 ℝ ℝ hm).map_add]
  push_cast
  rw [((toSpanSingleton ℝ x).compLpL 2 μ).map_add]
  refine (Lp.coeFn_add _ _).trans ?_
  filter_upwards with y using rfl

end CondexpIndL1Fin

open scoped Classical

section CondexpIndL1


/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexpIndL1Fin hm hs.1 hs.2 x else 0

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condexpIndL1 hm μ s x = condexpIndL1Fin hm hs hμs x := by
  simp only [condexpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]

theorem condexpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [condexpIndL1, hμs, eq_self_iff_true, not_true, Ne, dif_neg, not_false_iff,
    and_false]

theorem condexpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condexpIndL1 hm μ s x = 0 := by
  simp only [condexpIndL1, hs, dif_neg, not_false_iff, false_and]

theorem condexpIndL1_add (x y : G) :
    condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condexpIndL1Fin_add hs hμs x y

theorem condexpIndL1_smul (c : ℝ) (x : G) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condexpIndL1Fin_smul hs hμs c x

theorem condexpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condexpIndL1Fin_smul' hs hμs c x

theorem norm_condexpIndL1_le (x : G) : ‖condexpIndL1 hm μ s x‖ ≤ (μ s).toReal * ‖x‖ := by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condexpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condexpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    exact norm_condexpIndL1Fin_le hs hμs x

theorem continuous_condexpIndL1 : Continuous fun x : G => condexpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condexpIndL1_add condexpIndL1_smul norm_condexpIndL1_le

theorem condexpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condexpIndL1 hm μ (s ∪ t) x = condexpIndL1 hm μ s x + condexpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs x,
    condexpIndL1_of_measurableSet_of_measure_ne_top ht hμt x,
    condexpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condexpIndL1Fin_disjoint_union hs ht hμs hμt hst x

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

variable {G}

theorem condexpInd_ae_eq_condexpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpInd G hm μ s x =ᵐ[μ] condexpIndSMul hm hs hμs x := by
  refine EventuallyEq.trans ?_ (condexpIndL1Fin_ae_eq_condexpIndSMul hm hs hμs x)
  simp [condexpInd, condexpIndL1, hs, hμs]

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aestronglyMeasurable'_condexpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable' m (condexpInd G hm μ s x) μ :=
  AEStronglyMeasurable'.congr (aeStronglyMeasurable'_condexpIndSMul hm hs hμs x)
    (condexpInd_ae_eq_condexpIndSMul hm hs hμs x).symm

@[simp]
theorem condexpInd_empty : condexpInd G hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext1 x
  ext1
  refine (condexpInd_ae_eq_condexpIndSMul hm MeasurableSet.empty (by simp) x).trans ?_
  rw [condexpIndSMul_empty]
  refine (Lp.coeFn_zero G 2 μ).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_zero G 1 μ).symm
  rfl

theorem condexpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpInd F hm μ s (c • x) = c • condexpInd F hm μ s x :=
  condexpIndL1_smul' c x

theorem norm_condexpInd_apply_le (x : G) : ‖condexpInd G hm μ s x‖ ≤ (μ s).toReal * ‖x‖ :=
  norm_condexpIndL1_le x

theorem norm_condexpInd_le : ‖(condexpInd G hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ (μ s).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg norm_condexpInd_apply_le

theorem condexpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condexpInd G hm μ (s ∪ t) x = condexpInd G hm μ s x + condexpInd G hm μ t x :=
  condexpIndL1_disjoint_union hs ht hμs hμt hst x

theorem condexpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) : (condexpInd G hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) =
    condexpInd G hm μ s + condexpInd G hm μ t := by
  ext1 x; push_cast; exact condexpInd_disjoint_union_apply hs ht hμs hμt hst x

variable (G)

theorem dominatedFinMeasAdditive_condexpInd (hm : m ≤ m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condexpInd G hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun _ _ => condexpInd_disjoint_union, fun _ _ _ => norm_condexpInd_le.trans (one_mul _).symm.le⟩

variable {G}

theorem setIntegral_condexpInd (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : ∫ a in s, condexpInd G' hm μ t x a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, condexpInd G' hm μ t x a ∂μ = ∫ a in s, condexpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condexpInd_ae_eq_condexpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (μ (t ∩ s)).toReal • x := setIntegral_condexpIndSMul hs ht hμs hμt x

@[deprecated (since := "2024-04-17")]
alias set_integral_condexpInd := setIntegral_condexpInd

theorem condexpInd_of_measurable (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condexpInd G hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  refine EventuallyEq.trans ?_ indicatorConstLp_coeFn.symm
  refine (condexpInd_ae_eq_condexpIndSMul hm (hm s hs) hμs c).trans ?_
  refine (condexpIndSMul_ae_eq_smul hm (hm s hs) hμs c).trans ?_
  rw [lpMeas_coe, condexpL2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  refine (@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono fun x hx => ?_
  dsimp only
  rw [hx]
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]

theorem condexpInd_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) : 0 ≤ condexpInd E hm μ s x := by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condexpInd_ae_eq_condexpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condexpIndSMul_nonneg hs hμs x hx)

end CondexpInd

section CondexpL1


variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

-- Porting note: `F'` is not automatically inferred in `condexpL1CLM` in Lean 4;
-- to avoid repeatedly typing `(F' := ...)` it is made explicit.
variable (F')

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexpL1CLM (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condexpInd F' hm μ)

variable {F'}

theorem condexpL1CLM_smul (c : 𝕜) (f : α →₁[μ] F') :
    condexpL1CLM F' hm μ (c • f) = c • condexpL1CLM F' hm μ f := by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condexpInd F' hm μ) ?_ c f
  exact fun c s x => condexpInd_smul' c x

theorem condexpL1CLM_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1CLM F' hm μ) (indicatorConstLp 1 hs hμs x) = condexpInd F' hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condexpInd F' hm μ) hs hμs x

theorem condexpL1CLM_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1CLM F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condexpInd F' hm μ s x := by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condexpL1CLM_indicatorConstLp hs hμs x

/-- Auxiliary lemma used in the proof of `setIntegral_condexpL1CLM`. -/
theorem setIntegral_condexpL1CLM_of_measure_ne_top (f : α →₁[μ] F') (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condexpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => ∫ x in s, condexpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condexpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst, setIntegral_indicatorConstLp (hm _ hs)]
    exact setIntegral_condexpInd hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp _ hf hg
    simp_rw [(condexpL1CLM F' hm μ).map_add]
    rw [setIntegral_congr_ae (hm s hs) ((Lp.coeFn_add (condexpL1CLM F' hm μ (hf_Lp.toLp f))
      (condexpL1CLM F' hm μ (hg_Lp.toLp g))).mono fun x hx _ => hx)]
    rw [setIntegral_congr_ae (hm s hs)
      ((Lp.coeFn_add (hf_Lp.toLp f) (hg_Lp.toLp g)).mono fun x hx _ => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn,
      integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn, hf,
      hg]
  · exact (continuous_setIntegral s).comp (condexpL1CLM F' hm μ).continuous
  · exact continuous_setIntegral s

@[deprecated (since := "2024-04-17")]
alias set_integral_condexpL1CLM_of_measure_ne_top :=
  setIntegral_condexpL1CLM_of_measure_ne_top

/-- The integral of the conditional expectation `condexpL1CLM` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `setIntegral_condexp`, the similar statement for
`condexp`. -/
theorem setIntegral_condexpL1CLM (f : α →₁[μ] F') (hs : MeasurableSet[m] s) :
    ∫ x in s, condexpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
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
    (fun i => ∫ x in S i ∩ s, condexpL1CLM F' hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      setIntegral_condexpL1CLM_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left : Tendsto (fun i => ∫ x in S i ∩ s, condexpL1CLM F' hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condexpL1CLM F' hm μ f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
      (L1.integrable_coeFn (condexpL1CLM F' hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right

@[deprecated (since := "2024-04-17")]
alias set_integral_condexpL1CLM := setIntegral_condexpL1CLM

theorem aestronglyMeasurable'_condexpL1CLM (f : α →₁[μ] F') :
    AEStronglyMeasurable' m (condexpL1CLM F' hm μ f) μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => AEStronglyMeasurable' m (condexpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condexpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable'_condexpInd hs hμs.ne c
  · intro f g hf hg _ hfm hgm
    rw [(condexpL1CLM F' hm μ).map_add]
    refine AEStronglyMeasurable'.congr ?_ (coeFn_add _ _).symm
    exact AEStronglyMeasurable'.add hfm hgm
  · have : {f : Lp F' 1 μ | AEStronglyMeasurable' m (condexpL1CLM F' hm μ f) μ} =
        condexpL1CLM F' hm μ ⁻¹' {f | AEStronglyMeasurable' m f μ} := rfl
    rw [this]
    refine IsClosed.preimage (condexpL1CLM F' hm μ).continuous ?_
    exact isClosed_aeStronglyMeasurable' hm

theorem condexpL1CLM_lpMeas (f : lpMeas F' ℝ m 1 μ) :
    condexpL1CLM F' hm μ (f : α →₁[μ] F') = ↑f := by
  let g := lpMeasToLpTrimLie F' ℝ 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α →₁[μ.trim hm] F' =>
    condexpL1CLM F' hm μ ((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
    ↑((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g)) ?_ ?_ ?_ g
  · intro c s hs hμs
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator hs hμs.ne c,
      condexpL1CLM_indicatorConstLp]
    exact condexpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
  · intro f g hf hg _ hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
  · refine isClosed_eq ?_ ?_
    · refine (condexpL1CLM F' hm μ).continuous.comp (continuous_induced_dom.comp ?_)
      exact LinearIsometryEquiv.continuous _
    · refine continuous_induced_dom.comp ?_
      exact LinearIsometryEquiv.continuous _

theorem condexpL1CLM_of_aestronglyMeasurable' (f : α →₁[μ] F') (hfm : AEStronglyMeasurable' m f μ) :
    condexpL1CLM F' hm μ f = f :=
  condexpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condexpInd F' hm μ) (dominatedFinMeasAdditive_condexpInd F' hm μ) f

theorem condexpL1_undef (hf : ¬Integrable f μ) : condexpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditive_condexpInd F' hm μ) hf

theorem condexpL1_eq (hf : Integrable f μ) : condexpL1 hm μ f = condexpL1CLM F' hm μ (hf.toL1 f) :=
  setToFun_eq (dominatedFinMeasAdditive_condexpInd F' hm μ) hf

@[simp]
theorem condexpL1_zero : condexpL1 hm μ (0 : α → F') = 0 :=
  setToFun_zero _

@[simp]
theorem condexpL1_measure_zero (hm : m ≤ m0) : condexpL1 hm (0 : Measure α) f = 0 :=
  setToFun_measure_zero _ rfl

theorem aestronglyMeasurable'_condexpL1 {f : α → F'} :
    AEStronglyMeasurable' m (condexpL1 hm μ f) μ := by
  by_cases hf : Integrable f μ
  · rw [condexpL1_eq hf]
    exact aestronglyMeasurable'_condexpL1CLM _
  · rw [condexpL1_undef hf]
    refine AEStronglyMeasurable'.congr ?_ (coeFn_zero _ _ _).symm
    exact StronglyMeasurable.aeStronglyMeasurable' (@stronglyMeasurable_zero _ _ m _ _)

theorem condexpL1_congr_ae (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (h : f =ᵐ[μ] g) :
    condexpL1 hm μ f = condexpL1 hm μ g :=
  setToFun_congr_ae _ h

theorem integrable_condexpL1 (f : α → F') : Integrable (condexpL1 hm μ f) μ :=
  L1.integrable_coeFn _

/-- The integral of the conditional expectation `condexpL1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `setIntegral_condexp`, the similar statement for
`condexp`. -/
theorem setIntegral_condexpL1 (hf : Integrable f μ) (hs : MeasurableSet[m] s) :
    ∫ x in s, condexpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  simp_rw [condexpL1_eq hf]
  rw [setIntegral_condexpL1CLM (hf.toL1 f) hs]
  exact setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)

@[deprecated (since := "2024-04-17")]
alias set_integral_condexpL1 := setIntegral_condexpL1

theorem condexpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f + g) = condexpL1 hm μ f + condexpL1 hm μ g :=
  setToFun_add _ hf hg

theorem condexpL1_neg (f : α → F') : condexpL1 hm μ (-f) = -condexpL1 hm μ f :=
  setToFun_neg _ f

theorem condexpL1_smul (c : 𝕜) (f : α → F') : condexpL1 hm μ (c • f) = c • condexpL1 hm μ f := by
  refine setToFun_smul _ ?_ c f
  exact fun c _ x => condexpInd_smul' c x

theorem condexpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f - g) = condexpL1 hm μ f - condexpL1 hm μ g :=
  setToFun_sub _ hf hg

theorem condexpL1_of_aestronglyMeasurable' (hfm : AEStronglyMeasurable' m f μ)
    (hfi : Integrable f μ) : condexpL1 hm μ f =ᵐ[μ] f := by
  rw [condexpL1_eq hfi]
  refine EventuallyEq.trans ?_ (Integrable.coeFn_toL1 hfi)
  rw [condexpL1CLM_of_aestronglyMeasurable']
  exact AEStronglyMeasurable'.congr hfm (Integrable.coeFn_toL1 hfi).symm

theorem condexpL1_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condexpL1 hm μ f ≤ᵐ[μ] condexpL1 hm μ g := by
  rw [coeFn_le]
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condexpInd E hm μ s x :=
    fun s hs hμs x hx => condexpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condexpInd E hm μ) h_nonneg hf hg hfg

end CondexpL1

end MeasureTheory

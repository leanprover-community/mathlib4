/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Spaces where indicators of closed sets have sequences of continuous approximating from above

In this file we define a typeclass `HasOuterApproxClosed` for topological spaces in which indicator
functions of closed sets have sequences of bounded continuous functions approximating them from
above. All pseudo-emetrizable spaces have this property, see `instHasOuterApproxClosed`.

In spaces with the `HasOuterApproxClosed` property, finite Borel measures are uniquely characterized
by the integrals of bounded continuous functions. Also weak convergence of finite measures and
convergence in distribution for random variables behave somewhat well in spaces with this property.

## Main definitions

 * `HasOuterApproxClosed`: the typeclass for topological spaces in which indicator functions of
   closed sets have sequences of bounded continuous functions approximating them.
 * `IsClosed.apprSeq`: a (non-constructive) choice of an approximating sequence to the indicator
   function of a closed set.

## Main results

 * `instHasOuterApproxClosed`: Any pseudo-emetrizable space has the property `HasOuterApproxClosed`.
 * `tendsto_lintegral_apprSeq`: The integrals of the approximating functions to the indicator of a
   closed set tend to the measure of the set.
 * `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`: Two finite measures are equal if the integrals
   of all bounded continuous functions with respect to both agree.

-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section HasOuterApproxClosed

/-- A type class for topological spaces in which the indicator functions of closed sets can be
approximated pointwise from above by a sequence of bounded continuous functions. -/
class HasOuterApproxClosed (X : Type _) [TopologicalSpace X] where
  exAppr : ∀ (F : Set X), IsClosed F → ∃ (fseq: ℕ → (X →ᵇ ℝ≥0)),
    (∀ n x, fseq n x ≤ 1) ∧ (∀ n x, x ∈ F → 1 ≤ fseq n x) ∧
    Tendsto (fun n : ℕ ↦ (fun x ↦ fseq n x)) atTop (𝓝 (indicator F fun _ ↦ (1 : ℝ≥0)))

namespace HasOuterApproxClosed

variable {X : Type _} [TopologicalSpace X] [HasOuterApproxClosed X]
variable {F : Set X} (hF : IsClosed F)

/-- A sequence of continuous functions `X → [0,1]` tending to the indicator of a closed set. -/
noncomputable def _root_.IsClosed.apprSeq : ℕ → (X →ᵇ ℝ≥0) :=
  Exists.choose (HasOuterApproxClosed.exAppr F hF)

lemma apprSeq_apply_le_one (n : ℕ) (x : X) :
    hF.apprSeq n x ≤ 1 :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).1 n x

lemma one_le_apprSeq_apply (n : ℕ) {x : X} (hxF : x ∈ F) :
    1 ≤ hF.apprSeq n x :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.1 n x hxF

lemma tendsto_apprSeq :
    Tendsto (fun n : ℕ ↦ (fun x ↦ hF.apprSeq n x)) atTop (𝓝 (indicator F fun _ ↦ (1 : ℝ≥0))) :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.2

lemma indicator_le_apprSeq (n : ℕ) :
    indicator F (fun _ ↦ 1) ≤ hF.apprSeq n := by
  intro x
  by_cases hxF : x ∈ F
  · simp only [hxF, indicator_of_mem, one_le_apprSeq_apply hF n]
  · simp only [hxF, not_false_eq_true, indicator_of_not_mem, zero_le]

lemma apprSeq_apply_eq_one (n : ℕ) {x : X} (hx : x ∈ F) :
    hF.apprSeq n x = 1 :=
  le_antisymm (apprSeq_apply_le_one hF n x) (one_le_apprSeq_apply hF n hx)

/-- The measure of a closed set is at most the integral of any function in a decreasing
approximating sequence to the indicator of the set. -/
theorem measure_le_lintegral [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (n : ℕ) :
    μ F ≤ ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂μ := by
  convert_to ∫⁻ x, (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) x ∂μ ≤ ∫⁻ x, hF.apprSeq n x ∂μ
  · rw [lintegral_indicator _ hF.measurableSet]
    simp only [lintegral_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  · apply lintegral_mono
    intro x
    by_cases hxF : x ∈ F
    · simpa only [hxF, indicator_of_mem, one_le_coe_iff] using one_le_apprSeq_apply hF n hxF
    · simp only [hxF, not_false_eq_true, indicator_of_not_mem, zero_le]

/-- The integrals along a decreasing approximating sequence to the indicator of a closed set
tend to the measure of the closed set. -/
lemma tendsto_lintegral_apprSeq [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    Tendsto (fun n ↦ ∫⁻ x, hF.apprSeq n x ∂μ) atTop (𝓝 ((μ : Measure X) F)) :=
  measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet hF.apprSeq
    (apprSeq_apply_le_one hF) (tendsto_apprSeq hF)

end HasOuterApproxClosed --namespace

noncomputable instance (X : Type _) [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] : HasOuterApproxClosed X := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  refine ⟨fun F hF ↦ ?_⟩
  · use fun n ↦ thickenedIndicator (δ := (1 : ℝ) / (n + 1)) Nat.one_div_pos_of_nat F
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · exact fun n x ↦ thickenedIndicator_le_one Nat.one_div_pos_of_nat F x
    · exact fun n x hxF ↦ one_le_thickenedIndicator_apply X Nat.one_div_pos_of_nat hxF
    · have key := thickenedIndicator_tendsto_indicator_closure
                (δseq := fun (n : ℕ) ↦ (1 : ℝ) / (n + 1))
                (fun _ ↦ Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_0_nat F
      rw [tendsto_pi_nhds] at *
      intro x
      nth_rw 2 [←IsClosed.closure_eq hF]
      exact key x

namespace MeasureTheory

/-- Two finite measures give equal values to all closed sets if the integrals of all bounded
continuous functions with respect to the two measures agree. -/
theorem measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) {F : Set Ω} (F_closed : IsClosed F) :
    μ F = ν F := by
  have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed μ
  have obs_ν := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed ν
  simp_rw [h] at obs_μ
  exact tendsto_nhds_unique obs_μ obs_ν

/-
/-- Two finite measures give equal values to all closed sets if the integrals of all bounded
continuous functions with respect to the two measures agree. -/
theorem FiniteMeasure.measure_isClosed_eq_of_forall_lintegral_eq {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ ν : FiniteMeasure Ω}
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) {F : Set Ω} (F_closed : IsClosed F) :
    μ F = ν F :=
  Subtype.ext (congrArg Subtype.val (congrArg ENNReal.toNNReal
    (measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure h F_closed)))
 -/

/-- Two finite Borel measures are equal if the integrals of all bounded continuous functions with
respect to both agree. -/
theorem ext_of_forall_lintegral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
    μ = ν := by
  have key := @measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure Ω _ _ _ _ μ ν _ _ h
  apply ext_of_generate_finite _ ?_ isPiSystem_set_isClosed
  · exact fun F F_closed ↦ key F_closed
  · exact key isClosed_univ
  · rw [← borel_eq_generateFrom_isClosed]
    exact BorelSpace.measurable_eq

end MeasureTheory -- namespace

end HasOuterApproxClosed -- section

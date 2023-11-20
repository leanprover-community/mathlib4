/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Topology.MetricSpace.ThickenedIndicator

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

section auxiliary

namespace MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is `MeasureTheory.lintegral`, i.e., the functions and their integrals are
   `ℝ≥0∞`-valued.
-/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    (μ : Measure Ω) [IsFiniteMeasure μ] {fs : ι → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c) {f : Ω → ℝ≥0}
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i => fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i => ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
    (eventually_of_forall fun i => (ENNReal.continuous_coe.comp (fs i).continuous).measurable) ?_
    (@lintegral_const_lt_top _ _ μ _ _ (@ENNReal.coe_ne_top c)).ne ?_
  · simpa only [Function.comp_apply, ENNReal.coe_le_coe] using fs_le_const
  · simpa only [Function.comp_apply, ENNReal.tendsto_coe] using fs_lim
#align measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const MeasureTheory.tendsto_lintegral_nn_filter_of_le_const

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : ι → Ω →ᵇ ℝ≥0)
    (fs_bdd : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c)
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i : ι => ((⇑) : (Ω →ᵇ ℝ≥0) → Ω → ℝ≥0) (fs i) ω) L
      (𝓝 (indicator E (fun _ => (1 : ℝ≥0)) ω))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) L (𝓝 (μ E)) := by
  convert tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : ∀ ω, indicator E (fun _ => (1 : ℝ≥0∞)) ω = ↑(indicator E (fun _ => (1 : ℝ≥0)) ω) :=
    fun ω => by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator _ E_mble]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
#align measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E)
    (fs : ℕ → Ω →ᵇ ℝ≥0) (fs_bdd : ∀ n ω, fs n ω ≤ c)
    (fs_lim : Tendsto (fun n : ℕ => ((⇑) : (Ω →ᵇ ℝ≥0) → Ω → ℝ≥0) (fs n)) atTop
      (𝓝 (indicator E fun _ => (1 : ℝ≥0)))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) atTop (𝓝 (μ E)) := by
  have fs_lim' :
    ∀ ω, Tendsto (fun n : ℕ => (fs n ω : ℝ≥0)) atTop (𝓝 (indicator E (fun _ => (1 : ℝ≥0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω => fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (eventually_of_forall fun n => eventually_of_forall (fs_bdd n)) (eventually_of_forall fs_lim')
#align measure_theory.measure_of_cont_bdd_of_tendsto_indicator MeasureTheory.measure_of_cont_bdd_of_tendsto_indicator

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
theorem tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ n, 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n => lintegral μ fun ω => (thickenedIndicator (δs_pos n) F ω : ℝ≥0∞)) atTop
      (𝓝 (μ F)) := by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n => thickenedIndicator (δs_pos n) F) fun n ω => thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key
#align measure_theory.tendsto_lintegral_thickened_indicator_of_is_closed MeasureTheory.tendsto_lintegral_thickenedIndicator_of_isClosed

end MeasureTheory -- namespace

end auxiliary -- section

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
  · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]
    rfl

end MeasureTheory -- namespace

end HasOuterApproxClosed -- section

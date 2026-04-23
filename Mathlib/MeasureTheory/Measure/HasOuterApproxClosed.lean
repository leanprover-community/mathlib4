/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.MetricSpace.ThickenedIndicator
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Spaces where indicators of closed sets have decreasing approximations by continuous functions

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

@[expose] public section

open BoundedContinuousFunction MeasureTheory Topology Metric Filter Set ENNReal NNReal
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
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i ↦ fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i ↦ ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ c)
    (Eventually.of_forall fun i ↦ (ENNReal.continuous_coe.comp (fs i).continuous).measurable) ?_
    (@lintegral_const_lt_top _ _ μ _ _ (@ENNReal.coe_ne_top c)).ne ?_
  · simpa only [Function.comp_apply, ENNReal.coe_le_coe] using fs_le_const
  · simpa only [Function.comp_apply, ENNReal.tendsto_coe] using fs_lim

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (μ : Measure Ω)
    [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : ι → Ω →ᵇ ℝ≥0)
    (fs_bdd : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c)
    (fs_lim : ∀ᵐ ω ∂μ, Tendsto (fun i ↦ fs i ω) L (𝓝 (indicator E (fun _ ↦ (1 : ℝ≥0)) ω))) :
    Tendsto (fun n ↦ lintegral μ fun ω ↦ fs n ω) L (𝓝 (μ E)) := by
  convert tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : ∀ ω, indicator E (fun _ ↦ (1 : ℝ≥0∞)) ω = ↑(indicator E (fun _ ↦ (1 : ℝ≥0)) ω) :=
    fun ω ↦ by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator E_mble]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E)
    (fs : ℕ → Ω →ᵇ ℝ≥0) (fs_bdd : ∀ n ω, fs n ω ≤ c)
    (fs_lim : Tendsto (fun n ω ↦ fs n ω) atTop (𝓝 (indicator E fun _ ↦ (1 : ℝ≥0)))) :
    Tendsto (fun n ↦ lintegral μ fun ω ↦ fs n ω) atTop (𝓝 (μ E)) := by
  have fs_lim' :
    ∀ ω, Tendsto (fun n : ℕ ↦ (fs n ω : ℝ≥0)) atTop (𝓝 (indicator E (fun _ ↦ (1 : ℝ≥0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω ↦ fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (Eventually.of_forall fun n ↦ Eventually.of_forall (fs_bdd n)) (Eventually.of_forall fs_lim')

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero. -/
theorem tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ n, 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n ↦ lintegral μ fun ω ↦ (thickenedIndicator (δs_pos n) F ω : ℝ≥0∞)) atTop
      (𝓝 (μ F)) := by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n ↦ thickenedIndicator (δs_pos n) F) fun n ω ↦ thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

/-- A thickened indicator is integrable. -/
lemma integrable_thickenedIndicator {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (F : Set Ω)
    {δ : ℝ} (δ_pos : 0 < δ) :
    Integrable (fun ω ↦ (thickenedIndicator δ_pos F ω : ℝ)) μ := by
  refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
  simpa using thickenedIndicator_le_one δ_pos F x

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero. -/
lemma tendsto_integral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ (n : ℕ), 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (thickenedIndicator (δs_pos n) F ω : ℝ) ∂μ) atTop (𝓝 (μ.real F)) := by
  -- we switch to the `lintegral` formulation and apply the corresponding lemma there
  let fs : ℕ → Ω → ℝ := fun n ω ↦ thickenedIndicator (δs_pos n) F ω
  have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ F_closed δs_pos δs_lim
  have h_eq (n : ℕ) : ∫⁻ ω, thickenedIndicator (δs_pos n) F ω ∂μ
      = ENNReal.ofReal (∫ ω, fs n ω ∂μ) := by
    rw [lintegral_coe_eq_integral]
    exact integrable_thickenedIndicator F (δs_pos _)
  simp_rw [h_eq] at h
  rw [Measure.real_def]
  have h_eq' : (fun n ↦ ∫ ω, fs n ω ∂μ) = fun n ↦ (ENNReal.ofReal (∫ ω, fs n ω ∂μ)).toReal := by
    ext n
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg fun x ↦ by simp [fs]
  rwa [h_eq', ENNReal.tendsto_toReal_iff (by simp) (by finiteness)]

end MeasureTheory -- namespace

end auxiliary -- section

section HasOuterApproxClosed

/-- A type class for topological spaces in which the indicator functions of closed sets can be
approximated pointwise from above by a sequence of bounded continuous functions. -/
class HasOuterApproxClosed (X : Type*) [TopologicalSpace X] : Prop where
  exAppr : ∀ (F : Set X), IsClosed F → ∃ (fseq : ℕ → (X →ᵇ ℝ≥0)),
    (∀ n x, fseq n x ≤ 1) ∧ (∀ n x, x ∈ F → 1 ≤ fseq n x) ∧
    Tendsto (fun n : ℕ ↦ (fun x ↦ fseq n x)) atTop (𝓝 (indicator F fun _ ↦ (1 : ℝ≥0)))

namespace HasOuterApproxClosed

variable {X : Type*} [TopologicalSpace X] [HasOuterApproxClosed X]
variable {F : Set X} (hF : IsClosed F)

/-- A sequence of continuous functions `X → [0,1]` tending to the indicator of a closed set. -/
noncomputable def _root_.IsClosed.apprSeq : ℕ → (X →ᵇ ℝ≥0) :=
  Exists.choose (HasOuterApproxClosed.exAppr F hF)

lemma apprSeq_apply_le_one (n : ℕ) (x : X) :
    hF.apprSeq n x ≤ 1 :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).1 n x

lemma apprSeq_apply_eq_one (n : ℕ) {x : X} (hxF : x ∈ F) :
    hF.apprSeq n x = 1 :=
  le_antisymm (apprSeq_apply_le_one _ _ _)
    ((Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.1 n x hxF)

lemma tendsto_apprSeq :
    Tendsto (fun n : ℕ ↦ (fun x ↦ hF.apprSeq n x)) atTop (𝓝 (indicator F fun _ ↦ (1 : ℝ≥0))) :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.2

lemma indicator_le_apprSeq (n : ℕ) :
    indicator F (fun _ ↦ 1) ≤ hF.apprSeq n := by
  intro x
  by_cases hxF : x ∈ F
  · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n, le_refl]
  · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

/-- The measure of a closed set is at most the integral of any function in a decreasing
approximating sequence to the indicator of the set. -/
theorem measure_le_lintegral [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (n : ℕ) :
    μ F ≤ ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂μ := by
  convert_to ∫⁻ x, (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) x ∂μ ≤ ∫⁻ x, hF.apprSeq n x ∂μ
  · rw [lintegral_indicator hF.measurableSet]
    simp only [lintegral_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  · apply lintegral_mono
    intro x
    by_cases hxF : x ∈ F
    · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n hxF, ENNReal.coe_one, le_refl]
    · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

/-- The integrals along a decreasing approximating sequence to the indicator of a closed set
tend to the measure of the closed set. -/
lemma tendsto_lintegral_apprSeq [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    Tendsto (fun n ↦ ∫⁻ x, hF.apprSeq n x ∂μ) atTop (𝓝 ((μ : Measure X) F)) :=
  measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet hF.apprSeq
    (apprSeq_apply_le_one hF) (tendsto_apprSeq hF)

end HasOuterApproxClosed --namespace

noncomputable instance (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] : HasOuterApproxClosed X := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  refine ⟨fun F hF ↦ ?_⟩
  use fun n ↦ thickenedIndicator (δ := (1 : ℝ) / (n + 1)) Nat.one_div_pos_of_nat F
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact fun n x ↦ thickenedIndicator_le_one Nat.one_div_pos_of_nat F x
  · exact fun n x hxF ↦ one_le_thickenedIndicator_apply X Nat.one_div_pos_of_nat hxF
  · have key := thickenedIndicator_tendsto_indicator_closure
              (δseq := fun (n : ℕ) ↦ (1 : ℝ) / (n + 1))
              (fun _ ↦ Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat F
    rw [tendsto_pi_nhds] at *
    intro x
    nth_rw 2 [← IsClosed.closure_eq hF]
    exact key x

namespace MeasureTheory

/-- Two finite measures give equal values to all closed sets if the integrals of all bounded
continuous functions with respect to the two measures agree. -/
theorem measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) {F : Set Ω} (F_closed : IsClosed F) :
    μ F = ν F := by
  have ν_finite : IsFiniteMeasure ν := by
    constructor
    have whole := h 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_const,
      one_mul] at whole
    simp [← whole]
  have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed μ
  have obs_ν := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed ν
  simp_rw [h] at obs_μ
  exact tendsto_nhds_unique obs_μ obs_ν

/-- Two finite Borel measures are equal if the integrals of all non-negative bounded continuous
functions with respect to both agree. -/
theorem ext_of_forall_lintegral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
    μ = ν := by
  have key := @measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure Ω _ _ _ _ μ ν _ h
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F F_closed ↦ key F_closed
  · exact key isClosed_univ
  · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]

/-- Two finite Borel measures are equal if the integrals of all bounded continuous functions with
respect to both agree. -/
theorem ext_of_forall_integral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Ω →ᵇ ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ, toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

end MeasureTheory -- namespace

end HasOuterApproxClosed -- section

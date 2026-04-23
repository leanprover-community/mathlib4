/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
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
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Neighborhoods

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
* the type `MeasureTheory.ProbabilityMeasure Ω` with the topology of convergence in
  distribution (a.k.a. convergence in law, weak convergence of measures);
* `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`: Interpret a probability measure as
  a finite measure;
* `MeasureTheory.FiniteMeasure.normalize`: Normalize a finite measure to a probability measure
  (returns junk for the zero measure).
* `MeasureTheory.ProbabilityMeasure.map`: The push-forward `f* μ` of a probability measure
  `μ` on `Ω` along a measurable function `f : Ω → Ω'`.

## Main results

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of
  probability measures is characterized by the convergence of expected values of all bounded
  continuous random variables. This shows that the chosen definition of topology coincides with
  the common textbook definition of convergence in distribution, i.e., weak convergence of
  measures. A similar characterization by the convergence of expected values (in the
  `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative random variables is
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`: The convergence of finite
  measures to a nonzero limit is characterized by the convergence of the probability-normalized
  versions and of the total masses.
* `MeasureTheory.ProbabilityMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of probability measures `f* : ProbabilityMeasure Ω → ProbabilityMeasure Ω'` is
  continuous.
* `MeasureTheory.ProbabilityMeasure.t2Space`: The topology of convergence in distribution is
  Hausdorff on Borel spaces where indicators of closed sets have continuous decreasing
  approximating sequences (in particular on any pseudo-metrizable spaces).

TODO:
* Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `MeasureTheory.ProbabilityMeasure Ω` is inherited
weak convergence of finite measures via the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Like `MeasureTheory.FiniteMeasure Ω`, the implementation of `MeasureTheory.ProbabilityMeasure Ω`
is directly as a subtype of `MeasureTheory.Measure Ω`, and the coercion to a function is the
composition `ENNReal.toNNReal` and the coercion to function of `MeasureTheory.Measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/

@[expose] public section


noncomputable section

open Set Filter BoundedContinuousFunction Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section ProbabilityMeasure

/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`MeasureTheory.ProbabilityMeasure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.ProbabilityMeasure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/


/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

instance [Inhabited Ω] : Inhabited (ProbabilityMeasure Ω) :=
  ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

/-- Coercion from `MeasureTheory.ProbabilityMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
def toMeasure : ProbabilityMeasure Ω → Measure Ω := Subtype.val

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω) := { coe := toMeasure }

instance (μ : ProbabilityMeasure Ω) : IsProbabilityMeasure (μ : Measure Ω) :=
  μ.prop

@[simp, norm_cast] lemma coe_mk (μ : Measure Ω) (hμ) : toMeasure ⟨μ, hμ⟩ = μ := rfl

@[simp]
theorem val_eq_to_measure (ν : ProbabilityMeasure Ω) : ν.val = (ν : Measure Ω) := rfl

theorem toMeasure_injective : Function.Injective ((↑) : ProbabilityMeasure Ω → Measure Ω) :=
  Subtype.coe_injective

instance instFunLike : FunLike (ProbabilityMeasure Ω) (Set Ω) ℝ≥0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
  coe_injective' μ ν h := toMeasure_injective <| Measure.ext fun s _ ↦ by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

lemma coeFn_def (μ : ProbabilityMeasure Ω) : μ = fun s ↦ ((μ : Measure Ω) s).toNNReal := rfl

lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ (μ s).toNNReal := rfl

@[simp, norm_cast]
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl

@[simp, norm_cast]
theorem coeFn_univ (ν : ProbabilityMeasure Ω) : ν univ = 1 :=
  congr_arg ENNReal.toNNReal ν.prop.measure_univ

@[simp]
theorem coeFn_empty (ν : ProbabilityMeasure Ω) : ν ∅ = 0 := by simp [coeFn_def]

theorem coeFn_univ_ne_zero (ν : ProbabilityMeasure Ω) : ν univ ≠ 0 := by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]

@[simp] theorem measureReal_eq_coe_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν : Measure Ω).real s = ν s := by
  simp [coeFn_def, Measure.real, ENNReal.toReal]

theorem toNNReal_measureReal_eq_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ((ν : Measure Ω).real s).toNNReal = ν s := by
  simp

/-- A probability measure can be interpreted as a finite measure. -/
def toFiniteMeasure (μ : ProbabilityMeasure Ω) : FiniteMeasure Ω := ⟨μ, inferInstance⟩

@[simp] lemma coeFn_toFiniteMeasure (μ : ProbabilityMeasure Ω) : ⇑μ.toFiniteMeasure = μ := rfl
lemma toFiniteMeasure_apply (μ : ProbabilityMeasure Ω) (s : Set Ω) :
    μ.toFiniteMeasure s = μ s := rfl

@[simp]
theorem toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω) := rfl

@[simp]
theorem coeFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Set Ω → ℝ≥0) = (ν : Set Ω → ℝ≥0) := rfl

@[simp]
theorem toFiniteMeasure_apply_eq_apply (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν.toFiniteMeasure s = ν s := rfl

@[simp]
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν s : ℝ≥0∞) = (ν : Measure Ω) s := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    toMeasure_comp_toFiniteMeasure_eq_toMeasure]

@[simp]
theorem null_iff_toMeasure_null (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν s = 0 ↔ (ν : Measure Ω) s = 0 :=
  ⟨fun h ↦ by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h ↦ congrArg ENNReal.toNNReal h⟩

@[gcongr]
theorem apply_mono (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_mono _ h

theorem apply_union_le (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_union_le _

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
protected lemma tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : ProbabilityMeasure Ω} {f : ι → Set Ω} :
    Tendsto (fun i ↦ μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)

@[simp] theorem apply_le_one (μ : ProbabilityMeasure Ω) (s : Set Ω) : μ s ≤ 1 := by
  simpa using apply_mono μ (subset_univ s)

theorem nonempty (μ : ProbabilityMeasure Ω) : Nonempty Ω :=
  nonempty_of_isProbabilityMeasure μ

@[ext]
theorem eq_of_forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble

theorem eq_of_forall_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (h s s_mble)

@[simp]
theorem mass_toFiniteMeasure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1 :=
  μ.coeFn_univ

@[simp] lemma range_toFiniteMeasure :
    range toFiniteMeasure = {μ : FiniteMeasure Ω | μ.mass = 1} := by
  ext μ
  simp only [mem_range, mem_setOf_eq]
  refine ⟨fun ⟨ν, hν⟩ ↦ by simp [← hν], fun h ↦ ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using h)⟩, ?_⟩
  ext s hs
  simp

theorem toFiniteMeasure_nonzero (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure ≠ 0 := by
  simp [← FiniteMeasure.mass_nonzero_iff]

/-- The type of probability measures is a measurable space when equipped with the Giry monad. -/
instance : MeasurableSpace (ProbabilityMeasure Ω) :=
  inferInstanceAs <| MeasurableSpace (Subtype _)

lemma measurableSet_isProbabilityMeasure :
    MeasurableSet { μ : Measure Ω | IsProbabilityMeasure μ } := by
  suffices { μ : Measure Ω | IsProbabilityMeasure μ } = (fun μ => μ univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext _
  apply isProbabilityMeasure_iff

/-- The monoidal product is a measurable function from the product of probability spaces over
`α` and `β` into the type of probability spaces over `α × β`. Lemma 4.1 of [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]. -/
theorem measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β)
      ↦ μ.1.toMeasure.prod μ.2.toMeasure) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod _
  simp only [mem_image2, mem_setOf_eq, forall_exists_index, and_imp]
  intro _ u Hu v Hv Heq
  simp_rw [← Heq, Measure.prod_prod]
  apply Measurable.mul
  · exact (Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst)
  · exact (Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd)

lemma apply_iUnion_le {μ : ProbabilityMeasure Ω} {f : ℕ → Set Ω}
    (hf : Summable fun n ↦ μ (f n)) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

section convergence_in_distribution

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

theorem testAgainstNN_lipschitz (μ : ProbabilityMeasure Ω) :
    LipschitzWith 1 fun f : Ω →ᵇ ℝ≥0 ↦ μ.toFiniteMeasure.testAgainstNN f :=
  μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz

/-- The topology of weak convergence on `MeasureTheory.ProbabilityMeasure Ω`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`. -/
instance : TopologicalSpace (ProbabilityMeasure Ω) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance

theorem toFiniteMeasure_continuous :
    Continuous (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) :=
  continuous_induced_dom

/-- Probability measures yield elements of the `WeakDual` of bounded continuous nonnegative
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration. -/
def toWeakDualBCNN : ProbabilityMeasure Ω → WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
  FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure

@[simp]
theorem coe_toWeakDualBCNN (μ : ProbabilityMeasure Ω) :
    ⇑μ.toWeakDualBCNN = μ.toFiniteMeasure.testAgainstNN := rfl

@[simp]
theorem toWeakDualBCNN_apply (μ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    μ.toWeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal := rfl

theorem toWeakDualBCNN_continuous : Continuous fun μ : ProbabilityMeasure Ω ↦ μ.toWeakDualBCNN :=
  FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
theorem continuous_testAgainstNN_eval (f : Ω →ᵇ ℝ≥0) :
    Continuous fun μ : ProbabilityMeasure Ω ↦ μ.toFiniteMeasure.testAgainstNN f :=
  (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous

-- The canonical mapping from probability measures to finite measures is an embedding.
theorem toFiniteMeasure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] :
    IsEmbedding (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) where
  eq_induced := rfl
  injective _μ _ν h := Subtype.ext <| congr_arg FiniteMeasure.toMeasure h

instance R1Space : R1Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).r1Space

theorem tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
    {μs : δ → ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ₀) ↔ Tendsto (toFiniteMeasure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  (toFiniteMeasure_isEmbedding Ω).tendsto_nhds_iff

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0,
        Tendsto (fun i ↦ ∫⁻ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_tendsto]

theorem tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ 𝕜,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]

variable {X : Type*} [TopologicalSpace X] {μs : X → ProbabilityMeasure Ω}

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
lemma continuous_iff_forall_continuous_lintegral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ≥0, Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
lemma continuous_iff_forall_continuous_integral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ, Continuous fun x ↦ ∫ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

lemma continuous_lintegral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ≥0) : Continuous fun μ : ProbabilityMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuous_lintegral.1 continuous_id _

lemma continuous_integral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ) : Continuous fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuous_integral.1 continuous_id _

variable [CompactSpace Ω]

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
lemma continuous_iff_forall_continuousMap_continuous_lintegral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ≥0), Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
lemma continuous_iff_forall_continuousMap_continuous_integral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ), Continuous fun x ↦ ∫ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {F : Type*}

lemma continuous_lintegral_continuousMap [FunLike F X ℝ≥0] [ContinuousMapClass F X ℝ≥0] (f : F) :
    Continuous fun μ : ProbabilityMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

lemma continuous_integral_continuousMap [FunLike F X ℝ] [ContinuousMapClass F X ℝ] (f : F) :
    Continuous fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

end convergence_in_distribution -- section

section Hausdorff

variable [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
variable (Ω)

/-- On topological spaces where indicators of closed sets have decreasing approximating sequences of
continuous functions (`HasOuterApproxClosed`), the topology of convergence in distribution of Borel
probability measures is Hausdorff (`T2Space`). -/
instance t2Space : T2Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).t2Space

end Hausdorff -- section

end ProbabilityMeasure

-- namespace
end ProbabilityMeasure

-- section
section NormalizeFiniteMeasure

/-! ### Normalization of finite measures to probability measures

This section is about normalizing finite measures to probability measures.

The weak convergence of finite measures to nonzero limit measures is characterized by
the convergence of the total mass and the convergence of the normalized probability
measures.
-/

namespace FiniteMeasure

variable {Ω : Type*} [Nonempty Ω] {m0 : MeasurableSpace Ω} (μ : FiniteMeasure Ω)

/-- Normalize a finite measure so that it becomes a probability measure, i.e., divide by the
total mass. -/
def normalize : ProbabilityMeasure Ω :=
  if zero : μ.mass = 0 then ⟨Measure.dirac ‹Nonempty Ω›.some, Measure.dirac.isProbabilityMeasure⟩
  else
    { val := μ.mass⁻¹ • (μ : Measure Ω)
      property := by
        refine ⟨?_⟩
        simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
          ENNReal.coe_inv zero, ennreal_mass]
        rw [← Ne, ← ENNReal.coe_ne_zero, ennreal_mass] at zero
        exact ENNReal.inv_mul_cancel zero μ.prop.measure_univ_lt_top.ne }

@[simp]
theorem self_eq_mass_mul_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s := by
  obtain rfl | h := eq_or_ne μ 0
  · simp
  have mass_nonzero : μ.mass ≠ 0 := by rwa [μ.mass_nonzero_iff]
  simp only [normalize, dif_neg mass_nonzero]
  simp [mul_inv_cancel_left₀ mass_nonzero, coeFn_def]

theorem self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure := by
  apply eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.self_eq_mass_mul_normalize s, smul_apply, smul_eq_mul,
    ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]

theorem normalize_eq_of_nonzero (nonzero : μ ≠ 0) (s : Set Ω) : μ.normalize s = μ.mass⁻¹ * μ s := by
  simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero, inv_mul_cancel_left₀,
    Ne, not_false_iff]

theorem normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ ≠ 0) :
    μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ := by
  nth_rw 3 [μ.self_eq_mass_smul_normalize]
  rw [← smul_assoc]
  simp only [μ.mass_nonzero_iff.mpr nonzero, smul_eq_mul, inv_mul_cancel₀, Ne,
    not_false_iff, one_smul]

theorem toMeasure_normalize_eq_of_nonzero (nonzero : μ ≠ 0) :
    (μ.normalize : Measure Ω) = μ.mass⁻¹ • μ := by
  ext1 s _s_mble
  rw [← μ.normalize.ennreal_coeFn_eq_coeFn_toMeasure s, μ.normalize_eq_of_nonzero nonzero s,
    ENNReal.coe_mul, ennreal_coeFn_eq_coeFn_toMeasure]
  exact Measure.coe_nnreal_smul_apply _ _ _

@[simp]
theorem _root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self {m0 : MeasurableSpace Ω}
    (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.normalize = μ := by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.toFiniteMeasure.normalize_eq_of_nonzero μ.toFiniteMeasure_nonzero s]
  simp only [ProbabilityMeasure.mass_toFiniteMeasure, inv_one, one_mul, μ.coeFn_toFiniteMeasure]

/-- Averaging with respect to a finite measure is the same as integrating against
`MeasureTheory.FiniteMeasure.normalize`. -/
theorem average_eq_integral_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (nonzero : μ ≠ 0) (f : Ω → E) :
    average (μ : Measure Ω) f = ∫ ω, f ω ∂(μ.normalize : Measure Ω) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero nonzero, average]
  congr
  simp [ENNReal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass]

variable [TopologicalSpace Ω]

theorem testAgainstNN_eq_mass_mul (f : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNN f = μ.mass * μ.normalize.toFiniteMeasure.testAgainstNN f := by
  nth_rw 1 [μ.self_eq_mass_smul_normalize]
  rw [μ.normalize.toFiniteMeasure.smul_testAgainstNN_apply μ.mass f, smul_eq_mul]

theorem normalize_testAgainstNN (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    μ.normalize.toFiniteMeasure.testAgainstNN f = μ.mass⁻¹ * μ.testAgainstNN f := by
  simp [μ.testAgainstNN_eq_mass_mul, inv_mul_cancel_left₀ <| μ.mass_nonzero_iff.mpr nonzero]

variable [OpensMeasurableSpace Ω]
variable {μ}

theorem tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*}
    {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (μs_lim : Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass)) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i ↦ (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f)) := by
  by_cases h_mass : μ.mass = 0
  · simp only [μ.mass_zero_iff.mp h_mass, zero_testAgainstNN_apply, zero_mass] at mass_lim ⊢
    exact tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  simp_rw [fun i ↦ (μs i).testAgainstNN_eq_mass_mul f, μ.testAgainstNN_eq_mass_mul f]
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at μs_lim
  rw [tendsto_iff_forall_testAgainstNN_tendsto] at μs_lim
  have lim_pair :
    Tendsto (fun i ↦ (⟨(μs i).mass, (μs i).normalize.toFiniteMeasure.testAgainstNN f⟩ : ℝ≥0 × ℝ≥0))
      F (𝓝 ⟨μ.mass, μ.normalize.toFiniteMeasure.testAgainstNN f⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨mass_lim, μs_lim f⟩
  exact tendsto_mul.comp lim_pair

theorem tendsto_normalize_testAgainstNN_of_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i ↦ (μs i).normalize.toFiniteMeasure.testAgainstNN f) F
      (𝓝 (μ.normalize.toFiniteMeasure.testAgainstNN f)) := by
  have lim_mass := μs_lim.mass
  have aux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero)
  have eventually_nonzero : ∀ᶠ i in F, μs i ≠ 0 := by
    simp_rw [← mass_nonzero_iff]
    exact lim_mass aux
  have eve : ∀ᶠ i in F,
      (μs i).normalize.toFiniteMeasure.testAgainstNN f =
        (μs i).mass⁻¹ * (μs i).testAgainstNN f := by
    filter_upwards [eventually_iff.mp eventually_nonzero]
    intro i hi
    apply normalize_testAgainstNN _ hi
  simp_rw [tendsto_congr' eve, μ.normalize_testAgainstNN nonzero]
  have lim_pair :
    Tendsto (fun i ↦ (⟨(μs i).mass⁻¹, (μs i).testAgainstNN f⟩ : ℝ≥0 × ℝ≥0)) F
      (𝓝 ⟨μ.mass⁻¹, μ.testAgainstNN f⟩) := by
    refine (Prod.tendsto_iff _ _).mpr ⟨?_, ?_⟩
    · exact (continuousOn_inv₀.continuousAt aux).tendsto.comp lim_mass
    · exact tendsto_iff_forall_testAgainstNN_tendsto.mp μs_lim f
  exact tendsto_mul.comp lim_pair

/-- If the normalized versions of finite measures converge weakly and their total masses
also converge, then the finite measures themselves converge weakly. -/
theorem tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure Ω} (μs_lim : Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass)) : Tendsto μs F (𝓝 μ) := by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f ↦
    tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass μs_lim mass_lim f

/-- If finite measures themselves converge weakly to a nonzero limit measure, then their
normalized versions also converge weakly. -/
theorem tendsto_normalize_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) :
    Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f ↦ tendsto_normalize_testAgainstNN_of_tendsto μs_lim nonzero f

/-- The weak convergence of finite measures to a nonzero limit can be characterized by the weak
convergence of both their normalized versions (probability measures) and their total masses. -/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (nonzero : μ ≠ 0) :
    Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize) ∧
        Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass) ↔
      Tendsto μs F (𝓝 μ) := by
  constructor
  · rintro ⟨normalized_lim, mass_lim⟩
    exact tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normalized_lim mass_lim
  · intro μs_lim
    exact ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩

end FiniteMeasure --namespace

end NormalizeFiniteMeasure -- section

section map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

namespace ProbabilityMeasure

/-- The push-forward of a probability measure by a measurable function. -/
noncomputable def map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν) :
    ProbabilityMeasure Ω' :=
  ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isProbabilityMeasure_map f_aemble⟩

@[simp] lemma toMeasure_map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (hf : AEMeasurable f ν) :
    (ν.map hf).toMeasure = ν.toMeasure.map f := rfl

/-- Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.ProbabilityMeasure.map_apply` for the corresponding equality as elements of `ℝ≥0`. -/
lemma map_apply' (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply_of_aemeasurable f_aemble A_mble

lemma map_apply_of_aemeasurable (ν : ProbabilityMeasure Ω) {f : Ω → Ω'}
    (f_aemble : AEMeasurable f ν) {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) := by
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr <|
    ν.map_apply' f_aemble A_mble

lemma map_apply (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) :=
  map_apply_of_aemeasurable ν f_aemble A_mble

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
convergence (in distribution) of `ProbabilityMeasure`s on `X` implies convergence (in
distribution) of the push-forwards of these measures by `f`. -/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι → ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω → Ω'} (f_cont : Continuous f) :
    Tendsto (fun i ↦ (νs i).map f_cont.measurable.aemeasurable) L
      (𝓝 (ν.map f_cont.measurable.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
the push-forward of probability measures `f* : ProbabilityMeasure X → ProbabilityMeasure Y`
is continuous (in the topologies of convergence in distribution). -/
lemma continuous_map {f : Ω → Ω'} (f_cont : Continuous f) :
    Continuous (fun ν ↦ ProbabilityMeasure.map ν f_cont.measurable.aemeasurable) := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

end ProbabilityMeasure -- namespace

end map -- section

section join_bind

theorem isProbabilityMeasure_join {α : Type*} [MeasurableSpace α] {m : Measure (Measure α)}
    [IsProbabilityMeasure m] (hm : ∀ᵐ μ ∂m, IsProbabilityMeasure μ) :
    IsProbabilityMeasure (m.join) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

theorem isProbabilityMeasure_bind {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} [IsProbabilityMeasure m] {f : α → Measure β} (hf₀ : AEMeasurable f m)
    (hf₁ : ∀ᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProbabilityMeasure (m.bind f) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
  simp_rw [isProbabilityMeasure_iff] at hf₁
  exact lintegral_eq_const hf₁

end join_bind

end MeasureTheory -- namespace

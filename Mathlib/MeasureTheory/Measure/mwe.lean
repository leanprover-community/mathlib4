import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

open Topology Filter Uniformity Uniform MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {α ι : Type*}

variable [MeasurableSpace α] {μ : Measure α}

/-- A measure `μ` is separable if there is a separable set `S` such that `μ S = μ Set.univ`. -/
 def IsSeparable [TopologicalSpace α] (μ : Measure α) : Prop :=
   ∃ S : Set α, TopologicalSpace.IsSeparable S ∧ μ S = μ Set.univ

/-- A measure `μ` is pre-tight if for all `0 < ε`, there exists `K` totally bounded such that
  `μ Kᶜ ≤ ε`. -/
def IsPretight [UniformSpace α] (μ : Measure α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ ε

/-- Ulam tightness theorem, which I have already proven. -/
lemma of_separableSpace_on_metric [PseudoMetricSpace α] [TopologicalSpace.SeparableSpace α]
    [OpensMeasurableSpace α] [IsFiniteMeasure μ] : IsPretight μ := by
  sorry

-- The proof idea is simple: if `μ` is separable, then there exists a separable set `S` such that
-- `μ S = μ Set.univ`. On this subspace, we can invoke `of_separableSpace_on_metric` to get that
-- `μ` is pre-tight on this subspace. As this has full measure, we want to lift this back.
lemma of_isSeparable_on_metric [PseudoMetricSpace α] [OpensMeasurableSpace α]
    (h : IsSeparable μ) [IsFiniteMeasure μ] : IsPretight μ := by
  obtain ⟨S, hS, hSμ⟩ := h
  have : TopologicalSpace.PseudoMetrizableSpace (closure S) := by
    infer_instance
  have : TopologicalSpace.SeparableSpace (closure S) := by
    have hSc := TopologicalSpace.IsSeparable.closure hS
    have : closure S = Set.univ (α := closure S) := by
      exact (Subtype.coe_image_univ (closure S)).symm
    rw [this] at hSc
    sorry
  have := of_separableSpace_on_metric (α := closure S) -- fails

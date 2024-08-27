import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter Set Function
open scoped Topology NNReal Pointwise

#check Nat.instMeasurableSpace

def MulAction.IsWanderingPoint (M : Type*) [One M] [TopologicalSpace M]
    {X : Type*} [TopologicalSpace X] [SMul M X] (x : X) : Prop :=
  ∀ V ∈ 𝓝 (1 : M), ∃ U ∈ 𝓝 x, ∀ g ∉ V, Disjoint (g • U) U

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

-- TODO: likely limit set or Milnor attractor?
def milnorAttractor (f : X → X) (μ : Measure X) : Set X :=
  ⋂₀ {s : Set X | IsClosed s ∧ ∀ᵐ x ∂μ, ∀ U ∈ 𝓝ˢ s, ∀ᶠ n in atTop, f^[n] x ∈ U}

theorem isClosed_milnorAttractor (f : X → X) (μ : Measure X) : IsClosed (milnorAttractor f μ) :=
  isClosed_sInter fun _ ↦ And.left

def IsWandering (f : X → X) (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ n > 0, Disjoint (f^[n] '' U) U

def nonwanderingSet (f : X → X) : Set X := {x | ¬IsWandering f x}

def statisticalAttractor (f : X → X) (μ : Measure X) : Set X :=
  ⋂₀ {s : Set X | IsClosed s ∧ ∀ U ∈ 𝓝ˢ s, ∀ᵐ x ∂μ,
    Tendsto (fun n : ℕ ↦ (Set.ncard {k | k < n ∧ f^[k] x ∈ U} / n : ℝ)) atTop (𝓝 1)}

def minimalAttractor (f : X → X) (μ : Measure X) : Set X :=
  ⋂₀ {s : Set X | IsClosed s ∧ ∀ U ∈ 𝓝ˢ s,
    Tendsto (birkhoffAverage ℝ≥0 (f ⁻¹' ·) μ · Uᶜ) atTop (𝓝 0)}

theorem minimalAttractor_subset_statisticalAttractor
    (f : X → X) (μ : Measure X) [IsFiniteMeasure μ] :
    minimalAttractor f μ ⊆ statisticalAttractor f μ := by
  refine sInter_subset_sInter fun s ⟨hsc, hs⟩ ↦ ⟨hsc, fun U hU ↦ ?_⟩
  simp only [birkhoffAverage, birkhoffSum, ← preimage_iterate_eq, ENNReal.tendsto_nhds_zero]
  intro ε hε
  have := tendstoInMeasure_of_tendsto_ae ?_ (hs U hU)
  

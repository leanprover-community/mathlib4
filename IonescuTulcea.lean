import Mathlib.KolmogorovExtension4.Transition
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.Probability.Kernel.MeasureCompProd

open MeasureTheory ProbabilityTheory Set

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

theorem test
    (κ : (k : ℕ) → kernel ((transitionGraph X).node k) ((transitionGraph X).path k (k + 1)))
    [∀ k, IsMarkovKernel (κ k)]
    (μ : Measure ((transitionGraph X).node 0)) [IsProbabilityMeasure μ] :
    ∃ ν : Measure ((k : ℕ) → X k), ∀ k : ℕ, (hk : 0 < k) →
    ν.map (fun x (i : Iic k) ↦ x i) =
    (μ ⊗ₘ (MeasurableSpaceGraph.transition κ).ker 0 k).map ((transitionGraph X).el 0 k hk) := by sorry

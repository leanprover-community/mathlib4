import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Condexp

open MeasureTheory ProbabilityTheory

example {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableEq Ω] [StandardBorelSpace (Fin n → Ω)] {μ : Fin n → Measure Ω}
    [∀ i, IsProbabilityMeasure (μ i)] (k : Fin (n + 1)) :
    condExpKernel (Measure.pi μ) (MeasurableSpace.piPrefix Ω k)
      =ᵐ[(Measure.pi μ).trim (MeasurableSpace.piPrefix_le_pi Ω k)]
        Kernel.piPrefixTail Ω μ k :=
  ProbabilityTheory.condExpKernel_piPrefix_eq_dirac_prod_pi (μ := μ) k

example {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableEq Ω] [StandardBorelSpace (Fin n → Ω)] {μ : Fin n → Measure Ω}
    [∀ i, IsFiniteMeasure (μ i)] (k : Fin (n + 1)) :
    ∀ᵐ S ∂((Measure.pi μ).trim (MeasurableSpace.piPrefix_le_pi Ω k)),
      ∀ᵐ T ∂(condExpKernel (Measure.pi μ) (MeasurableSpace.piPrefix Ω k) S),
        ∀ i : Fin n, (i : ℕ) < (k : ℕ) → T i = S i :=
  ProbabilityTheory.condExpKernel_piPrefix_ae_eq (μ := μ) k

example (p : unitInterval) (k : Fin 4) :
    ∀ᵐ S ∂((Measure.pi (fun _ : Fin 3 =>
        ProbabilityTheory.bernoulliMeasure false true p)).trim
          (MeasurableSpace.piPrefix_le_pi Bool k)),
      ∀ᵐ T ∂(condExpKernel
          (Measure.pi (fun _ : Fin 3 => ProbabilityTheory.bernoulliMeasure false true p))
          (MeasurableSpace.piPrefix Bool k) S),
        ∀ i : Fin 3, (i : ℕ) < (k : ℕ) → T i = S i :=
  ProbabilityTheory.condExpKernel_piPrefix_ae_eq
    (μ := fun _ : Fin 3 => ProbabilityTheory.bernoulliMeasure false true p) k

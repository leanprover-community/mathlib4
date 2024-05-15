import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Boxes

variable (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)]



theorem test (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

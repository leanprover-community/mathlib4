import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped Classical BigOperators Topology ENNReal
open Filter MeasureTheory NormedSpace Set

noncomputable section

variable? [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [BorelSpace W] => [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W]
variable {U : Set V}

/-
lemma emeasure_cball_aux:
  assumes "finite A" "r > 0"
  shows   "emeasure (Pi⇩M A (λ_. lborel))
             ({f. sqrt (∑i∈A. (f i)⇧2) ≤ r} ∩ space (Pi⇩M A (λ_. lborel))) =
             ennreal (unit_ball_vol (real (card A)) * r ^ card A)"
-/

example [Fintype ι] {r : ℝ} (h : 0 < r) :
    volume { x : ι → ℝ | ∑ i, (x i) ^ 2 ≤ r } = sorry := by
  rw [← ofReal_set_integral_one_of_measure_ne_top sorry]
  sorry

def myBall [Fintype ι] (r : ℝ) : Set (ι → ℝ) :=
  { x : ι → ℝ | ∑ i, (x i) ^ 2 ≤ r }

def expectedVolume (n : ℕ) (r : ℝ) : ℝ := sorry * r ^ n

example [Fintype ι] (s : Finset ι) {r : ℝ} (h : 0 < r) {x : ι → ℝ} :
    marginal (fun _ ↦ volume) s (indicator (myBall r) 1) x =
    .ofReal (expectedVolume s.card <| Real.sqrt <| 1 - ∑ i in sᶜ, (x i) ^ 2) := by
  sorry

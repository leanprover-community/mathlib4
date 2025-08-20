import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.Dual


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Metric

#check NormedSpace.polar_closedBall (𝕜 := ℝ) (E := E) (zero_lt_one)

-- lemma fromPR StronDual.polar
-- IsClosed (((↑) : StrongDual 𝕜 E → E → 𝕜) '' StrongDual.polar ℝ (ball 0 1)) =

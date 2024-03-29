import Mathlib

lemma foo (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (z : ℝ) (v : E) :
  z • v = (z : ℂ) • v := by exact?

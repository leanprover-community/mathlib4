import Mathlib.Analysis.Normed.Field.WithAbs

example (v : AbsoluteValue R ℝ) :
    (normedField v).toNormedCommRing.toNormedRing = (normedRing v) := by
  with_reducible_and_instances rfl

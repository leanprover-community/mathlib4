import Mathlib

example {R : Type*} [Field R] (v : AbsoluteValue R ℝ) :
    (WithAbs.normedField v).toNormedCommRing.toNormedRing = WithAbs.normedRing v := by
  with_reducible_and_instances rfl

import Mathlib

example {R : Type*} [Field R] (v : AbsoluteValue R ℝ) :
    (normedField v).toNormedCommRing.toNormedRing = normedRing v := by
  with_reducible_and_instances rfl

module

public import Mathlib
import all Mathlib.Analysis.Normed.Field.WithAbs

example {R : Type*} [Field R] (v : AbsoluteValue R ℝ) :
    (WithAbs.normedField v).toNormedCommRing.toNormedRing = WithAbs.normedRing v := by
  with_reducible_and_instances rfl

example {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (@Algebra.toSMul ℕ v.Completion _ _ inferInstance) = (@NSMul.toSMul v.Completion _) := by
  with_reducible_and_instances rfl

example {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (@Algebra.toSMul ℤ v.Completion _ _ inferInstance) = (@ZSMul.toSMul v.Completion _) := by
  with_reducible_and_instances rfl

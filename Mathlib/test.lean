import Mathlib

#check instCompleteSpaceRealToUniformSpacePseudoMetricSpace

lemma foo : CompleteSpace ℝ := by infer_instance


lemma bar1 {R : Type*} [Ring R] (a b : R) : a + b = b + a := by
  apply add_co

lemma bar {R : Type*} [CommRing R] (a b : R) : a * b = b * a := by
  exact mul_comm a b

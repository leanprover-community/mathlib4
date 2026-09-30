/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-! # Continuous functional calculus and projections

This file collects some results related to projections, idempotents,
and the continuous functional calculus. -/

public section

section Field
variable (R : Type*) {A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]

theorem isIdempotentElem_iff_quasispectrum_subset [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [NonUnitalContinuousFunctionalCalculus R A p]
    (a : A) (ha : p a) : IsIdempotentElem a ↔ quasispectrum R a ⊆ {0, 1} := by
  refine ⟨IsIdempotentElem.quasispectrum_subset R, fun h ↦ ?_⟩
  rw [IsIdempotentElem, ← cfcₙ_id' R a, ← cfcₙ_mul _ _]
  exact cfcₙ_congr fun x hx ↦ by grind

theorem isIdempotentElem_iff_spectrum_subset [Ring A] [StarRing A] [Algebra R A]
    [NonUnitalContinuousFunctionalCalculus R A p] (a : A) (ha : p a) :
    IsIdempotentElem a ↔ spectrum R a ⊆ {0, 1} := by
  grind [quasispectrum_eq_spectrum_union_zero, isIdempotentElem_iff_quasispectrum_subset R]

end Field

theorem isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star {A : Type*}
    [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {x : A} : IsIdempotentElem (star x * x) ↔ IsIdempotentElem (x * star x) := by
  simp [isIdempotentElem_iff_quasispectrum_subset ℝ, quasispectrum.mul_comm]

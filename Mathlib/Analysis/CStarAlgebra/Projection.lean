/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!

# Projections in C⋆-algebras

To show that an element is a star projection in a non-unital C⋆-algebra,
it is enough to show that it is idempotent and normal,
because self-adjointedness and normality are equivalent for idempotent
elements in non-unital C⋆-algebras.

-/

variable {A : Type*} [TopologicalSpace A]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An idempotent element in a non-unital C⋆-algebra is self-adjoint iff it is normal. -/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

/-- An element in a non-unital C⋆-algebra is a star projection
if and only if it is idempotent and normal. -/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsStarNormal p :=
  (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

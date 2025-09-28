/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Artinian rings over Jacobson rings

## Main results
- `Module.finite_iff_isArtinianRing`: If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an Artinian ring.

-/

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
lemma Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A] :
    Module.Finite R A :=
  (Finite.equiv_iff <|
    (AlgEquiv.ofRingEquiv (f := IsArtinianRing.equivPi A) fun _ ↦ rfl).toLinearEquiv).mpr <|
  have (I : MaximalSpectrum A) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  Finite.pi

/-- If `A` is a finite type algebra over `R`, then `A` is an Artinian ring and `R` is Jacobson
implies `A` is finite over `R`. -/
/- If made an instance, causes timeouts synthesizing `FaithfulSMul R I.ResidueField` at
`Ideal.algebraMap_residueField_eq_zero` and `Ideal.ker_algebraMap_residueField` during
simpNF linting. -/
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A] :
    Module.Finite R A :=
  have := finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A

/-- If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an Artinian ring. -/
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R] :
    Module.Finite R A ↔ IsArtinianRing A :=
  ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _ ↦ finite_of_isArtinianRing R A⟩

/-- If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `dim A = 0`. -/
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R] :
    Module.Finite R A ↔ Ring.KrullDimLE 0 A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero,
    and_iff_right this]

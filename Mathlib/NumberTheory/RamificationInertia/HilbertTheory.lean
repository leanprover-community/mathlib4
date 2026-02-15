/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`.

For `P` a prime ideal of `B`, the decomposition field `D` of `P` in `L/K` is the subfield of
elements of `L` fixed by the decomposition group, that the stabilizer, of `P` in `Gal(L/K)` and
the inertia field `E` of `P` in `L/K` is the subfield of elements of `L` fixed by the inertia
group of `P` in `Gal(L/K)`.

Implementation notes. It is convenient to also define the decomposition ring and inertia ring of
`P` which are, respectively, the subring of elements of `B` fixed by the decomposition group,
resp. inertia group` of `P` in `B ≃ₐ[A] B`.

In the case of number fields, the decomposition ring, resp. inertia ring, is the ring of integers
of the decomposition field, resp. inertia field.

-/

@[expose] public section

noncomputable section Basic

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] [MulSemiringAction Gal(L/K) B] (P : Ideal B)

open MulAction Pointwise Ideal

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The decomposition
field of `P` in `L/K` is the subfield fixed the decomposition subgroup of `P`, that is the
stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionField extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The inertia field
of `P` in `L/K` is the subfield fixed the inertia subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsInertiaField extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

instance [IsGalois K L] :
    IsDecompositionField K L P
      (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

instance [IsGalois K L] :
    IsInertiaField K L P
      (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable (𝓞D : Type*) [CommRing 𝓞D] [Algebra 𝓞D B]

/--
Let `A ⊆ B` be an extension of rings and let `P` be a prime ideal of `B `. The decomposition ring
of `P` is the subring of elements of `B` fixed the decomposition subgroup of `P`, that is the
stabilizer, of `P` in `B ≃ₐ[A] B`.
-/
@[mk_iff]
class IsDecompositionRing extends
    IsGaloisGroup (stabilizer (B ≃ₐ[A] B) P) 𝓞D B

variable (𝓞E : Type*) [CommRing 𝓞E] [Algebra 𝓞E B]

/--
Let `A ⊆ B` be an extension of rings and let `P` be a prime ideal of `B `. The inertia ring
of `P` is the subring of elements of `B` fixed the inertia subgroup of `P` in `B ≃ₐ[A] B`.
-/
@[mk_iff]
class IsInertiaRing extends
    IsGaloisGroup (inertia (B ≃ₐ[A] B) P) 𝓞E B

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L]
  [IsFractionRing B L]

/--
Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`. For `P` an ideal of `B`, the stabilizer of `P` in `B ≃ₐ[A] B` is
isomorphic to the stabilizer of `P` in `Gal(L/K)`.
-/
abbrev stabilizerEquivOfIsFractionRing [FaithfulSMul B L] [Algebra.IsAlgebraic K L] :
    stabilizer (B ≃ₐ[A] B) P ≃* stabilizer Gal(L/K)  P :=
  stabilizerEquiv P (galRestrict A K L B).symm
    (fun _ _ ↦ by
      apply FaithfulSMul.algebraMap_injective B L
      simp [algebraMap.smul, AlgEquiv.smul_def, galRestrict_symm_algebraMap_apply])

/--
Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`. For `P` an ideal of `B`, the inertia subgroup of `P` in `B ≃ₐ[A] B` is
isomorphic to the inertia subgroup of `P` in `Gal(L/K)`.
-/
abbrev inertiaEquivOfIsFractionRing [FaithfulSMul B L] [Algebra.IsAlgebraic K L] :
    inertia (B ≃ₐ[A] B) P ≃* inertia Gal(L/K)  P :=
  inertiaEquiv P (galRestrict A K L B).symm
    (fun _ _ ↦ by
      apply FaithfulSMul.algebraMap_injective B L
      simp [algebraMap.smul, AlgEquiv.smul_def, galRestrict_symm_algebraMap_apply])

/--
If `D` is the decomposition field of `P` in `L/K` and `𝓞D` is such that `D` is the fraction
field of `𝓞D`. Then `𝓞D` is the decomposition ring of `P` in `L/K`.
This cannot be an instance since Lean cannot infer `D`.
-/
theorem IsDecompositionRing.of_isDecompositionField [Algebra.IsAlgebraic K L] [Algebra 𝓞D D]
    [IsFractionRing 𝓞D D] [Algebra.IsIntegral 𝓞D B] [IsIntegrallyClosed 𝓞D] [Algebra 𝓞D L]
    [IsScalarTower 𝓞D B L] [IsScalarTower 𝓞D D L] [IsDecompositionField K L P D] :
    IsDecompositionRing A P 𝓞D where
  toIsGaloisGroup :=
    have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
    IsGaloisGroup.congr (stabilizerEquivOfIsFractionRing A K L P) (by simp)

/--
If `E` is the inertia field of `P` in `L/K` and `𝓞E ⊆ E` is such that `E` is the fraction
field of `𝓞E`. Then `𝓞E` is the decomposition ring of `P` in `L/K`.
This cannot be an instance since Lean cannot infer `E`.
-/
theorem IsInertiaRing.of_isInertiaField [Algebra.IsAlgebraic K L] [Algebra 𝓞E E]
    [IsFractionRing 𝓞E E] [Algebra.IsIntegral 𝓞E B] [IsIntegrallyClosed 𝓞E] [Algebra 𝓞E L]
    [IsScalarTower 𝓞E B L] [IsScalarTower 𝓞E E L] [IsInertiaField K L P E] :
    IsInertiaRing A P 𝓞E where
  toIsGaloisGroup :=
    have := IsGaloisGroup.of_isFractionRing (inertia Gal(L/K) P) 𝓞E B E L
    IsGaloisGroup.congr (inertiaEquivOfIsFractionRing A K L P) (by simp)

open NumberField in
/--
If the number field `D` is the decomposition field of `P` in `L/K`, then its ring of integers
is the decomposition ring of `P` in `L/K`.
-/
instance [Algebra.IsAlgebraic K L] [NumberField K] [NumberField L] [NumberField D]
    (P : Ideal (𝓞 L)) [IsDecompositionField K L P D] :
    IsDecompositionRing (𝓞 K) P (𝓞 D) := .of_isDecompositionField (𝓞 K) K L P D (𝓞 D)

open NumberField in
/--
If the number field `E` is the inertia field of `P` in `L/K`, then its ring of integers
is the inertia ring of `P` in `L/K`.
-/
instance [Algebra.IsAlgebraic K L] [NumberField K] [NumberField L] [NumberField E]
    (P : Ideal (𝓞 L)) [IsInertiaField K L P E] :
    IsInertiaRing (𝓞 K) P (𝓞 E) := .of_isInertiaField (𝓞 K) K L P E (𝓞 E)

end Basic

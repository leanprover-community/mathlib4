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

Let `L/K` be a Galois extension of fields. Let `P` be a prime ideal of the ring `B ⊆ L` above the
prime ideal `p` of the ring `A ⊆ K`.

The decomposition field `D` of `P` in `L/K` is the subfield of elements of `L` fixed by the
decomposition group, that the stabilizer, of `P` in `Gal(L/K)` and the inertia field `E` of `P`
in `L/K` is the subfield of elements of `L` fixed by the inertia group of `P` in `Gal(L/K)`.

Implementation notes. It is convenient to also define the decomposition ring and inertia ring of
`P` in `L/K` which are, respectively, the subring of elements of `B` fixed by the decomposition
group, resp. inertia group` of `P`.

In the case of number fields, the decomposition ring, resp. inertia ring, is the ring of integers
of the decomposition field, resp. inertia field.

-/

@[expose] public section

section Basic

variable (K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing B]
  [MulSemiringAction Gal(L/K) B] (P : Ideal B)

variable (D : Type*) [Field D] [Algebra D L]

open MulAction Pointwise Ideal

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of the ring `B ⊆ L`.
The decomposition field of `P` in `L/K` is the subfield fixed the decomposition subgroup of `P`,
that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionField extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

variable (𝓞D : Type*) [CommRing 𝓞D] [Algebra 𝓞D B]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of a subring `B ⊆ L`.
The decomposition ring of `P` in `L/K` is the subring of elements of `B` fixed the decomposition
subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionRing extends
    IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [CommRing 𝓞E] [Algebra 𝓞E B]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of a subring `B ⊆ L`.
The inertia field of `P` in `L/K` is the subfield fixed the inertia subgroup of `P`.
-/
@[mk_iff]
class IsInertiaField extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of a subring `B ⊆ L`.
The inertia ring of `P` in `L/K` is the subring of elements of `B` fixed the inertia
subgroup of `P`.
-/
@[mk_iff]
class IsInertiaRing extends
    IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B

instance [IsGalois K L] :
    IsDecompositionField K L P
      (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) :=
  { toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P) }

instance [IsGalois K L] :
    IsInertiaField K L P
      (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) :=
  { toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P) }

/--
If `D` is the decomposition field of `P` in `L/K` and `𝓞D ⊆ D` is such that `D` is the fraction
field of `𝓞D`. Then `𝓞D` is the decomposition ring of `P` in `L/K`.
This cannot be an instance since Lean cannot infer `D`.
-/
theorem IsDecompositionRing.of_isFractionRing [Algebra 𝓞D D] [IsFractionRing 𝓞D D]
    [Algebra.IsIntegral 𝓞D B] [IsIntegrallyClosed 𝓞D] [Algebra B L] [IsFractionRing B L]
    [Algebra 𝓞D L] [IsScalarTower 𝓞D B L] [IsScalarTower 𝓞D D L] [IsDecompositionField K L P D]
    [SMulDistribClass (stabilizer Gal(L/K) P) B L] :
    IsDecompositionRing K L P 𝓞D :=
  { toIsGaloisGroup := IsGaloisGroup.of_isFractionRing _ _ _ D L  }

/--
If `E` is the inertia field of `P` in `L/K` and `𝓞E ⊆ E` is such that `E` is the fraction
field of `𝓞E`. Then `𝓞E` is the decomposition ring of `P` in `L/K`.
This cannot be an instance since Lean cannot infer `E`.
-/
theorem IsInertiaRing.of_isFractionRing [Algebra 𝓞E E] [IsFractionRing 𝓞E E]
    [Algebra.IsIntegral 𝓞E B] [IsIntegrallyClosed 𝓞E] [Algebra B L] [IsFractionRing B L]
    [Algebra 𝓞E L] [IsScalarTower 𝓞E B L] [IsScalarTower 𝓞E E L] [IsInertiaField K L P E]
    [SMulDistribClass (inertia Gal(L/K) P) B L] :
    IsInertiaRing K L P 𝓞E :=
  { toIsGaloisGroup := IsGaloisGroup.of_isFractionRing _ _ _ E L  }

open NumberField in
/--
If the number field `D` is the decomposition field of `P` in `L/K`, then its ring of integers
is the decomposition ring of `P` in `L/K`.
-/
instance [NumberField D] [IsDecompositionField K L P D] [Algebra (𝓞 D) B]
    [Algebra.IsIntegral (𝓞 D) B] [Algebra B L] [IsScalarTower (𝓞 D) B L] [IsFractionRing B L]
    [SMulDistribClass (stabilizer Gal(L/K) P) B L] :
    IsDecompositionRing K L P (𝓞 D) := IsDecompositionRing.of_isFractionRing K L P D (𝓞 D)

open NumberField in
/--
If the number field `E` is the inertia field of `P` in `L/K`, then its ring of integers
is the inertia ring of `P` in `L/K`.
-/
instance [NumberField E] [IsInertiaField K L P E] [Algebra (𝓞 E) B]
    [Algebra.IsIntegral (𝓞 E) B] [Algebra B L] [IsScalarTower (𝓞 E) B L] [IsFractionRing B L]
    [SMulDistribClass (inertia Gal(L/K) P) B L] :
    IsInertiaRing K L P (𝓞 E) := IsInertiaRing.of_isFractionRing K L P E (𝓞 E)

end Basic

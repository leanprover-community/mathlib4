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
`K` fraction field of `A`, `L` fraction field of `B` and `B` the integral closure of `A` in `L`.

For `P` a prime ideal of `B`, the decomposition field `D` of `P` in `L/K` is the subfield of
elements of `L` fixed by the stabilizer of `P` in `Gal(L/K)`, and the inertia field `E` of `P`
in `L/K` is the subfield of elements of `L` fixed by the inertia group of `P` in `Gal(L/K)`.

-/

@[expose] public section

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

section basic

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionField K L P D :=  { toIsGaloisGroup := h }

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed the inertia
subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) D L] :
    IsInertiaField K L P D :=  { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]

instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] (G : Type*) [Group G]
    [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B]
    [SMulDistribClass G B L]

theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
  refine (isDecompositionField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

theorem IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) D L] :
    IsInertiaField K L P D := by
  refine (isInertiaField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      inertiaEquiv_symm_apply_smul]

end basic

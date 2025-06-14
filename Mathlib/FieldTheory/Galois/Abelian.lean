/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Galois.Infinite

/-!

# Abelian extensions

In this file, we define the typeclass of abelian extensions and provide some basic API.

-/

variable (K L M : Type*) [Field K] [Field L] [Algebra K L]
variable [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The class of abelian extensions,
defined as galois extensions whose galois group is commutative. -/
class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, Std.Commutative (α := L ≃ₐ[K] L) (· * ·)

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L] :
    CommGroup (L ≃ₐ[K] L) where
  mul_comm := Std.Commutative.comm

lemma IsAbelianGalois.tower_bot [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  have : IsGalois K L :=
    ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M).rangeRestrict
      ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩).transfer_galois
        (E' := (IsScalarTower.toAlgHom K L M).fieldRange)).mpr
      ((InfiniteGalois.normal_iff_isGalois _).mp inferInstance)
  { comm x y := by
      obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M x
      obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M y
      rw [← map_mul, ← map_mul, mul_comm] }

lemma IsAbelianGalois.tower_top [IsAbelianGalois K M] :
    IsAbelianGalois L M :=
  have : IsGalois L M := .tower_top_of_isGalois K L M
  { comm x y := AlgEquiv.restrictScalars_injective K
      (mul_comm (x.restrictScalars K) (y.restrictScalars K)) }

variable {K L M} in
omit [IsScalarTower K L M] [Algebra L M] in
lemma IsAbelianGalois.of_algHom (f : L →ₐ[K] M) [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  letI := f.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  .tower_bot K L M

instance [IsAbelianGalois K L] (K' : IntermediateField K L) : IsAbelianGalois K K' :=
  .tower_bot K K' L

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    (K' : IntermediateField K L) : IsAbelianGalois K' L :=
  .tower_top K _ L

lemma IsAbelianGalois.of_isCyclic [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    IsAbelianGalois K L :=
  letI := IsCyclic.commGroup (α := L ≃ₐ[K] L)
  ⟨⟩

/-
Copyright (c) 2024 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The tensor product is a coproduct in the category of commutative rings

In this file, we show that the tensor product over the integers is a coproduct in the category
of commutative rings, see `tensorProductColimit`.

-/

universe u

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace CommRingCat

variable (A B : CommRingCat.{u})

/-- The tensor product `A ⊗[ℤ] B` forms a cocone for `A` and `B`. -/
@[simps! pt ι]
def tensorProductCocone : BinaryCofan A B :=
BinaryCofan.mk
  (ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom : A ⟶  of (A ⊗[ℤ] B))
  (ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom : B ⟶  of (A ⊗[ℤ] B))

@[simp]
theorem tensorProductCocAone_inl : (tensorProductCocone A B).inl =
  ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom := rfl

@[simp]
theorem tensorProductCocone_inr : (tensorProductCocone A B).inr =
  ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom := rfl

/-- The tensor product `A ⊗[ℤ] B` is a coproduct for `A` and `B`. -/
@[simps]
def tensorProductColimit : IsColimit (tensorProductCocone A B) where
  desc (s : BinaryCofan A B) :=
    ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom
      (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := fun ⟨j⟩ => by cases j <;> ext a <;> simp
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A ⊗[ℤ] B →+* s.pt⟩ hm
    apply CommRingCat.hom_ext
    apply RingHom.toIntAlgHom_injective
    apply Algebra.TensorProduct.liftEquiv.symm.injective
    apply Subtype.ext
    rw [Algebra.TensorProduct.liftEquiv_symm_apply_coe, Prod.mk.injEq]
    constructor
    · ext a
      dsimp
      rw [map_one, mul_one]
      have : _ = s.inl := hm (Discrete.mk WalkingPair.left)
      rw [←this]
      rfl
    · ext b
      dsimp
      rw [map_one, one_mul]
      have : _ = s.inr := hm (Discrete.mk WalkingPair.right)
      rw [←this]
      rfl

/-- The limit cone of the tensor product `A ⊗[ℤ] B` in `CommRingCat`. -/
def tensorProductColimitCocone : Limits.ColimitCocone (pair A B) :=
  ⟨_, tensorProductColimit A B⟩

end CommRingCat

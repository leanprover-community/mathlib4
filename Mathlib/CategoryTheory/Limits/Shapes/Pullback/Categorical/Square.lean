/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-! # Categorical pullback squares

-/


universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.Limits
open scoped CategoricalPullback

section

open CategoricalPullback in
/-- A `CatPullbackSquare T L R B` asserts that a `CatCommSq T L R B` is a
categorical pullback square. This is realized as the data of a chosen
(adjoint) inverse to the canonical functor `C₁ ⥤ R ⊡ B` induced by
the square. The field of this struct are not intended to be accessed directly.
Instead one should use the corresponding fields of
`CatPullbackSquare.equivalence`. -/
class CatPullbackSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
    [CatCommSq T L R B] where
  /-- a chosen (adjoint) inverse to the canonical functor `C₁ ⥤ R ⊡ B`. -/
  inverse (T) (L) (R) (B) : R ⊡ B ⥤ C₁
  /-- the unit isomorphism for the equivalence -/
  unitIso (T) (L) (R) (B) :
    𝟭 C₁ ≅ (functorEquiv _ _ _).inverse.obj (.ofSquare T L R B) ⋙ inverse
  /-- the counit isomorphism for the equivalence -/
  counitIso (T) (L) (R) (B) :
    inverse ⋙ (functorEquiv _ _ _).inverse.obj (.ofSquare T L R B) ≅ 𝟭 (R ⊡ B)
  /-- the left triangle identity -/
  functorEquiv_inverse_obj_unitIso_comp (T) (L) (R) (B) (X : C₁) :
    ((functorEquiv _ _ _).inverse.obj (.ofSquare T L R B)).map
      (unitIso.hom.app X) ≫
      counitIso.hom.app
        (functorEquiv _ _ _|>.inverse.obj (.ofSquare T L R B)|>.obj X) =
    𝟙 _ := by aesop_cat

namespace CatPullbackSquare

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
    [CatCommSq T L R B] [CatPullbackSquare T L R B]

/-- The canonical equivalence `C₁ ≌ R ⊡ B` bundled by the fields of 
`CatPullbackSquare T L R B`. -/
@[simps! functor_obj_fst functor_obj_snd functor_obj_iso functor_obj_iso_hom
functor_obj_iso_inv functor_map_fst functor_map_snd]
def equivalence : C₁ ≌ R ⊡ B where
  functor :=
    (CategoricalPullback.functorEquiv _ _ _).inverse.obj (.ofSquare T L R B)
  inverse := inverse T L R B
  unitIso := unitIso T L R B
  counitIso := counitIso T L R B
  functor_unitIso_comp := functorEquiv_inverse_obj_unitIso_comp T L R B

variable {X : Type u₅} [Category.{v₅} X]

@[simps!]
def functorEquiv : (X ⥤ C₁) ≌ CategoricalPullback.CatCommSqOver R B X :=
  (equivalence T L R B).congrRight.trans <| 
    CategoricalPullback.functorEquiv R B X

end CatPullbackSquare

end CategoryTheory.Limits

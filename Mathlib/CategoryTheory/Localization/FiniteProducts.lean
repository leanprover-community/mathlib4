/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! The localized category has finite products

In this file, it is shown that if `L : C ⥤ D` is
a localization functor for `W : MorphismProperty C` and that
`W` is stable under finite products, then `D` has finite
products, and `L` preserves finite products.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  {W : MorphismProperty C} [L.IsLocalization W] [W.ContainsIdentities]

namespace HasProductsOfShapeAux

variable {J : Type} [Finite J] [HasProductsOfShape J C]
  (hW : W.IsStableUnderProductsOfShape J)

lemma inverts :
    (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (hW.lim_map f hf)

/-- The (candidate) limit functor for the localized category.
It is induced by `lim ⋙ L : (Discrete J ⥤ C) ⥤ D`. -/
noncomputable abbrev limitFunctor :
    (Discrete J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts L hW)
    ((whiskeringRight (Discrete J) C D).obj L)

/-- The functor `limitFunctor L hW` is induced by `lim ⋙ L`. -/
noncomputable def compLimitFunctorIso :
    ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFunctor L hW ≅
      lim ⋙ L := by
  apply Localization.fac

instance :
    CatCommSq (Functor.const (Discrete J)) L
      ((whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) where
  iso' := (Functor.compConstIso _ _).symm

noncomputable instance :
    CatCommSq lim ((whiskeringRight (Discrete J) C D).obj L) L (limitFunctor L hW) where
  iso' := (compLimitFunctorIso L hW).symm

/-- The adjunction between the constant functor `D ⥤ (Discrete J ⥤ D)`
and `limitFunctor L hW`. -/
noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L hW :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L hW)

lemma adj_counit_app (F : Discrete J ⥤ C) :
    (adj L hW).counit.app (F ⋙ L) =
      (Functor.const (Discrete J)).map ((compLimitFunctorIso L hW).hom.app F) ≫
        (Functor.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫
        whiskerRight (constLimAdj.counit.app F) L := by
  apply constLimAdj.localization_counit_app

/-- Auxiliary definition for `Localization.preservesProductsOfShape`. -/
noncomputable def isLimitMapCone (F : Discrete J ⥤ C) :
    IsLimit (L.mapCone (limit.cone F)) :=
  IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L hW) (F ⋙ L))
    (Cones.ext ((compLimitFunctorIso L hW).app F) (by simp [adj_counit_app, constLimAdj]))

end HasProductsOfShapeAux

variable (W)

lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    (hW : W.IsStableUnderProductsOfShape J) :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L hW).isLeftAdjoint

/-- When `C` has finite products indexed by `J`, `W : MorphismProperty C` contains
identities and is stable by products indexed by `J`,
then any localization functor for `W` preserves finite products indexed by `J`. -/
noncomputable def preservesProductsOfShape (J : Type) [Finite J]
    [HasProductsOfShape J C] (hW : W.IsStableUnderProductsOfShape J) :
    PreservesLimitsOfShape (Discrete J) L where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L hW F)

variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]

lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _
    (W.isStableUnderProductsOfShape_of_isStableUnderFiniteProducts _)⟩

/-- When `C` has finite products and `W : MorphismProperty C` contains
identities and is stable by finite products,
then any localization functor for `W` preserves finite products. -/
noncomputable def preservesFiniteProducts :
    PreservesFiniteProducts L where
  preserves J _ := preservesProductsOfShape L W J
      (W.isStableUnderProductsOfShape_of_isStableUnderFiniteProducts _)

instance : HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W

noncomputable instance : PreservesFiniteProducts W.Q := preservesFiniteProducts W.Q W

instance [W.HasLocalization] :
    HasFiniteProducts (W.Localization') :=
  hasFiniteProducts W.Q' W

noncomputable instance [W.HasLocalization] :
    PreservesFiniteProducts W.Q' :=
  preservesFiniteProducts W.Q' W

end Localization

end CategoryTheory

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

open Limits Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  (W : MorphismProperty C) [L.IsLocalization W]

namespace HasProductsOfShapeAux

variable (J : Type) [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J]

lemma inverts :
    (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [W.ContainsIdentities] [Finite J]

/-- The (candidate) limit functor for the localized category.
It is induced by `lim ⋙ L : (Discrete J ⥤ C) ⥤ D`. -/
noncomputable abbrev limitFunctor :
    (Discrete J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts L W J)
    ((whiskeringRight (Discrete J) C D).obj L)

/-- The functor `limitFunctor L W J` is induced by `lim ⋙ L`. -/
noncomputable def compLimitFunctorIso :
    ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFunctor L W J ≅
      lim ⋙ L := by
  apply Localization.fac

instance :
    CatCommSq (Functor.const (Discrete J)) L
      ((whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) where
  iso := (Functor.compConstIso _ _).symm

noncomputable instance :
    CatCommSq lim ((whiskeringRight (Discrete J) C D).obj L) L (limitFunctor L W J) where
  iso := (compLimitFunctorIso L W J).symm

/-- The adjunction between the constant functor `D ⥤ (Discrete J ⥤ D)`
and `limitFunctor L W J`. -/
noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L W J :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L W J)

lemma adj_counit_app (F : Discrete J ⥤ C) :
    (adj L W J).counit.app (F ⋙ L) =
      (Functor.const (Discrete J)).map ((compLimitFunctorIso L W J).hom.app F) ≫
        (Functor.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫
        whiskerRight (constLimAdj.counit.app F) L := by
  apply constLimAdj.localization_counit_app

/-- Auxiliary definition for `Localization.preservesProductsOfShape`. -/
noncomputable def isLimitMapCone (F : Discrete J ⥤ C) :
    IsLimit (L.mapCone (limit.cone F)) :=
  IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L W J) (F ⋙ L))
    (Cones.ext ((compLimitFunctorIso L W J).app F) (by simp [adj_counit_app, constLimAdj]))

end HasProductsOfShapeAux

variable [W.ContainsIdentities]

include L
lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    [W.IsStableUnderProductsOfShape J] :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L W J).isLeftAdjoint

/-- When `C` has finite products indexed by `J`, `W : MorphismProperty C` contains
identities and is stable by products indexed by `J`,
then any localization functor for `W` preserves finite products indexed by `J`. -/
lemma preservesProductsOfShape (J : Type) [Finite J]
    [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J] :
    PreservesLimitsOfShape (Discrete J) L where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L W J F)

variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]

include W in
lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _⟩

include W in
/-- When `C` has finite products and `W : MorphismProperty C` contains
identities and is stable by finite products,
then any localization functor for `W` preserves finite products. -/
lemma preservesFiniteProducts :
    PreservesFiniteProducts L where
  preserves _ := preservesProductsOfShape L W _

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

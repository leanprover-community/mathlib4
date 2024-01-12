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

/-! The localized category has finite products

In this file, it is shown that if `W : MorphismProperty C` and
`L : C ⥤ D` is a localization functor for `C`, then `D`
has finite products if `C` has finite products and `W` is
stable under finite products, and the localization functor
`L` preserves finite products.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
    (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities]

namespace HasProductsOfShapeAux

variable {W}
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

instance :
    CatCommSq (Functor.const (Discrete J)) L
      ((whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) where
  iso' := (Functor.compConstIso _ _).symm

noncomputable instance :
    CatCommSq lim ((whiskeringRight (Discrete J) C D).obj L) L (limitFunctor L hW) where
  iso' := (Lifting.iso _ (W.functorCategory (Discrete J)) (lim ⋙ L) _).symm

/-- The adjunction between the constant functor `D ⥤ (Discrete J ⥤ D)`
and `limitFunctor L hW`. -/
noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L hW :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L hW)

end HasProductsOfShapeAux

lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    (hW : W.IsStableUnderProductsOfShape J) :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    ⟨⟨_, HasProductsOfShapeAux.adj L hW⟩⟩

--noncomputable def preservesProductsOfShape (J : Type) [Finite J]
--    [HasProductsOfShape J C] (hW : W.IsStableUnderProductsOfShape J) :
--    PreservesLimitsOfShape (Discrete J) L := by
--  sorry

variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]

lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _
    (W.isStableUnderProductsOfShape_of_isStableUnderFiniteProducts _)⟩

--noncomputable def preservesFiniteProducts :
--    PreservesFiniteProducts L where
--  preserves J _ := preservesProductsOfShape L W J
--      (W.isStableUnderProductsOfShape_of_isStableUnderFiniteProducts _)

instance : HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W

--noncomputable instance :
--  PreservesFiniteProducts W.Q := preservesFiniteProducts W.Q W

instance [W.HasLocalization] :
    HasFiniteProducts (W.Localization') :=
  hasFiniteProducts W.Q' W

--noncomputable instance [W.HasLocalization] :
--    PreservesFiniteProducts W.Q' :=
--  preservesFiniteProducts W.Q' W

end Localization

end CategoryTheory

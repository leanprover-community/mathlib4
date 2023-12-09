/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.HasSheafify
/-!

This file proves that a sufficiently nice concrete category `D`, one can sheafify with `D` valued
presheaves.
-/

namespace CategoryTheory

open Limits

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (D : Type w) [Category.{max v u} D]
  [ConcreteCategory.{max v u} D]
  [PreservesLimits (forget D)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
  [ReflectsIsomorphisms (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

instance hasSheafifyOfPlusPlus : HasWeakSheafify J D where
  isRightAdjoint := ⟨inferInstance⟩

/--
The functor `plusPlusSheaf`, doing the plus construction twice, is isomorphic to any choice of
sheafification functor (by uniqueness of left adjoints).
-/
noncomputable
def presheafToSheafIsoPlusPlus : plusPlusSheaf J D ≅ presheafToSheaf J D :=
  Adjunction.leftAdjointUniq (plusPlusAdjunction J D) (sheafificationAdjunction J D)

-- porting note: added to ease the port of CategoryTheory.Sites.LeftExact
-- in mathlib, this was `by refl`, but here it would timeout
/--
"Sheafification" as an endofunctor of the presheaf category is isomorphic to sheafification
followed by inclusion.
-/
@[simps! hom_app inv_app]
noncomputable
def GrothendieckTopology.sheafificationIsoPresheafToSheafCompSheafToPreasheaf :
    J.sheafification D ≅ presheafToSheaf J D ⋙ sheafToPresheaf J D :=
  (NatIso.ofComponents fun P => Iso.refl _) ≪≫
    isoWhiskerRight (presheafToSheafIsoPlusPlus J D) (sheafToPresheaf J D)

end CategoryTheory

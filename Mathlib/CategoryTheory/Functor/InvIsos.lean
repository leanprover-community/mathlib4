/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.CategoryTheory.EqToHom

#align_import category_theory.functor.inv_isos from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Natural isomorphisms with composition with inverses

Definition of useful natural isomorphisms involving inverses of functors.
These definitions cannot go in `CategoryTheory/Equivalence` because they require `EqToHom`.
-/


namespace CategoryTheory

open CategoryTheory.Functor

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C]

variable {F : A ⥤ C} {G : A ⥤ B} {H : B ⥤ C}

/-- Construct an isomorphism `F ⋙ H.inv ≅ G` from an isomorphism `F ≅ G ⋙ H`. -/
@[simps!]
def compInvIso [h : IsEquivalence H] (i : F ≅ G ⋙ H) : F ⋙ H.inv ≅ G :=
  isoWhiskerRight i H.inv ≪≫
    associator G H H.inv ≪≫ isoWhiskerLeft G h.unitIso.symm ≪≫ eqToIso (Functor.comp_id G)
#align category_theory.comp_inv_iso CategoryTheory.compInvIso

/-- Construct an isomorphism `G ≅ F ⋙ H.inv` from an isomorphism `G ⋙ H ≅ F`. -/
@[simps!]
def isoCompInv [_h : IsEquivalence H] (i : G ⋙ H ≅ F) : G ≅ F ⋙ H.inv :=
  (compInvIso i.symm).symm
#align category_theory.iso_comp_inv CategoryTheory.isoCompInv

/-- Construct an isomorphism `G.inv ⋙ F ≅ H` from an isomorphism `F ≅ G ⋙ H`. -/
@[simps!]
def invCompIso [h : IsEquivalence G] (i : F ≅ G ⋙ H) : G.inv ⋙ F ≅ H :=
  isoWhiskerLeft G.inv i ≪≫
    (associator G.inv G H).symm ≪≫ isoWhiskerRight h.counitIso H ≪≫ eqToIso (Functor.id_comp H)
#align category_theory.inv_comp_iso CategoryTheory.invCompIso

/-- Construct an isomorphism `H ≅ G.inv ⋙ F` from an isomorphism `G ⋙ H ≅ F`. -/
@[simps!]
def isoInvComp [_h : IsEquivalence G] (i : G ⋙ H ≅ F) : H ≅ G.inv ⋙ F :=
  (invCompIso i.symm).symm
#align category_theory.iso_inv_comp CategoryTheory.isoInvComp

end CategoryTheory

/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Compatibilities of bifunctors acting on cochain complexes and shifts

-/

@[expose] public section

open CategoryTheory Category Limits

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

section

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

lemma map₂CochainComplex_obj_commShiftIso_hom_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso y).hom.app K₂ =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom := rfl

lemma map₂CochainComplex_obj_commShiftIso_inv_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso y).inv.app K₂ =
      (mapBifunctorShift₂Iso K₁ K₂ F y).inv := rfl

lemma map₂CochainComplex_flip_obj_commShiftIso_hom_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (x : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso x).hom.app K₁ =
      (mapBifunctorShift₁Iso K₁ K₂ F x).hom := rfl

lemma map₂CochainComplex_flip_obj_commShiftIso_inv_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (x : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso x).inv.app K₁ =
      (mapBifunctorShift₁Iso K₁ K₂ F x).inv := rfl

end

end CochainComplex

namespace HomotopyCategory

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F]

noncomputable instance (K₁ : HomotopyCategory C₁ (.up ℤ)) :
    ((F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).obj K₁).CommShift ℤ :=
  Quotient.commShiftOfFac ℤ (F.quotientCompBifunctorMapHomotopyObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K₁.as)

instance (K₁ : CochainComplex C₁ ℤ) :
    NatTrans.CommShift (F.quotientCompBifunctorMapHomotopyObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) K₁).hom ℤ := by
  apply Quotient.natTransCommshift_of_fac

noncomputable instance (K₂ : HomotopyCategory C₂ (.up ℤ)) :
    ((F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K₂).CommShift ℤ :=
  Quotient.commShiftOfFac ℤ (F.quotientCompBifunctorMapHomotopyFlipObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K₂.as)

instance (K₂ : CochainComplex C₂ ℤ) :
    NatTrans.CommShift (F.quotientCompBifunctorMapHomotopyFlipObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) K₂).hom ℤ := by
  apply Quotient.natTransCommshift_of_fac

end HomotopyCategory

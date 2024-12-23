/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.CatCenter.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Twisting the commutation isomorphisms of a functor with shifts

-/

namespace CategoryTheory

open Category

-- not sure this is useful...

namespace Functor

structure TwistCommShiftData (A : Type*) [AddMonoid A] (D : Type*)
    [Category D] [HasShift D A] where
  ε (a : A) : (CatCenter D)ˣ
  ε_zero : ε 0 = 1
  ε_add (a b : A) : ε (a + b) = ε a * ε b
  commutes (a b : A) : (shiftFunctor D a).CommutesWithCenterElement (ε b).val := by infer_instance

namespace TwistCommShiftData

attribute [simp] ε_zero

variable {A : Type*} [AddMonoid A] {D : Type*} [Category D] [HasShift D A]
  (t : TwistCommShiftData A D)

open Multiplicative
@[simps]
def mulHomε : Multiplicative A →* (CatCenter D)ˣ where
  toFun := t.ε
  map_one' := t.ε_zero
  map_mul' := t.ε_add

end TwistCommShiftData

variable {C D : Type*} [Category C] [Category D]
  (F : C ⥤ D) {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [F.CommShift A]

def twistCommShift (_ : TwistCommShiftData A D) : C ⥤ D := F

variable (t : TwistCommShiftData A D)

instance : (F.twistCommShift t).CommShift A where
  iso a :=
    (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft _ (CatCenter.unitsMulEquiv (t.ε a)) ≪≫
      Functor.rightUnitor _ ≪≫ F.commShiftIso a
  zero := by
    ext
    simp [twistCommShift, F.commShiftIso_zero]
  add a b := by
    have := t.commutes
    ext
    dsimp [twistCommShift]
    simp only [F.commShiftIso_add, t.ε_add, Units.val_mul, End.mul_def, NatTrans.comp_app,
      id_obj, CommShift.isoAdd_hom_app, comp_obj, id_comp, assoc, Iso.trans_hom,
      Iso.symm_hom, isoWhiskerLeft_hom, rightUnitor_inv_app, whiskerLeft_app,
      CatCenter.unitsMulEquiv_apply_hom_app, rightUnitor_hom_app, map_comp,
      map_app_of_commutesWithCenterElement]
    conv_rhs => rw [CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      CatCenter.naturality_assoc]

@[reassoc]
lemma twistCommShift_commShiftIso_hom_app (a : A) (X : C) :
    ((F.twistCommShift t).commShiftIso a).hom.app X =
      (t.ε a).val.app _ ≫ (F.commShiftIso a).hom.app X := by
  simp [twistCommShift, commShiftIso, CommShift.iso]

@[reassoc]
lemma twistCommShift_commShiftIso_inv_app (a : A) (X : C) :
    ((F.twistCommShift t).commShiftIso a).inv.app X =
      (t.ε a).inv.app _ ≫ (F.commShiftIso a).inv.app X := by
  rw [← CatCenter.naturality]
  simp [twistCommShift, commShiftIso, CommShift.iso]

end Functor

end CategoryTheory

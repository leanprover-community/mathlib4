/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# The right derived functor commutes with the shift

Let `L : C ⥤ H` be a localization functor with respect to `W : MorphismProperty C`.
Let `F : C ⥤ D`, `RF : H ⥤ D` and `α : F ⟶ L ⋙ RF` be a natural transformation
which makes `RF` the right derived functor of `F`. We assume that `C`, `D` and `H`
are equipped with shifts by an additive groupe `A`, that `L` and `F` commutes with these shifts,
and that `W` is compatible with the shift. Then, we show that `RF` commutes with
shifts, and that for this structure, the natural transformation `α` is compatible
with the shifts.


-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]
  (RF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (W : MorphismProperty C) [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A]

namespace IsRightDerivedFunctor

variable {A} (a : A)

/-- The natural transformation `shiftFunctor C a ⋙ F ⟶ L ⋙ shiftFunctor H a ⋙ RF`
deduced from `α : F ⟶ L ⋙ RF` when `L` commutes with the shift. -/
@[simps!]
def precomposeShiftNatTrans :
    shiftFunctor C a ⋙ F ⟶ L ⋙ shiftFunctor H a ⋙ RF :=
  whiskerLeft (shiftFunctor C a) α ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight (L.commShiftIso a).hom _ ≫ (Functor.associator _ _ _).hom

/-- The natural transformation `F ⋙ shiftFunctor D a ⟶ L ⋙ RF ⋙ shiftFunctor D a`
deduced from `α : F ⟶ L ⋙ RF` when `L` commutes with the shift. -/
@[simps!]
def postcomposeShiftNatTrans :
    F ⋙ shiftFunctor D a ⟶ L ⋙ RF ⋙ shiftFunctor D a :=
  whiskerRight α (shiftFunctor D a) ≫ (Functor.associator _ _ _).hom

instance :
    (shiftFunctor H a ⋙ RF).IsRightDerivedFunctor (precomposeShiftNatTrans RF α a) W := by
  have : RF.IsRightDerivedFunctor α W := inferInstance
  have : W.IsCompatibleWithShift A := inferInstance
  sorry
  /-((W.shiftLocalizerMorphism a).isRightDerivedFunctor_iff_precomp L L
    (shiftFunctor H a) (L.commShiftIso a) α (precomposeShiftNatTrans RF α a) (Iso.refl _)
    (Iso.refl _) (by aesop_cat)).2 inferInstance-/

instance :
    (RF ⋙ shiftFunctor D a).IsRightDerivedFunctor (postcomposeShiftNatTrans RF α a) W := by
  dsimp only [postcomposeShiftNatTrans]
  infer_instance

variable (A)

set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible]
noncomputable def commShift : RF.CommShift A where
  commShiftIso a := rightDerivedNatIso _ _ (precomposeShiftNatTrans RF α a)
    (postcomposeShiftNatTrans RF α a) W (F.commShiftIso a)
  commShiftIso_zero := by
    ext : 1
    apply rightDerived_ext _ (precomposeShiftNatTrans RF α 0) W
    ext X
    dsimp
    rw [dsimp% rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α 0)
      (postcomposeShiftNatTrans RF α 0) W (F.commShiftIso (0 : A)).hom X]
    simp only [commShiftIso_zero, CommShift.isoZero_hom_app, postcomposeShiftNatTrans_app,
      Category.assoc, precomposeShiftNatTrans_app, ← map_comp_assoc, Iso.inv_hom_id_app, id_obj,
      Category.comp_id]
    rw [← dsimp% (shiftFunctorZero D A).inv.naturality (α.app X)]
    simp
  commShiftIso_add a b := by
    ext : 1
    apply rightDerived_ext _ (precomposeShiftNatTrans RF α (a + b)) W
    ext X
    have ha := (shiftFunctor D b).congr_map (rightDerivedNatTrans_app _ _
      (precomposeShiftNatTrans RF α a) (postcomposeShiftNatTrans RF α _) W
      (F.commShiftIso _).hom X)
    rw [precomposeShiftNatTrans_app, postcomposeShiftNatTrans_app,
      Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc] at ha
    have hb := rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α b)
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom (X⟦a⟧) =≫
        (RF.map ((L.commShiftIso a).hom.app X))⟦b⟧'
    rw [Category.assoc, Category.assoc,
      ← dsimp% (rightDerivedNatTrans _ _ (precomposeShiftNatTrans RF α b)
        (postcomposeShiftNatTrans RF α b) W (commShiftIso F b).hom).naturality
        ((L.commShiftIso a).hom.app X), precomposeShiftNatTrans_app] at hb
    dsimp at ha hb ⊢
    rw [dsimp% rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α (a + b))
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom X]
    simp only [postcomposeShiftNatTrans_app, precomposeShiftNatTrans_app,
      CommShift.isoAdd_hom_app, comp_obj, rightDerivedNatIso_hom, Category.assoc,
      L.commShiftIso_add a b, ← RF.map_comp_assoc, Iso.inv_hom_id_app,
      Category.comp_id]
    rw [RF.map_comp_assoc, RF.map_comp, Category.assoc,
      ← dsimp% α.naturality_assoc ((shiftFunctorAdd C a b).hom.app X),
      reassoc_of% hb, postcomposeShiftNatTrans_app _ _ b, reassoc_of% ha,
      F.commShiftIso_add, CommShift.isoAdd_hom_app_assoc,
      ← NatTrans.naturality]
    dsimp

@[reassoc (attr := simp)]
lemma comp_map_commShiftIso_hom_app (a : A) (X : C) :
    letI := commShift RF α W A
    dsimp% α.app (X⟦a⟧) ≫ RF.map ((L.commShiftIso a).hom.app X) ≫
      (RF.commShiftIso a).hom.app (L.obj X) =
    (F.commShiftIso a).hom.app X ≫ (α.app X)⟦a⟧' := by
  simpa using (rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α a)
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom X)

attribute [local simp] commShiftIso_comp_hom_app in
instance natTrans_commShift :
    letI := commShift RF α W A
    NatTrans.CommShift α A :=
  letI := commShift RF α W A
  { }

noncomputable instance [HasRightDerivedFunctor F W] :
    (F.totalRightDerived L W).CommShift A :=
  commShift _ (F.totalRightDerivedUnit L W) W A

example [HasRightDerivedFunctor F W] :
    NatTrans.CommShift (F.totalRightDerivedUnit L W) A := inferInstance

end IsRightDerivedFunctor

end Functor

end CategoryTheory

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# The left derived functor commutes with the shift

Let `L : C ⥤ H` be a localization functor with respect to `W : MorphismProperty C`.
Let `F : C ⥤ D`, `LF : H ⥤ D` and `α : L ⋙ LF ⟶ F` be a natural transformation
which makes `LF` the left derived functor of `F`. We assume that `C`, `D` and `H`
are equipped with shifts by an additive group `A`, that `L` and `F` commute with these shifts,
and that `W` is compatible with the shift. Under these assumptions, we show that
`LF` commutes with shifts, and that for this structure, the natural
transformation `α` is compatible with the shifts.

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]
  [LF.IsLeftDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A]

namespace IsLeftDerivedFunctor

variable {A} (a : A)

/-- The natural transformation `L ⋙ shiftFunctor H a ⋙ LF ⟶ shiftFunctor C a ⋙ F`
deduced from `α : L ⋙ LF ⟶ F` when `L` commutes with the shift. -/
@[simps!]
def precomposeShiftNatTrans :
    L ⋙ shiftFunctor H a ⋙ LF ⟶ shiftFunctor C a ⋙ F :=
  (associator _ _ _).inv ≫ whiskerRight (L.commShiftIso a).inv _ ≫
    (associator _ _ _).hom ≫ whiskerLeft (shiftFunctor C a) α

/-- The natural transformation `F ⋙ shiftFunctor D a ⟶ L ⋙ LF ⋙ shiftFunctor D a`
deduced from `α : F ⟶ L ⋙ LF` when `L` commutes with the shift. -/
@[simps!]
def postcomposeShiftNatTrans :
    L ⋙ LF ⋙ shiftFunctor D a ⟶ F ⋙ shiftFunctor D a :=
  (associator _ _ _).inv ≫ whiskerRight α (shiftFunctor D a)

instance :
    (shiftFunctor H a ⋙ LF).IsLeftDerivedFunctor (precomposeShiftNatTrans LF α a) W := by
  rwa [← (W.shiftLocalizerMorphism a).isLeftDerivedFunctor_iff_precomp
    L L _ (L.commShiftIso a) (precomposeShiftNatTrans LF α a) α (Iso.refl _) (Iso.refl _)]

instance :
    (LF ⋙ shiftFunctor D a).IsLeftDerivedFunctor (postcomposeShiftNatTrans LF α a) W := by
  dsimp only [postcomposeShiftNatTrans]
  infer_instance

variable (A)

--set_option backward.isDefEq.respectTransparency false in
/-- The right derived functor commutes with the shift. -/
@[implicit_reducible]
noncomputable def commShift : LF.CommShift A where
  commShiftIso a := leftDerivedNatIso _ _ (precomposeShiftNatTrans LF α a)
    (postcomposeShiftNatTrans LF α a) W (F.commShiftIso a)
  commShiftIso_zero := sorry
  commShiftIso_add := sorry
  /-
  commShiftIso_zero := by
    ext : 1
    apply rightDerived_ext _ (precomposeShiftNatTrans LF α 0) W
    ext X
    dsimp
    rw [dsimp% rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans LF α 0)
      (postcomposeShiftNatTrans LF α 0) W (F.commShiftIso (0 : A)).hom X]
    simp only [commShiftIso_zero, CommShift.isoZero_hom_app, postcomposeShiftNatTrans_app,
      Category.assoc, precomposeShiftNatTrans_app, ← map_comp_assoc, Iso.inv_hom_id_app, id_obj,
      Category.comp_id]
    rw [← dsimp% (shiftFunctorZero D A).inv.naturality (α.app X)]
    simp
  commShiftIso_add a b := by
    ext : 1
    apply rightDerived_ext _ (precomposeShiftNatTrans LF α (a + b)) W
    ext X
    have ha := (shiftFunctor D b).congr_map (rightDerivedNatTrans_app _ _
      (precomposeShiftNatTrans LF α a) (postcomposeShiftNatTrans LF α _) W
      (F.commShiftIso _).hom X)
    rw [precomposeShiftNatTrans_app, postcomposeShiftNatTrans_app,
      map_comp, map_comp, map_comp, Category.assoc] at ha
    have hb := rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans LF α b)
      (postcomposeShiftNatTrans LF α _) W (F.commShiftIso _).hom (X⟦a⟧) =≫
        (LF.map ((L.commShiftIso a).hom.app X))⟦b⟧'
    rw [Category.assoc, Category.assoc,
      ← dsimp% (rightDerivedNatTrans _ _ (precomposeShiftNatTrans LF α b)
        (postcomposeShiftNatTrans LF α b) W (commShiftIso F b).hom).naturality
        ((L.commShiftIso a).hom.app X), precomposeShiftNatTrans_app] at hb
    dsimp at ha hb ⊢
    rw [dsimp% rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans LF α (a + b))
      (postcomposeShiftNatTrans LF α _) W (F.commShiftIso _).hom X]
    simp only [postcomposeShiftNatTrans_app, precomposeShiftNatTrans_app,
      CommShift.isoAdd_hom_app, comp_obj, rightDerivedNatIso_hom, Category.assoc,
      L.commShiftIso_add a b, ← LF.map_comp_assoc, Iso.inv_hom_id_app,
      Category.comp_id]
    rw [LF.map_comp_assoc, LF.map_comp, Category.assoc,
      ← dsimp% α.naturality_assoc ((shiftFunctorAdd C a b).hom.app X),
      reassoc_of% hb, postcomposeShiftNatTrans_app _ _ b, reassoc_of% ha,
      F.commShiftIso_add, CommShift.isoAdd_hom_app_assoc,
      ← NatTrans.naturality]
    dsimp-/

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma map_commShiftIso_hom_app_comp (a : A) (X : C) :
    letI := commShift LF α W A
    dsimp% LF.map ((L.commShiftIso a).hom.app X) ≫
      (commShiftIso LF a).hom.app (L.obj X) ≫ (α.app X)⟦a⟧' =
    α.app ((shiftFunctor C a).obj X) ≫ (commShiftIso F a).hom.app X := by
  simpa [← Functor.map_comp_assoc] using (LF.map ((L.commShiftIso a).hom.app X)) ≫=
    leftDerivedNatTrans_app _ _ (precomposeShiftNatTrans LF α a)
      (postcomposeShiftNatTrans LF α _) W (F.commShiftIso _).hom X

attribute [local simp] commShiftIso_comp_hom_app in
instance natTrans_commShift :
    letI := commShift LF α W A
    NatTrans.CommShift α A :=
  letI := commShift LF α W A
  { }

noncomputable instance [HasLeftDerivedFunctor F W] :
    (F.totalLeftDerived L W).CommShift A :=
  commShift _ (F.totalLeftDerivedCounit L W) W A

example [HasLeftDerivedFunctor F W] :
    NatTrans.CommShift (F.totalLeftDerivedCounit L W) A := inferInstance

end IsLeftDerivedFunctor

end Functor

end CategoryTheory

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

set_option backward.isDefEq.respectTransparency false in
/-- The right derived functor commutes with the shift. -/
@[implicit_reducible]
noncomputable def commShift : LF.CommShift A where
  commShiftIso a := leftDerivedNatIso _ _ (precomposeShiftNatTrans LF α a)
    (postcomposeShiftNatTrans LF α a) W (F.commShiftIso a)
  commShiftIso_zero := by
    ext : 1
    apply leftDerived_ext _ (postcomposeShiftNatTrans LF α 0) W
    ext X
    dsimp
    rw [dsimp% leftDerivedNatTrans_app _ _ (precomposeShiftNatTrans LF α (0 : A))
      (postcomposeShiftNatTrans LF α 0) W (F.commShiftIso 0).hom X]
    simp only [precomposeShiftNatTrans_app, commShiftIso_zero, CommShift.isoZero_inv_app, map_comp,
      Category.assoc, CommShift.isoZero_hom_app, postcomposeShiftNatTrans_app]
    simp [dsimp% α.naturality_assoc, ← Functor.map_comp_assoc,
      dsimp% (shiftFunctorZero D A).inv.naturality (α.app X)]
  commShiftIso_add a b := by
    ext : 1
    apply leftDerived_ext _ (postcomposeShiftNatTrans LF α (a + b)) W
    ext X
    have ha := (leftDerivedNatTrans_app _ _
      (precomposeShiftNatTrans LF α a) (postcomposeShiftNatTrans LF α _) W
      (F.commShiftIso _).hom X)
    have hb := (leftDerivedNatTrans_app _ _
      (precomposeShiftNatTrans LF α b) (postcomposeShiftNatTrans LF α _) W
      (F.commShiftIso _).hom (X⟦a⟧))
    simp only [comp_obj, postcomposeShiftNatTrans_app, precomposeShiftNatTrans_app,
      Category.assoc] at ha hb
    dsimp
    rw [leftDerivedNatTrans_app]
    simp only [precomposeShiftNatTrans_app, postcomposeShiftNatTrans_app,
      CommShift.isoAdd_hom_app, CommShift.isoAdd_inv_app, comp_obj,
      leftDerivedNatIso_hom, Category.assoc, commShiftIso_add,
      ← dsimp% (shiftFunctorAdd D a b).inv.naturality (α.app X),
      ← (shiftFunctor D b).map_comp_assoc, ha,
      ← dsimp% ((shiftFunctor H b ⋙ LF).leftDerivedNatTrans (LF ⋙ shiftFunctor D b)
        (precomposeShiftNatTrans LF α b)
        (postcomposeShiftNatTrans LF α b) W (commShiftIso F b).hom).naturality_1
      ((L.commShiftIso a).app X), ← LF.map_comp_assoc, Iso.hom_inv_id_app,
      map_id, Category.id_comp]
    simp only [map_comp_assoc, reassoc_of% hb,
      ← dsimp% α.naturality_assoc ((shiftFunctorAdd C a b).hom.app X)]
    simp [← Functor.map_comp_assoc, ← Functor.map_comp]

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

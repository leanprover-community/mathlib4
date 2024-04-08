import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Shift.Localization

namespace CategoryTheory

open Category

namespace MorphismProperty

variable {C : Type*} [Category C]
  (W : MorphismProperty C) {A : Type*} [AddGroup A] [HasShift C A]
  [W.IsCompatibleWithShift A] (a : A)

@[simps]
def localizerMorphismOfIsCompatibleWithShift :
    LocalizerMorphism W W where
  functor := shiftFunctor C a
  map _ _ f hf := (IsCompatibleWithShift.iff W f a).2 hf

noncomputable instance :
    IsEquivalence (W.localizerMorphismOfIsCompatibleWithShift a).functor := by
  dsimp
  infer_instance

instance : (W.localizerMorphismOfIsCompatibleWithShift a).IsLocalizedEquivalence := by
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  intro X Y f hf
  exact ⟨_, _, f⟦-a⟧', (IsCompatibleWithShift.iff W f _).2 hf,
    ⟨Arrow.isoOfNatIso (shiftEquiv C a).counitIso (Arrow.mk f)⟩⟩

end MorphismProperty

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]
  (RF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (W : MorphismProperty C)
  [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A]

namespace IsRightDerivedFunctor

variable {A}
variable (a : A)

@[simps!]
def precomposeShiftNatTrans :
    shiftFunctor C a ⋙ F ⟶ L ⋙ shiftFunctor H a ⋙ RF :=
  whiskerLeft (shiftFunctor C a) α ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight (L.commShiftIso a).hom _ ≫ (Functor.associator _ _ _).hom

@[simps!]
def postcomposeShiftNatTrans :
    F ⋙ shiftFunctor D a ⟶ L ⋙ (RF ⋙ shiftFunctor D a) :=
  whiskerRight α (shiftFunctor D a) ≫ (Functor.associator _ _ _).hom

instance :
    (shiftFunctor H a ⋙ RF).IsRightDerivedFunctor (precomposeShiftNatTrans RF α a) W :=
  ((W.localizerMorphismOfIsCompatibleWithShift a).isRightDerivedFunctor_iff_precomp L L
    (shiftFunctor H a) (L.commShiftIso a) α (precomposeShiftNatTrans RF α a) (Iso.refl _)
    (Iso.refl _) (by aesop_cat)).2 inferInstance

instance :
    (RF ⋙ shiftFunctor D a).IsRightDerivedFunctor (postcomposeShiftNatTrans RF α a) W := by
  apply isRightDerivedFunctor_postcomp

variable (A)

noncomputable def commShift : RF.CommShift A where
  iso a := rightDerivedNatIso _ _ (precomposeShiftNatTrans RF α a)
    (postcomposeShiftNatTrans RF α a) W (F.commShiftIso a)
  zero := by
    ext1
    apply rightDerived_ext _ (precomposeShiftNatTrans RF α 0) W
    ext X
    apply (rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α 0)
      (postcomposeShiftNatTrans RF α 0) W (F.commShiftIso (0 : A)).hom X).trans
    dsimp
    rw [postcomposeShiftNatTrans_app, precomposeShiftNatTrans_app, assoc,
      CommShift.isoZero_hom_app, commShiftIso_zero, commShiftIso_zero,
      CommShift.isoZero_hom_app, CommShift.isoZero_hom_app, assoc, RF.map_comp, assoc]
    erw [← α.naturality_assoc]
    rw [← RF.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp
    rw [RF.map_id, id_comp]
    erw [← NatTrans.naturality]
    dsimp
  add a b := by
    ext1
    apply rightDerived_ext _ (precomposeShiftNatTrans RF α (a + b)) W
    ext X
    apply (rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α (a + b))
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom X).trans
    dsimp
    rw [precomposeShiftNatTrans_app, CommShift.isoAdd_hom_app, rightDerivedNatIso_hom,
      rightDerivedNatIso_hom, assoc]
    dsimp

    have ha := (shiftFunctor D b).congr_map
      (rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α a)
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom X)
    rw [precomposeShiftNatTrans_app, postcomposeShiftNatTrans_app,
      Functor.map_comp, Functor.map_comp, Functor.map_comp, assoc] at ha

    have hb := rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α b)
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom (X⟦a⟧)
        =≫ (RF.map ((L.commShiftIso a).hom.app X))⟦b⟧'
    rw [assoc, assoc] at hb
    erw [← NatTrans.naturality] at hb
    rw [precomposeShiftNatTrans_app] at hb
    dsimp at ha hb

    rw [L.commShiftIso_add a b, CommShift.isoAdd_hom_app, map_comp, assoc,
      ← RF.map_comp_assoc, ← RF.map_comp_assoc, assoc, assoc, assoc, Iso.inv_hom_id_app]
    dsimp
    rw [comp_id, RF.map_comp, RF.map_comp, assoc, assoc]
    erw [← NatTrans.naturality_assoc]
    rw [reassoc_of% hb, postcomposeShiftNatTrans_app _ _ b, reassoc_of% ha,
      postcomposeShiftNatTrans_app, F.commShiftIso_add, CommShift.isoAdd_hom_app,
      assoc, assoc, assoc, ← NatTrans.naturality]
    rfl

@[reassoc (attr := simp)]
lemma comp_commShiftIso_hom (a : A) (X : C):
    letI := commShift RF α W A
    α.app (X⟦a⟧) ≫ RF.map ((L.commShiftIso a).hom.app X) ≫ (RF.commShiftIso a).hom.app (L.obj X) =
      (F.commShiftIso a).hom.app X ≫ ((shiftFunctor D a).map (α.app X)) := by
  simpa using (rightDerivedNatTrans_app _ _ (precomposeShiftNatTrans RF α a)
      (postcomposeShiftNatTrans RF α _) W (F.commShiftIso _).hom X)

lemma natTrans_commShift :
    letI := commShift RF α W A
    NatTrans.CommShift α A :=
  letI := commShift RF α W A
  { comm' := fun a => by
      ext X
      simp [commShiftIso_comp_hom_app]}

end IsRightDerivedFunctor

end Functor

end CategoryTheory

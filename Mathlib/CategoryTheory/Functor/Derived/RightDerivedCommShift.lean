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

/-noncomputable def commShift : RF.CommShift A where
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
    sorry-/

end IsRightDerivedFunctor

end Functor

end CategoryTheory

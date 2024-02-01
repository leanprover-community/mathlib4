import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]
  (LF LF' LF'' : H ⥤ D) {F F' F'' : C ⥤ D} (e : F ≅ F') {L : C ⥤ H}
  (α : L ⋙ LF ⟶ F) (α' : L ⋙ LF' ⟶ F') (α'' : L ⋙ LF'' ⟶ F'') (α'₂ : L ⋙ LF' ⟶ F)
  (W : MorphismProperty C)

class IsLeftDerivedFunctor [L.IsLocalization W] : Prop where
  isRightKanExtension' : LF.IsRightKanExtension α

lemma IsLeftDerivedFunctor.isRightKanExtension [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W] :
    LF.IsRightKanExtension α :=
  IsLeftDerivedFunctor.isRightKanExtension' W

section

variable [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]
  [LF'.IsLeftDerivedFunctor α' W] [LF''.IsLeftDerivedFunctor α'' W]

noncomputable def leftDerivedLift (G : H ⥤ D) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.rightKanExtensionLift α G β

@[reassoc (attr := simp)]
lemma leftDerived_fac (G : H ⥤ D) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (LF.leftDerivedLift α W G β) ≫ α = β :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.rightKanExtension_fac α G β

@[reassoc (attr := simp)]
lemma leftDerived_fac_app (G : H ⥤ D) (β : L ⋙ G ⟶ F) (X : C):
    (LF.leftDerivedLift α W G β).app (L.obj X) ≫ α.app X = β.app X:=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.rightKanExtension_fac_app α G β X

lemma leftDerived_ext (G : H ⥤ D) (γ₁ γ₂ : G ⟶ LF)
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.rightKanExtension_ext α γ₁ γ₂ hγ

noncomputable def leftDerivedNatTrans (τ : F ⟶ F') : LF ⟶ LF' :=
  LF'.leftDerivedLift α' W LF (α ≫ τ)

@[reassoc (attr := simp)]
lemma leftDerivedNatTrans_fac (τ : F ⟶ F') :
    whiskerLeft L (leftDerivedNatTrans LF LF' α α' W τ) ≫ α' =
    α ≫ τ := by
  dsimp only [leftDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
lemma leftDerivedNatTrans_app (τ : F ⟶ F') (X : C) :
  (leftDerivedNatTrans LF LF' α α' W τ).app (L.obj X) ≫ α'.app X =
    α.app X ≫ τ.app X := by
  dsimp only [leftDerivedNatTrans]
  simp

@[simp]
lemma leftDerivedNatTrans_id :
    leftDerivedNatTrans LF LF α α W (𝟙 F) = 𝟙 LF :=
  leftDerived_ext LF α W _ _ _ (by aesop_cat)

@[simp]
lemma leftDerivedNatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') :
  leftDerivedNatTrans LF LF' α α' W τ ≫ leftDerivedNatTrans LF' LF'' α' α'' W τ' =
    leftDerivedNatTrans LF LF'' α α'' W (τ ≫ τ') :=
  leftDerived_ext LF'' α'' W _ _ _ (by aesop_cat)

@[simps]
noncomputable def leftDerivedNatIso (τ : F ≅ F') :
    LF ≅ LF' where
  hom := leftDerivedNatTrans LF LF' α α' W τ.hom
  inv := leftDerivedNatTrans LF' LF α' α W τ.inv

@[simp]
noncomputable def leftDerivedFunctorUnique [LF'.IsLeftDerivedFunctor α'₂ W] : LF ≅ LF' :=
  leftDerivedNatIso LF LF' α α'₂ W (Iso.refl F)

end

variable (F L)

class HasLeftDerivedFunctor : Prop where
  hasRightKanExtension' : HasRightKanExtension W.Q F

variable [L.IsLocalization W]

lemma hasLeftDerivedFunctor_iff :
    HasLeftDerivedFunctor F W ↔ HasRightKanExtension L F := by
  have : L.IsLocalization W := inferInstance
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasRightExtension_iff_postcomp₁ W.Q F (Localization.uniq W.Q L W),
    hasRightExtension_iff_of_iso₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

lemma hasLeftDerivedFunctor_iff_of_iso :
    HasLeftDerivedFunctor F W ↔ HasLeftDerivedFunctor F' W := by
  rw [hasLeftDerivedFunctor_iff F W.Q W, hasLeftDerivedFunctor_iff F' W.Q W,
    hasRightExtension_iff_of_iso₂ W.Q e]

variable (F)

lemma HasLeftDerivedFunctor.hasRightKanExtension [HasLeftDerivedFunctor F W] :
    HasRightKanExtension L F := by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

variable {F L W}

lemma HasLeftDerivedFunctor.mk' [LF.IsLeftDerivedFunctor α W] :
    HasLeftDerivedFunctor F W := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk' LF α

section

variable [F.HasLeftDerivedFunctor W] (L W)

noncomputable def totalLeftDerived : H ⥤ D :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

noncomputable def totalLeftDerivedCounit : L ⋙ F.totalLeftDerived L W ⟶ F :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

instance : (F.totalLeftDerived L W).IsLeftDerivedFunctor (F.totalLeftDerivedCounit L W) W where
  isRightKanExtension' := by
    dsimp [totalLeftDerived, totalLeftDerivedCounit]
    infer_instance

end

instance [IsIso α] : LF.IsLeftDerivedFunctor α W where
  isRightKanExtension' :=
    letI : Localization.Lifting L W F LF := ⟨asIso α⟩
    ⟨⟨IsTerminal.ofUniqueHom
      (fun G => CostructuredArrow.homMk
        (Localization.liftNatTrans L W (L ⋙ G.left) F G.left LF G.hom) (by
          ext X
          dsimp
          simp only [Localization.liftNatTrans_app, comp_obj, assoc]
          dsimp [Localization.Lifting.iso]
          simp only [NatIso.isIso_inv_app, comp_obj, IsIso.inv_hom_id, comp_id, id_comp]))
      (fun G φ => by
        ext1
        apply Localization.natTrans_ext L W
        intro X
        dsimp
        simp only [Localization.liftNatTrans_app, comp_obj]
        dsimp [Localization.Lifting.iso]
        simpa using NatTrans.congr_app φ.w X)⟩⟩

example (G : H ⥤ D) : G.IsLeftDerivedFunctor (𝟙 (L ⋙ G)) W := inferInstance

instance (G : H ⥤ D) : (L ⋙ G).HasLeftDerivedFunctor W :=
  HasLeftDerivedFunctor.mk' G (𝟙 _)

lemma hasLeftDerivedFunctor_of_inverts (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    F.HasLeftDerivedFunctor W :=
  HasLeftDerivedFunctor.mk' (Localization.lift F hF W.Q) (Localization.fac F hF W.Q).hom

lemma isIso_leftDerivedFunctor_counit_iff_inverts [LF.IsLeftDerivedFunctor α W] :
    IsIso α ↔ W.IsInvertedBy F := by
  constructor
  · intro
    exact MorphismProperty.IsInvertedBy.of_iso W (asIso α)
      (MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) LF)
  · intro hF
    rw [show α = whiskerLeft L (leftDerivedFunctorUnique LF
          (Localization.lift F hF L) α (Localization.fac F hF L).hom W).hom ≫
        (Localization.fac F hF L).hom by simp]
    infer_instance

end Functor

end CategoryTheory

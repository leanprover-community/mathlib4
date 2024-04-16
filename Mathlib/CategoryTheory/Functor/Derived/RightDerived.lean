import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C C' D D' H : Type _} [Category C] [Category C']
  [Category D] [Category D'] [Category H]
  (RF RF' RF'' : H ⥤ D) {F F' F'' : C ⥤ D} (e : F ≅ F') {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (α'' : F'' ⟶ L ⋙ RF'') (α'₂ : F ⟶ L ⋙ RF')
  (W : MorphismProperty C)

class IsRightDerivedFunctor [L.IsLocalization W] : Prop where
  isLeftKanExtension' : RF.IsLeftKanExtension α

lemma IsRightDerivedFunctor.isLeftKanExtension [L.IsLocalization W] [RF.IsRightDerivedFunctor α W] :
    RF.IsLeftKanExtension α :=
  IsRightDerivedFunctor.isLeftKanExtension' W

lemma isRightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] :
    RF.IsRightDerivedFunctor α W ↔ RF.IsLeftKanExtension α := by
  constructor
  · intros
    exact IsRightDerivedFunctor.isLeftKanExtension RF α W
  · intro h
    exact ⟨h⟩

section

variable {RF} {RF'}

lemma isRightDerivedFunctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
    [L.IsLocalization W] (e : RF ≅ RF')
    (comm : α ≫ whiskerLeft L e.hom = α') :
    RF.IsRightDerivedFunctor α W ↔
      RF'.IsRightDerivedFunctor α' W := by
    simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
    exact isLeftKanExtension_iff_of_iso e _ _ comm

end

section

variable [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
  [RF'.IsRightDerivedFunctor α' W] [RF''.IsRightDerivedFunctor α'' W]

noncomputable def rightDerivedDesc (G : H ⥤ D) (β : F ⟶ L ⋙ G) : RF ⟶ G :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β

@[reassoc (attr := simp)]
lemma rightDerived_fac (G : H ⥤ D) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac α G β

@[reassoc (attr := simp)]
lemma rightDerived_fac_app (G : H ⥤ D) (β : F ⟶ L ⋙ G) (X : C):
    α.app X ≫ (RF.rightDerivedDesc α W G β).app (L.obj X) = β.app X:=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac_app α G β X

lemma rightDerived_ext (G : H ⥤ D) (γ₁ γ₂ : RF ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.hom_ext_of_isLeftKanExtension α γ₁ γ₂ hγ

noncomputable def rightDerivedNatTrans (τ : F ⟶ F') : RF ⟶ RF' :=
  RF.rightDerivedDesc α W RF' (τ ≫ α')

@[reassoc (attr := simp)]
lemma rightDerivedNatTrans_fac (τ : F ⟶ F') :
    α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ α' := by
  dsimp only [rightDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
lemma rightDerivedNatTrans_app (τ : F ⟶ F') (X : C) :
  α.app X ≫ (rightDerivedNatTrans RF RF' α α' W τ).app (L.obj X) =
    τ.app X ≫ α'.app X := by
  dsimp only [rightDerivedNatTrans]
  simp

@[simp]
lemma rightDerivedNatTrans_id :
    rightDerivedNatTrans RF RF α α W (𝟙 F) = 𝟙 RF :=
  rightDerived_ext RF α W _ _ _ (by aesop_cat)

@[simp]
lemma rightDerivedNatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') :
  rightDerivedNatTrans RF RF' α α' W τ ≫ rightDerivedNatTrans RF' RF'' α' α'' W τ' =
    rightDerivedNatTrans RF RF'' α α'' W (τ ≫ τ') :=
  rightDerived_ext RF α W _ _ _ (by aesop_cat)

@[simps]
noncomputable def rightDerivedNatIso (τ : F ≅ F') :
    RF ≅ RF' where
  hom := rightDerivedNatTrans RF RF' α α' W τ.hom
  inv := rightDerivedNatTrans RF' RF α' α W τ.inv

@[simp]
noncomputable def rightDerivedFunctorUnique [RF'.IsRightDerivedFunctor α'₂ W] : RF ≅ RF' :=
  rightDerivedNatIso RF RF' α α'₂ W (Iso.refl F)

lemma isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (G : H ⥤ D) (β : F ⟶ L ⋙ G) :
    G.IsRightDerivedFunctor β W ↔ IsIso (RF.rightDerivedDesc α W G β) := by
  constructor
  · intro
    have : RF.rightDerivedDesc α W G β = (rightDerivedNatIso RF G α β W (Iso.refl _)).hom :=
      rightDerived_ext RF α W _ _ _ (by simp)
    rw [this]
    infer_instance
  · intro h
    rw [← isRightDerivedFunctor_iff_of_iso α β W (asIso (RF.rightDerivedDesc α W G β)) (by simp)]
    infer_instance

end

variable (F L)

class HasRightDerivedFunctor : Prop where
  hasLeftKanExtension' : HasLeftKanExtension W.Q F

variable [L.IsLocalization W]

lemma hasRightDerivedFunctor_iff :
    HasRightDerivedFunctor F W ↔ HasLeftKanExtension L F := by
  have : L.IsLocalization W := inferInstance
  have : HasRightDerivedFunctor F W ↔ HasLeftKanExtension W.Q F :=
    ⟨fun h => h.hasLeftKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasLeftExtension_iff_postcomp₁ W.Q F (Localization.uniq W.Q L W),
    hasLeftExtension_iff_of_iso₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

lemma hasRightDerivedFunctor_iff_of_iso :
    HasRightDerivedFunctor F W ↔ HasRightDerivedFunctor F' W := by
  rw [hasRightDerivedFunctor_iff F W.Q W, hasRightDerivedFunctor_iff F' W.Q W,
    hasLeftExtension_iff_of_iso₂ W.Q e]

variable (F)

lemma HasRightDerivedFunctor.hasLeftKanExtension [HasRightDerivedFunctor F W] :
    HasLeftKanExtension L F := by
  simpa only [← hasRightDerivedFunctor_iff F L W]

variable {F L W}

lemma HasRightDerivedFunctor.mk' [RF.IsRightDerivedFunctor α W] :
    HasRightDerivedFunctor F W := by
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  simpa only [hasRightDerivedFunctor_iff F L W] using HasLeftKanExtension.mk RF α

section

variable [F.HasRightDerivedFunctor W] (L W)

noncomputable def totalRightDerived : H ⥤ D :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtension L F

noncomputable def totalRightDerivedUnit : F ⟶ L ⋙ F.totalRightDerived L W :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtensionUnit L F

instance : (F.totalRightDerived L W).IsRightDerivedFunctor (F.totalRightDerivedUnit L W) W where
  isLeftKanExtension' := by
    dsimp [totalRightDerived, totalRightDerivedUnit]
    infer_instance

end

instance [IsIso α] : RF.IsRightDerivedFunctor α W where
  isLeftKanExtension' :=
    letI : Localization.Lifting L W F RF := ⟨(asIso α).symm⟩
    ⟨⟨IsInitial.ofUniqueHom
      (fun G => StructuredArrow.homMk
        (Localization.liftNatTrans L W F (L ⋙ G.right) RF G.right G.hom) (by
          ext X
          dsimp
          simp only [Localization.liftNatTrans_app, comp_obj]
          dsimp [Localization.Lifting.iso, Localization.Lifting.iso']
          simp only [NatIso.isIso_inv_app, comp_obj, comp_id, IsIso.hom_inv_id_assoc]))
      (fun G φ => by
        ext1
        apply Localization.natTrans_ext L W
        intro X
        dsimp
        simp only [Localization.liftNatTrans_app, comp_obj]
        dsimp [Localization.Lifting.iso, Localization.Lifting.iso']
        simpa using NatTrans.congr_app φ.w.symm X)⟩⟩

example (G : H ⥤ D) : G.IsRightDerivedFunctor (𝟙 (L ⋙ G)) W := inferInstance

instance (G : H ⥤ D) : (L ⋙ G).HasRightDerivedFunctor W :=
  HasRightDerivedFunctor.mk' G (𝟙 _)

lemma hasRightDerivedFunctor_of_inverts (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    F.HasRightDerivedFunctor W :=
  HasRightDerivedFunctor.mk' (Localization.lift F hF W.Q) (Localization.fac F hF W.Q).inv

variable (W)

lemma isIso_rightDerivedFunctor_unit_iff_inverts [RF.IsRightDerivedFunctor α W] :
    IsIso α ↔ W.IsInvertedBy F := by
  constructor
  · intro
    exact MorphismProperty.IsInvertedBy.of_iso W (asIso α).symm
      (MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) RF)
  · intro hF
    rw [show α = (Localization.fac F hF L).inv ≫  whiskerLeft L (rightDerivedFunctorUnique RF
          (Localization.lift F hF L) α (Localization.fac F hF L).inv W).inv by simp]
    infer_instance

lemma isRightDerivedFunctor_iff_postcomp (G : D ⥤ D') [IsEquivalence G] :
    RF.IsRightDerivedFunctor α W ↔
      (RF ⋙ G).IsRightDerivedFunctor (whiskerRight α G ≫ (Functor.associator _ _ _).hom) W := by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  apply isLeftKanExtension_iff_postcomp₂

instance isRightDerivedFunctor_postcomp (G : D ⥤ D') [IsEquivalence G]
    [RF.IsRightDerivedFunctor α W] :
      (RF ⋙ G).IsRightDerivedFunctor (whiskerRight α G ≫ (Functor.associator _ _ _).hom) W := by
  rw [← isRightDerivedFunctor_iff_postcomp]
  infer_instance

lemma isRightDerivedFunctor_of_iso₂ {F F' : C ⥤ D} {RF RF' : H ⥤ D}
    (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (e₁ : F ≅ F') (e₂ : RF ≅ RF')
    (h : α ≫ whiskerLeft L e₂.hom = e₁.hom ≫ α') :
    RF.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W := by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact Functor.isLeftKanExtension_iff_of_iso₂ _ _ e₁ e₂ h

variable {RF}
lemma isRightDerivedFunctor_iff_of_isLocalization
    {H' : Type*} [Category H'] {L' : C ⥤ H'} [L'.IsLocalization W]
    (α : F ⟶ L ⋙ RF)
    {RF' : H' ⥤ D} (α' : F ⟶ L' ⋙ RF') (G : H' ⥤ H) (e : L' ⋙ G ≅ L)
    (e' : G ⋙ RF ≅ RF')
    (hα' : α' = α ≫ whiskerRight e.inv _ ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft _ e'.hom) :
    RF.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W := by
  have := Functor.IsEquivalence.of_localization_comparison L' L W G e
  rw [isRightDerivedFunctor_iff_isLeftKanExtension _ α W,
    isLeftKanExtension_iff_precomp₁ G e α,
    ← isRightDerivedFunctor_iff_isLeftKanExtension _ _ W]
  exact isRightDerivedFunctor_of_iso₂ W _ _ (Iso.refl _) e' (by simp [hα'])

lemma isRightDerivedFunctor_of_isLocalization
    {H' : Type*} [Category H'] {L' : C ⥤ H'} [L'.IsLocalization W]
    (α : F ⟶ L ⋙ RF)
    {RF' : H' ⥤ D} (α' : F ⟶ L' ⋙ RF') (G : H' ⥤ H) (e : L' ⋙ G ≅ L)
    (e' : G ⋙ RF ≅ RF')
    (hα' : α' = α ≫ whiskerRight e.inv _ ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft _ e'.hom)
    [RF.IsRightDerivedFunctor α W] :
    RF'.IsRightDerivedFunctor α' W := by
  rw [← isRightDerivedFunctor_iff_of_isLocalization W α α' G e e' hα']
  infer_instance

end Functor

namespace LocalizerMorphism

variable {C₁ C₂ H₁ H₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Category H₁] [Category H₂] {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLocalizedEquivalence] [Φ.functor.IsEquivalence]
  (L₁ : C₁ ⥤ H₁) (L₂ : C₂ ⥤ H₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (G : H₁ ⥤ H₂) (iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
  {F₂ : C₂ ⥤ D} {RF₂ : H₂ ⥤ D} (α₂ : F₂ ⟶ L₂ ⋙ RF₂)
  {F₁ : C₁ ⥤ D} {RF₁ : H₁ ⥤ D} (α₁ : F₁ ⟶ L₁ ⋙ RF₁)
  (e₁ : Φ.functor ⋙ F₂ ≅ F₁)
  (e₂ : G ⋙ RF₂ ≅ RF₁)
  (h : α₁ = e₁.inv ≫ whiskerLeft Φ.functor α₂ ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight iso.hom RF₂ ≫ (Functor.associator L₁ G RF₂).hom ≫ whiskerLeft L₁ e₂.hom)

lemma isRightDerivedFunctor_iff_precomp :
    RF₁.IsRightDerivedFunctor α₁ W₁ ↔ RF₂.IsRightDerivedFunctor α₂ W₂ := by
  have : CatCommSq Φ.functor L₁ L₂ G := ⟨iso⟩
  have := Φ.isEquivalence L₁ L₂ G
  rw [← Functor.isRightDerivedFunctor_iff_of_isLocalization W₁
    (α₁ ≫ whiskerLeft L₁ e₂.inv ≫ (Functor.associator _ _ _).inv) α₁
    _ (Iso.refl _) e₂ (by aesop_cat),
    Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ W₁,
    Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ W₂,
    Functor.isLeftKanExtension_iff_precomp RF₂ α₂ Φ.functor]
  apply Functor.isLeftKanExtension_iff_of_iso₃ _ _ e₁.symm (Iso.refl _) iso.symm
  ext
  simp [h]

end LocalizerMorphism

end CategoryTheory

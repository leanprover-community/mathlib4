/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Existence
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
public import Mathlib.CategoryTheory.Localization.Prod

/-!
#

-/

@[expose] public section

universe v₁ v₂ v₁' v₂' v₃ v₄ v u₁ u₂ u₁' u₂' u₃ u₄ u

-- Part of this should be moved to `CategoryTheory.Functor.Derived`,
-- and the rest should be an adaptation of
-- `CategoryTheory.Localization.DerivabilityStructure.Derives`

namespace CategoryTheory

open Category Functor

variable
    (C₁ : Type u₁) (C₂ : Type u₂) (H : Type u)
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v} H]
    {D₁ : Type u₁'} {D₂ : Type u₂'}
    [Category.{v₁'} D₁] [Category.{v₂'} D₂]
    {C₁' : Type u₃} {C₂' : Type u₄}
    [Category.{v₃} C₁'] [Category.{v₄} C₂']

abbrev Bifunctor := C₁ ⥤ C₂ ⥤ H

namespace Bifunctor

variable {C₁ C₂ H}
variable (RF : Bifunctor D₁ D₂ H) (F : Bifunctor C₁ C₂ H)

nonrec abbrev uncurry : C₁ × C₂ ⥤ H := uncurry.obj F

variable {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₁' : MorphismProperty C₁'} {W₂' : MorphismProperty C₂'}
  (Φ₁ : LocalizerMorphism W₁' W₁) (Φ₂ : LocalizerMorphism W₂' W₂)

class PrecompLocalizerMorphismsInverts : Prop where
  isInvertedBy : (W₁'.prod W₂').IsInvertedBy ((Φ₁.functor.prod Φ₂.functor) ⋙ F.uncurry)

lemma precompLocalizerMorphismsInverts_iff [W₁'.ContainsIdentities] [W₂'.ContainsIdentities] :
    PrecompLocalizerMorphismsInverts F Φ₁ Φ₂ ↔
        (∀ ⦃X₁ Y₁ : C₁'⦄ (f₁ : X₁ ⟶ Y₁) (X₂ : C₂') (_ : W₁' f₁),
            IsIso ((F.map (Φ₁.functor.map f₁)).app (Φ₂.functor.obj X₂))) ∧
        (∀ (X₁ : C₁') ⦃X₂ Y₂ : C₂'⦄ (f₂ : X₂ ⟶ Y₂) (_ : W₂' f₂),
            IsIso ((F.obj (Φ₁.functor.obj X₁)).map (Φ₂.functor.map f₂))) := by
  constructor
  · intro hF
    constructor
    · intro X₁ Y₁ f₁ X₂ hf₁
      let φ : (⟨X₁, X₂⟩ : C₁' × C₂') ⟶ ⟨Y₁, X₂⟩ := ⟨f₁, 𝟙 _⟩
      simpa using hF.isInvertedBy φ ⟨hf₁, W₂'.id_mem _⟩
    · intro X₁ X₂ Y₂ f₂ hf₂
      let φ : (⟨X₁, X₂⟩ : C₁' × C₂') ⟶ ⟨X₁, Y₂⟩ := ⟨𝟙 _, f₂⟩
      simpa using hF.isInvertedBy φ ⟨W₁'.id_mem _, hf₂⟩
  · rintro ⟨hF₁, hF₂⟩
    refine ⟨fun ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩ => ?_⟩
    dsimp
    have := hF₁ f₁ X₂ hf₁
    have := hF₂ Y₁ f₂ hf₂
    infer_instance

variable (W₁ W₂)

abbrev HasRightDerivedBifunctor := F.uncurry.HasRightDerivedFunctor (W₁.prod W₂)

@[simps!]
def whiskeringLeft₂ (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) : (D₁ ⥤ D₂ ⥤ H) ⥤ (C₁ ⥤ C₂ ⥤ H) :=
  (whiskeringLeft C₁ D₁ (D₂ ⥤ H)).obj L₁ ⋙
    (whiskeringRight C₁ (D₂ ⥤ H) (C₂ ⥤ H)).obj ((whiskeringLeft C₂ D₂ H).obj L₂)


section

variable {F RF}

@[simps!]
def toWhiskeringLeft₂Eval₂ {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    (α : F ⟶ (whiskeringLeft₂ L₁ L₂).obj RF) (X₂ : C₂) :
    F ⋙ (evaluation C₂ H).obj X₂ ⟶ (whiskeringLeft₂ L₁ L₂).obj RF ⋙ (evaluation C₂ H).obj X₂ :=
  (((whiskeringRight C₁ (C₂ ⥤ H) H).obj ((evaluation C₂ H).obj X₂)).map α)

end

set_option backward.isDefEq.respectTransparency false in
@[simps]
def whiskeringLeft₂Equiv (F : Bifunctor C₁ C₂ H) (G : (D₁ × D₂) ⥤ H)
    (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) :
    (F ⟶ (whiskeringLeft₂ L₁ L₂).obj (curry.obj G)) ≃ (F.uncurry ⟶ (L₁.prod L₂) ⋙ G) where
  toFun α :=
    { app := fun ⟨X₁, X₂⟩ => (α.app X₁).app X₂
      naturality := fun ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ _ => by
        dsimp
        rw [assoc, NatTrans.naturality, ← NatTrans.comp_app_assoc, NatTrans.naturality]
        dsimp
        rw [assoc, ← Functor.map_comp]
        congr 1
        aesop_cat }
  invFun β :=
    { app := fun X₁ =>
        { app := fun X₂ => β.app ⟨X₁, X₂⟩
          naturality := fun X₂ Y₂ f₂ => by
            simpa using β.naturality (show ⟨X₁, X₂⟩ ⟶ ⟨X₁, Y₂⟩ from ⟨𝟙 _, f₂⟩) }
      naturality := fun X₁ Y₁ f₁ => by
        ext X₂
        simpa using β.naturality (show ⟨X₁, X₂⟩ ⟶ ⟨Y₁, X₂⟩ from ⟨f₁, 𝟙 _⟩) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- whiskeringLeft₂Equiv' -/
@[simps!]
def whiskeringLeft₂Equiv' (F : Bifunctor C₁ C₂ H) (G : Bifunctor D₁ D₂ H)
    (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) :
    (F ⟶ (whiskeringLeft₂ L₁ L₂).obj G) ≃ (F.uncurry ⟶ (L₁.prod L₂) ⋙ G.uncurry) :=
  Equiv.trans
    { toFun := fun α => α ≫ (whiskeringLeft₂ L₁ L₂).map (Functor.curryObjUncurryObjIso G).inv
      invFun := fun β => β ≫ (whiskeringLeft₂ L₁ L₂).map (Functor.curryObjUncurryObjIso G).hom
      left_inv := fun α => by
        dsimp only
        rw [assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id]
      right_inv := fun β => by
        dsimp only
        rw [assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, comp_id] }
    (whiskeringLeft₂Equiv F G.uncurry L₁ L₂)

variable {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]

variable {F}

abbrev IsRightDerivedBifunctor [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    (α : F ⟶ (whiskeringLeft₂ L₁ L₂).obj RF) :=
  RF.uncurry.IsRightDerivedFunctor (whiskeringLeft₂Equiv' _ _ _ _ α) (W₁.prod W₂)

section

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities] (α : F ⟶ (whiskeringLeft₂ L₁ L₂).obj RF)
    [Bifunctor.IsRightDerivedBifunctor RF W₁ W₂ α]

section

variable [Φ₁.IsRightDerivabilityStructure] [Φ₂.IsRightDerivabilityStructure]
variable {W₁ W₂}

lemma isIso_app_app_of_isRightDerivedBifunctor
    [W₁'.ContainsIdentities] [W₂'.ContainsIdentities]
    [hF : PrecompLocalizerMorphismsInverts F Φ₁ Φ₂] (X₁' : C₁') (X₂' : C₂') :
    IsIso ((α.app (Φ₁.functor.obj X₁')).app (Φ₂.functor.obj X₂')) := by
  convert (Φ₁.prod Φ₂).isIso_app_of_isRightDerivedFunctor F.uncurry hF.isInvertedBy
    (L₁.prod L₂) RF.uncurry (whiskeringLeft₂Equiv' _ _ _ _ α) ⟨X₁', X₂'⟩
  simp [LocalizerMorphism.prod]

end

section

variable (X₁ : C₁) (F₂ : D₂ ⥤ H) (α₁ : F.obj X₁ ⟶ L₂ ⋙ F₂) [F₂.IsRightDerivedFunctor α₁ W₂]

noncomputable def rightDerivedNatTrans₁ : F₂ ⟶ RF.obj (L₁.obj X₁) :=
  Functor.rightDerivedDesc F₂ α₁ W₂ _ (α.app X₁)

omit [W₂.ContainsIdentities] in
lemma rightDerivedNatTrans₁_fac_app (X₂ : C₂) :
    α₁.app X₂ ≫ (rightDerivedNatTrans₁ RF W₂ α X₁ F₂ α₁).app (L₂.obj X₂) =
      (α.app X₁).app X₂ := by
  apply Functor.rightDerived_fac_app

end

section

variable (X₂ : C₂) (F₁ : D₁ ⥤ H) (α₂ : F.flip.obj X₂ ⟶ L₁ ⋙ F₁) [F₁.IsRightDerivedFunctor α₂ W₁]

noncomputable def rightDerivedNatTrans₂ : F₁ ⟶ RF.flip.obj (L₂.obj X₂) :=
  Functor.rightDerivedDesc F₁ α₂ W₁ _
    (toWhiskeringLeft₂Eval₂ α X₂)

omit [W₁.ContainsIdentities] in
lemma rightDerivedNatTrans₂_fac_app (X₁ : C₁) :
  α₂.app X₁ ≫ (rightDerivedNatTrans₂ RF W₁ α X₂ F₁ α₂).app (L₁.obj X₁) =
    (α.app X₁).app X₂ := by
  apply Functor.rightDerived_fac_app

end

end

section

variable (F L₁ L₂)
variable [HasRightDerivedBifunctor F W₁ W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities]

noncomputable def rightDerivedBifunctor : D₁ ⥤ D₂ ⥤ H :=
    curry.obj (F.uncurry.totalRightDerived (L₁.prod L₂) (W₁.prod W₂))

noncomputable def rightDerivedUnit :
    F ⟶ (whiskeringLeft₂ L₁ L₂).obj (Bifunctor.rightDerivedBifunctor F W₁ W₂ L₁ L₂) :=
  (whiskeringLeft₂Equiv _ _ _ _).symm
    (F.uncurry.totalRightDerivedUnit (L₁.prod L₂) (W₁.prod W₂))

end

variable {W₁ W₂} (F)
section

variable
  [hF : PrecompLocalizerMorphismsInverts F Φ₁ Φ₂]

include hF in
lemma hasRightDerivedBifunctor_of_precompLocalizerMorphismsInverts
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    [W₁'.ContainsIdentities] [W₂'.ContainsIdentities]
    [Φ₁.IsRightDerivabilityStructure] [Φ₂.IsRightDerivabilityStructure] :
    HasRightDerivedBifunctor F W₁ W₂ :=
  (Φ₁.prod Φ₂).hasRightDerivedFunctor F.uncurry hF.isInvertedBy

lemma isInverted₁_of_precompLocalizerMorphismsInverts (X₁ : C₁') [W₁'.ContainsIdentities] :
    W₂'.IsInvertedBy (Φ₂.functor ⋙ F.obj (Φ₁.functor.obj X₁)) := by
  intro X₂ Y₂ f₂ hf₂
  let φ : (⟨X₁, X₂⟩ : C₁' × C₂') ⟶ ⟨X₁, Y₂⟩ := ⟨𝟙 _, f₂⟩
  simpa using hF.isInvertedBy φ ⟨W₁'.id_mem _, hf₂⟩

lemma hasRightDerivedFunctor₁_of_precompLocalizerMorphismsInverts
    [W₁'.ContainsIdentities]
    [Φ₂.IsRightDerivabilityStructure] (X₁ : C₁') :
    (F.obj (Φ₁.functor.obj X₁)).HasRightDerivedFunctor W₂ :=
  Φ₂.hasRightDerivedFunctor _ (isInverted₁_of_precompLocalizerMorphismsInverts F Φ₁ Φ₂ X₁)

lemma isInverted₂_of_precompLocalizerMorphismsInverts [W₂'.ContainsIdentities] (X₂ : C₂') :
    W₁'.IsInvertedBy (Φ₁.functor ⋙ F.flip.obj (Φ₂.functor.obj X₂)) := by
  intro X₁ Y₁ f₁ hf₁
  let φ : (⟨X₁, X₂⟩ : C₁' × C₂') ⟶ ⟨Y₁, X₂⟩ := ⟨f₁, 𝟙 _⟩
  simpa using hF.isInvertedBy φ ⟨hf₁, W₂'.id_mem _⟩

lemma hasRightDerivedFunctor₂_of_precompLocalizerMorphismsInverts
    [W₂'.ContainsIdentities] [Φ₁.IsRightDerivabilityStructure] (X₂ : C₂') :
    (F.flip.obj (Φ₂.functor.obj X₂)).HasRightDerivedFunctor W₁ :=
  Φ₁.hasRightDerivedFunctor _ (isInverted₂_of_precompLocalizerMorphismsInverts F Φ₁ Φ₂ X₂)

variable (α : F ⟶ (whiskeringLeft₂ L₁ L₂).obj RF) [W₁.ContainsIdentities]
  [W₂.ContainsIdentities] [IsRightDerivedBifunctor RF W₁ W₂ α]

section

variable (X₁ : C₁') (F₂ : D₂ ⥤ H)
  (α₁ : F.obj (Φ₁.functor.obj X₁) ⟶ L₂ ⋙ F₂) [F₂.IsRightDerivedFunctor α₁ W₂]

set_option backward.isDefEq.respectTransparency false in
lemma isIso_rightDerivedNatTrans₁ [Φ₂.IsRightDerivabilityStructure]
    [Φ₁.IsRightDerivabilityStructure] [W₁'.ContainsIdentities] [W₂'.ContainsIdentities] :
    IsIso (rightDerivedNatTrans₁ RF W₂ α (Φ₁.functor.obj X₁) F₂ α₁) := by
  rw [Φ₂.isIso_iff_of_hasRightResolutions L₂]
  intro X₂
  have := Φ₂.isIso_app_of_isRightDerivedFunctor _
    (isInverted₁_of_precompLocalizerMorphismsInverts F Φ₁ Φ₂ X₁) L₂ F₂ α₁ X₂
  have := isIso_app_app_of_isRightDerivedBifunctor RF Φ₁ Φ₂ α X₁ X₂
  exact IsIso.of_isIso_fac_left (rightDerivedNatTrans₁_fac_app RF W₂ α (Φ₁.functor.obj X₁)
    F₂ α₁ (Φ₂.functor.obj X₂))

include Φ₂ in
lemma isRightDerivedFunctor₁_of_isRightDerivedBifunctor [W₁'.ContainsIdentities]
    [W₂'.ContainsIdentities]
    [Φ₁.IsRightDerivabilityStructure]
    [Φ₂.IsRightDerivabilityStructure] :
    (RF.obj (L₁.obj (Φ₁.functor.obj X₁))).IsRightDerivedFunctor
      (α.app (Φ₁.functor.obj X₁)) W₂ := by
  have := hasRightDerivedFunctor₁_of_precompLocalizerMorphismsInverts F Φ₁ Φ₂ X₁
  let RF₂ := (F.obj (Φ₁.functor.obj X₁)).totalRightDerived L₂ W₂
  let α₁ := (F.obj (Φ₁.functor.obj X₁)).totalRightDerivedUnit L₂ W₂
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc RF₂ α₁ W₂
    (RF.obj (L₁.obj (Φ₁.functor.obj X₁)))
    (α.app (Φ₁.functor.obj X₁))]
  exact isIso_rightDerivedNatTrans₁ RF F Φ₁ Φ₂ α X₁ RF₂ α₁

end

section

variable (X₂ : C₂') (F₁ : D₁ ⥤ H) (α₂ : F.flip.obj (Φ₂.functor.obj X₂) ⟶ L₁ ⋙ F₁)
    [F₁.IsRightDerivedFunctor α₂ W₁]

include Φ₁ in
set_option backward.isDefEq.respectTransparency false in
lemma isIso_rightDerivedNatTrans₂ [Φ₁.IsRightDerivabilityStructure]
    [Φ₂.IsRightDerivabilityStructure] [W₁'.ContainsIdentities] [W₂'.ContainsIdentities] :
    IsIso (rightDerivedNatTrans₂ RF W₁ α (Φ₂.functor.obj X₂) F₁ α₂) := by
  rw [Φ₁.isIso_iff_of_hasRightResolutions L₁]
  intro X₁
  have := Φ₁.isIso_app_of_isRightDerivedFunctor _
    (isInverted₂_of_precompLocalizerMorphismsInverts F Φ₁ Φ₂ X₂) L₁ F₁ α₂ X₁
  have := isIso_app_app_of_isRightDerivedBifunctor RF Φ₁ Φ₂ α X₁ X₂
  exact IsIso.of_isIso_fac_left (rightDerivedNatTrans₂_fac_app RF W₁ α (Φ₂.functor.obj X₂)
    F₁ α₂ (Φ₁.functor.obj X₁))

set_option backward.isDefEq.respectTransparency false in
lemma isRightDerivedFunctor₂_of_isRightDerivedBifunctor [Φ₁.IsRightDerivabilityStructure]
    [Φ₂.IsRightDerivabilityStructure] [W₁'.ContainsIdentities] [W₂'.ContainsIdentities] :
    (RF.flip.obj (L₂.obj (Φ₂.functor.obj X₂))).IsRightDerivedFunctor
      (toWhiskeringLeft₂Eval₂ α (Φ₂.functor.obj X₂)) W₁ := by
  have := hasRightDerivedFunctor₂_of_precompLocalizerMorphismsInverts F Φ₁ Φ₂ X₂
  let RF₁ := (F.flip.obj (Φ₂.functor.obj X₂)).totalRightDerived L₁ W₁
  let α₂ := (F.flip.obj (Φ₂.functor.obj X₂)).totalRightDerivedUnit L₁ W₁
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc RF₁ α₂ W₁
    (RF.flip.obj (L₂.obj (Φ₂.functor.obj X₂)))
    (toWhiskeringLeft₂Eval₂ α (Φ₂.functor.obj X₂))]
  exact isIso_rightDerivedNatTrans₂ RF F Φ₁ Φ₂ α X₂ RF₁ α₂

end

end

end Bifunctor

end CategoryTheory

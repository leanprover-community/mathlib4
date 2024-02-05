import Mathlib.CategoryTheory.Localization.LocalizerMorphism

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

structure RightResolution (X₂ : C₂) where
  {X₁ : C₁}
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

section

variable {Φ X₂}

lemma RightResolution.mk_surjective (R : Φ.RightResolution X₂) :
    ∃ (X₁ : C₁) (w : X₂ ⟶ Φ.functor.obj X₁) (hw : W₂ w), R = RightResolution.mk w hw :=
  ⟨_, R.w, R.hw, rfl⟩

end

abbrev HasRightResolutions := ∀ (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}

@[ext]
structure Hom (R R' : Φ.RightResolution X₂) where
  f : R.X₁ ⟶ R'.X₁
  hf : W₁ f
  comm : R.w ≫ Φ.functor.map f = R'.w := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
def Hom.id [W₁.ContainsIdentities] (R : Φ.RightResolution X₂) : Hom R R where
  f := 𝟙 _
  hf := W₁.id_mem _

@[simps]
def Hom.comp [W₁.IsMultiplicative] {R R' R'' : Φ.RightResolution X₂}
    (φ : Hom R R') (ψ : Hom R' R'') : Hom R R'' where
  f := φ.f ≫ ψ.f
  hf := W₁.comp_mem _ _ φ.hf ψ.hf

instance [W₁.IsMultiplicative] : Category (Φ.RightResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end RightResolution

section

variable [Φ.HasRightResolutions]
    {D₂ : Type*} [Category D₂] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

lemma essSurj_of_hasRightResolutions : EssSurj (Φ.functor ⋙ L₂) where
  mem_essImage X₂ := by
    have : EssSurj L₂ := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩

lemma isIso_iff_of_hasRightResolutions
    {H : Type*} [Category H] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ ∀ (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    suffices ∀ (X₂ : D₂), IsIso (α.app X₂) from NatIso.isIso_of_isIso_app α
    have := Φ.essSurj_of_hasRightResolutions L₂
    intro X₂
    rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
    exact hα ((Φ.functor ⋙ L₂).objPreimage X₂)
end

end LocalizerMorphism

/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Resolutions for a morphism of localizers

Given a morphism of localizers `Φ : LocalizerMorphism W₁ W₂` (i.e. `W₁` and `W₂` are
morphism properties on categories `C₁` and `C₂`, and we have a functor
`Φ.functor : C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂`), we introduce
the notion of right resolutions of objects in `C₂`: if `X₂ : C₂`.
A right resolution consists of an object `X₁ : C₁` and a morphism
`w : X₂ ⟶ Φ.functor.obj X₁` that is in `W₂`. Then, the typeclass
`Φ.HasRightResolutions` holds when any `X₂ : C₂` has a right resolution.

The type of right resolutions `Φ.RightResolution X₂` is endowed with a category
structure when the morphism property `W₁` is multiplicative.

## Future works

* formalize right derivability structures as localizer morphisms admitting right resolutions
and forming a Guitart exact square, as it is defined in
[the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008] (TODO @joelriou)
* show that if `C` is an abelian category with enough injectives, there is a derivability
structure associated to the inclusion of the full subcategory of complexes of injective
objects into the bounded below homotopy category of `C` (TODO @joelriou)
* formalize dual results

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₂' u₁ u₂ u₂'

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D₂ H : Type*} [Category C₁] [Category C₂] [Category D₂] [Category H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/-- The category of resolutions of an object in the target category of a localizer morphism. -/
structure RightResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism to an object of the form `Φ.functor.obj X₁` -/
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

variable {Φ X₂} in
lemma RightResolution.mk_surjective (R : Φ.RightResolution X₂) :
    ∃ (X₁ : C₁) (w : X₂ ⟶ Φ.functor.obj X₁) (hw : W₂ w), R = RightResolution.mk w hw :=
  ⟨_, R.w, R.hw, rfl⟩

/-- A localizer morphism has right resolutions when any object has a right resolution. -/
abbrev HasRightResolutions := ∀ (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.RightResolution X₂` (when `W₁` is multiplicative). -/
@[ext]
structure Hom (R R' : Φ.RightResolution X₂) where
  /-- a morphism in the source category -/
  f : R.X₁ ⟶ R'.X₁
  hf : W₁ f
  comm : R.w ≫ Φ.functor.map f = R'.w := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of a object in `Φ.RightResolution X₂`. -/
@[simps]
def Hom.id [W₁.ContainsIdentities] (R : Φ.RightResolution X₂) : Hom R R where
  f := 𝟙 _
  hf := W₁.id_mem _

variable [W₁.IsMultiplicative]

/-- The composition of morphisms in `Φ.RightResolution X₂`. -/
@[simps]
def Hom.comp {R R' R'' : Φ.RightResolution X₂}
    (φ : Hom R R') (ψ : Hom R' R'') :
    Hom R R'' where
  f := φ.f ≫ ψ.f
  hf := W₁.comp_mem _ _ φ.hf ψ.hf

instance : Category (Φ.RightResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
lemma id_f (R : Φ.RightResolution X₂) : Hom.f (𝟙 R) = 𝟙 R.X₁ := rfl

@[simp, reassoc]
lemma comp_f {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
lemma hom_ext {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext _ _ h

end RightResolution

section

variable [Φ.HasRightResolutions] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

lemma essSurj_of_hasRightResolutions : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩

lemma isIso_iff_of_hasRightResolutions {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ ∀ (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : ∀ (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasRightResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α

end

end LocalizerMorphism

end CategoryTheory

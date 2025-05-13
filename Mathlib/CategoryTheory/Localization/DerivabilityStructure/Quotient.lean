/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# "Quotient" derivability structures

The assumptions of `IsLeftDerivabilityStructure.mk'` are stable by
quotients.

See `DerivabilityStructure.OfLocalizedEquivalences` for a more conceptual statement.

-/

namespace CategoryTheory

namespace LocalizerMorphism

variable {C₀ C H₀ H : Type*} [Category C₀] [Category C] [Category H₀] [Category H]
  {W₀ : MorphismProperty C₀} {W : MorphismProperty C}
  {W₀ₕ : MorphismProperty H₀} {Wₕ : MorphismProperty H}
  {T : LocalizerMorphism W₀ W} {L : LocalizerMorphism W₀ W₀ₕ}
  {R : LocalizerMorphism W Wₕ} {B : LocalizerMorphism W₀ₕ Wₕ}
  (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)

namespace IsLeftDerivabilityStructure.quotient

include iso

lemma isLocalizerEquivalence [T.IsLocalizedEquivalence] [L.IsLocalizedEquivalence]
    [R.IsLocalizedEquivalence] : B.IsLocalizedEquivalence := by
  have : (L.comp B).IsLocalizedEquivalence :=
    LocalizerMorphism.isLocalizedEquivalence_of_iso (Φ := T.comp R) (Φ' := L.comp B) iso
  exact LocalizerMorphism.isLocalizedEquibalence_of_precomp L B

@[simps]
def leftResolutionComparison [Wₕ.IsMultiplicative] [Wₕ.RespectsIso] (X : C) :
    T.LeftResolution X ⥤ B.LeftResolution (R.functor.obj X) where
  obj A :=
    { X₁ := L.functor.obj A.X₁
      w := iso.inv.app _ ≫ R.functor.map A.w
      hw := Wₕ.comp_mem _ _ (Wₕ.of_isIso _) (R.map _ A.hw) }
  map φ :=
    { f := L.functor.map φ.f
      comm := by
        have := iso.inv.naturality φ.f
        dsimp at this ⊢
        rw [reassoc_of% this, ← Functor.map_comp, φ.comm] }

instance [Wₕ.IsMultiplicative] [Wₕ.RespectsIso] [L.functor.EssSurj] [R.functor.Full]
    [R.IsInduced] (X : C) :
    (leftResolutionComparison iso X).EssSurj where
  mem_essImage A := by
    obtain ⟨f, hf⟩ := R.functor.map_surjective
      (iso.hom.app _ ≫ B.functor.map (L.functor.objObjPreimageIso A.X₁).hom ≫ A.w)
    let A' : T.LeftResolution X :=
      { X₁ := L.functor.objPreimage A.X₁
        w := f
        hw := by
          simp only [← R.inverseImage_eq, MorphismProperty.inverseImage_iff, hf,
            ← Category.assoc]
          exact Wₕ.comp_mem _ _ (Wₕ.of_isIso _) A.hw }
    exact ⟨A', ⟨LocalizerMorphism.LeftResolution.isoMk (L.functor.objObjPreimageIso _)⟩⟩

lemma isConnected_leftResolution
    [Wₕ.IsMultiplicative] [Wₕ.RespectsIso] [L.functor.EssSurj] [R.functor.Full] [R.IsInduced]
    [∀ (X : C), IsConnected (T.LeftResolution X)] [R.functor.EssSurj] (Y : H)
    : IsConnected (B.LeftResolution Y) := by
  obtain ⟨X, ⟨e⟩⟩ : ∃ (X : C), Nonempty (R.functor.obj X ≅ Y) :=
    ⟨_, ⟨R.functor.objObjPreimageIso Y⟩⟩
  have := (leftResolutionComparison iso X).isConnected_of_isConnected_of_essSurj
  exact isConnected_of_equivalent (LocalizerMorphism.LeftResolution.chgObjEquivalence B e)

lemma hasLeftResolutions_arrow [R.functor.EssSurj] [R.functor.Full]
    [T.arrow.HasLeftResolutions] [Wₕ.IsMultiplicative] [Wₕ.RespectsIso] :
    B.arrow.HasLeftResolutions := by
  rintro ⟨Y₁, Y₂, f⟩
  obtain ⟨X₁, ⟨e₁⟩⟩ : ∃ (X₁ : C), Nonempty (R.functor.obj X₁ ≅ Y₁) :=
    ⟨_, ⟨R.functor.objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : ∃ (X₂ : C), Nonempty (R.functor.obj X₂ ≅ Y₂) :=
    ⟨_, ⟨R.functor.objObjPreimageIso Y₂⟩⟩
  obtain ⟨φ, hφ⟩ := R.functor.map_surjective (e₁.hom ≫ f ≫ e₂.inv)
  simp only [← cancel_mono e₂.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hφ
  have A : T.arrow.LeftResolution (Arrow.mk φ) := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.mapArrow.obj A.X₁
    w := Arrow.homMk (iso.inv.app _ ≫ R.functor.map A.w.left ≫ e₁.hom)
        (iso.inv.app _ ≫ R.functor.map A.w.right ≫ e₂.hom) (by
          have h₁ := A.w.w
          have h₂ := iso.inv.naturality A.X₁.hom
          dsimp at h₁ h₂ ⊢
          rw [Category.assoc, Category.assoc, ← hφ, ← Functor.map_comp_assoc, h₁,
            Functor.map_comp_assoc, reassoc_of% h₂])
    hw := ⟨Wₕ.comp_mem _ _ (Wₕ.of_isIso _) (Wₕ.comp_mem _ _ (R.map _ A.hw.1) (Wₕ.of_isIso _)),
        Wₕ.comp_mem _ _ (Wₕ.of_isIso _) (Wₕ.comp_mem _ _ (R.map _ A.hw.2) (Wₕ.of_isIso _))⟩
  }⟩

end IsLeftDerivabilityStructure.quotient

include iso in
lemma IsLeftDerivabilityStructure.quotient
    [T.IsLocalizedEquivalence] [L.IsLocalizedEquivalence] [R.IsLocalizedEquivalence]
    [∀ (X : C), IsConnected (T.LeftResolution X)] [T.arrow.HasLeftResolutions]
    [W₀ₕ.IsMultiplicative] [Wₕ.IsMultiplicative] [Wₕ.RespectsIso]
    [R.IsInduced] [L.functor.EssSurj] [R.functor.EssSurj] [R.functor.Full] :
    B.IsLeftDerivabilityStructure := by
  have := quotient.isConnected_leftResolution iso
  have : B.arrow.HasLeftResolutions := quotient.hasLeftResolutions_arrow iso
  have : B.IsLocalizedEquivalence := quotient.isLocalizerEquivalence iso
  exact .mk' B

end LocalizerMorphism

end CategoryTheory

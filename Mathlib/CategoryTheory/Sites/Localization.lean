/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Sites.Sheafification

/-! The sheaf category as a localized category

In this file, it is shown that the category of sheaves `Sheaf J A` is a localization
of the category `Presheaf J A` with respect to the class `J.W` of morphisms
of presheaves which become isomorphisms after applying the sheafification functor.

-/

namespace CategoryTheory

open Category

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A]

namespace GrothendieckTopology

/-- The class of morphisms of presheaves which become isomorphisms after sheafification.
(See `GrothendieckTopology.W_iff`.) -/
@[pp_dot]
def W : MorphismProperty (Cᵒᵖ ⥤ A) := fun _ P₂ f =>
  ∀ Q, Presheaf.IsSheaf J Q → Function.Bijective (fun (g : P₂ ⟶ Q) => f ≫ g)

instance : (W (A := A) J).ContainsIdentities where
  id_mem' P Q _ := by
    simp only [id_comp]
    exact Function.bijective_id

instance : (W (A := A) J).IsMultiplicative where
  stableUnderComposition P₁ P₂ P₃ f g hf hg Q hQ := by
    simpa using Function.Bijective.comp (hf Q hQ) (hg Q hQ)

lemma W_postcomp_iff {P₁ P₂ P₃ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hg : J.W g) :
    J.W (f ≫ g) ↔ J.W f := by
  constructor
  · intro hfg Q hQ
    exact (Function.Bijective.of_comp_iff _ (hg Q hQ)).1 (by simpa using hfg Q hQ)
  · intro hf
    exact J.W.comp_mem _ _ hf hg

lemma W_precomp_iff {P₁ P₂ P₃ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hf : J.W f) :
    J.W (f ≫ g) ↔ J.W g := by
  constructor
  · intro hfg Q hQ
    exact (Function.Bijective.of_comp_iff' (hf Q hQ) _).1 (by simpa using hfg Q hQ)
  · intro hg
    exact J.W.comp_mem _ _ hf hg

section

variable {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂)

lemma W_of_isIso [IsIso f] : J.W f := fun Q _ => by
  constructor
  · intro _ _ h
    simpa only [← cancel_epi f] using h
  · intro g
    exact ⟨inv f ≫ g, by simp⟩

lemma W_iff_isIso (hP₁ : Presheaf.IsSheaf J P₁) (hP₂ : Presheaf.IsSheaf J P₂) :
    J.W f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hP₁).2 (𝟙 _)
    dsimp at hg
    exact ⟨g, hg, (hf _ hP₂).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · intro
    exact W_of_isIso J f

end

variable [HasWeakSheafify J A]

lemma W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P) := fun Q hQ => by
  let e : (sheafify J P ⟶ Q) ≃ (P ⟶ Q) :=
    equivOfFullyFaithful (F := sheafToPresheaf J A).symm.trans
      ((sheafificationAdjunction J A).homEquiv P ⟨Q, hQ⟩)
  convert e.bijective
  ext1 f
  dsimp [e]
  obtain ⟨g, rfl⟩ : ∃ (g : (presheafToSheaf J A).obj P ⟶ ⟨Q, hQ⟩),
    f = (sheafToPresheaf J A).map g := ⟨⟨f⟩, rfl⟩
  erw [equivOfFullyFaithful_symm_apply]
  rw [Functor.preimage_map]
  erw [Adjunction.homEquiv_unit]

lemma W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso ((presheafToSheaf J A).map f) := by
  rw [← W_postcomp_iff J f (toSheafify J P₂) (J.W_toSheafify P₂),
    toSheafify_naturality, W_precomp_iff J _ _ (J.W_toSheafify P₁),
    J.W_iff_isIso _ ((presheafToSheaf J A).obj P₁).cond ((presheafToSheaf J A).obj P₂).cond]
  constructor
  · intro (h : IsIso ((sheafToPresheaf J A).map ((presheafToSheaf J A).map f)))
    exact isIso_of_reflects_iso _ (sheafToPresheaf J A)
  · intro
    change IsIso ((sheafToPresheaf J A).map ((presheafToSheaf J A).map f))
    infer_instance

variable (A)

lemma W_eq_inverseImage_isomorphisms :
    J.W = (MorphismProperty.isomorphisms _).inverseImage (presheafToSheaf J A) := by
  ext P₁ P₂ f
  rw [W_iff]
  rfl

lemma W_isInvertedBy_presheafToSheaf :
    J.W.IsInvertedBy (presheafToSheaf J A) :=
  fun P₁ P₂ f hf => by simpa only [W_iff] using hf

instance : (presheafToSheaf J A).IsLocalization J.W := by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

end GrothendieckTopology

end CategoryTheory

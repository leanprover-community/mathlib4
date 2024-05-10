/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The sheaf category as a localized category

In this file, it is shown that the category of sheaves `Sheaf J A` is a localization
of the category `Presheaf J A` with respect to the class `J.W` of morphisms
of presheaves which become isomorphisms after applying the sheafification functor.

-/

namespace CategoryTheory

open Localization

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A : Type*} [Category A]

namespace GrothendieckTopology

/-- The class of morphisms of presheaves which become isomorphisms after sheafification.
(See `GrothendieckTopology.W_iff`.) -/
abbrev W : MorphismProperty (Cᵒᵖ ⥤ A) := Localization.LeftBousfield.W (Presheaf.IsSheaf J)

/-
section

variable {G : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : G ⊣ sheafToPresheaf J A)

lemma W_adj_unit_app (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P) := fun Q hQ => by
  let e := equivOfFullyFaithful (F := sheafToPresheaf J A).symm.trans (adj.homEquiv P ⟨Q, hQ⟩)
  convert e.bijective
  ext1 f
  dsimp [e]
  obtain ⟨g, rfl⟩ : ∃ (g : G.obj P ⟶ ⟨Q, hQ⟩),
    f = (sheafToPresheaf J A).map g := ⟨⟨f⟩, rfl⟩
  erw [equivOfFullyFaithful_symm_apply]
  rw [Functor.preimage_map]
  erw [Adjunction.homEquiv_unit]

lemma W_iff_isIso_map_of_adjunction {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso (G.map f) := by
  rw [← W_postcomp_iff J f _ (J.W_adj_unit_app adj P₂)]
  erw [adj.unit.naturality f]
  rw [W_precomp_iff J _ _ (J.W_adj_unit_app adj P₁),
    J.W_iff_isIso _ (G.obj P₁).cond (G.obj P₂).cond]
  dsimp
  constructor
  · intro (h : IsIso ((sheafToPresheaf J A).map (G.map f)))
    exact isIso_of_reflects_iso _ (sheafToPresheaf J A)
  · intro
    change IsIso ((sheafToPresheaf J A).map (G.map f))
    infer_instance

lemma W_eq_inverseImage_isomorphisms_of_adjunction :
    J.W = (MorphismProperty.isomorphisms _).inverseImage G := by
  ext P₁ P₂ f
  rw [J.W_iff_isIso_map_of_adjunction adj]
  rfl

lemma isLocalization_of_adjunction : G.IsLocalization J.W := by
  rw [J.W_eq_inverseImage_isomorphisms_of_adjunction adj]
  exact adj.isLocalization

end

section

variable [HasWeakSheafify J A]

lemma W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P) :=
  J.W_adj_unit_app (sheafificationAdjunction J A) P

lemma W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso ((presheafToSheaf J A).map f) :=
  J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f

variable (A)

lemma W_eq_inverseImage_isomorphisms :
    J.W = (MorphismProperty.isomorphisms _).inverseImage (presheafToSheaf J A) := by
  ext P₁ P₂ f
  rw [W_iff]
  rfl

instance : (presheafToSheaf J A).IsLocalization J.W := by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

end

-/

end GrothendieckTopology

end CategoryTheory

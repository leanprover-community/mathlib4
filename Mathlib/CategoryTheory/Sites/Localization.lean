/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The sheaf category as a localized category

In this file, it is shown that the category of sheaves `Sheaf J A` is a localization
of the category `Presheaf J A` with respect to the class `J.W` of morphisms
of presheaves which become isomorphisms after applying the sheafification functor.

-/

universe w

@[expose] public section

namespace CategoryTheory

open Localization

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A : Type*} [Category* A]

namespace GrothendieckTopology

/-- The class of morphisms of presheaves which become isomorphisms after sheafification.
(See `GrothendieckTopology.W_iff`.) -/
abbrev W : MorphismProperty (Cᵒᵖ ⥤ A) := ObjectProperty.isLocal (Presheaf.IsSheaf J)

variable (A) in
lemma W_eq_isLocal_range_sheafToPresheaf_obj :
    J.W = ObjectProperty.isLocal (· ∈ Set.range (sheafToPresheaf J A).obj) := by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.property

@[deprecated (since := "2025-11-20")] alias W_eq_W_range_sheafToPresheaf_obj :=
  W_eq_isLocal_range_sheafToPresheaf_obj

lemma W_sheafToPresheaf_map_iff_isIso {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) :
    J.W ((sheafToPresheaf J A).map φ) ↔ IsIso φ := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj,
    ObjectProperty.isLocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, isIso_iff_of_reflects_iso]

section Adjunction

variable {G : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A}

lemma W_adj_unit_app (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P) := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_adj_unit_app adj P

lemma W_iff_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A)
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso (G.map f) := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_iff_isIso_map adj f

lemma W_eq_inverseImage_isomorphisms_of_adjunction (adj : G ⊣ sheafToPresheaf J A) :
    J.W = (MorphismProperty.isomorphisms _).inverseImage G := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj,
    ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]

end Adjunction

section HasWeakSheafify

variable [HasWeakSheafify J A]

lemma W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P) :=
  J.W_adj_unit_app (sheafificationAdjunction J A) P

lemma W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso ((presheafToSheaf J A).map f) :=
  J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f

variable (A) in
lemma W_eq_inverseImage_isomorphisms :
    J.W = (MorphismProperty.isomorphisms _).inverseImage (presheafToSheaf J A) :=
  J.W_eq_inverseImage_isomorphisms_of_adjunction (sheafificationAdjunction J A)

instance : (presheafToSheaf J A).IsLocalization J.W := by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

end HasWeakSheafify

end GrothendieckTopology

lemma Sieve.W_shrinkFunctor_ι_of_mem [LocallySmall.{w} C] {X : C} (S : Sieve X) (hS : S ∈ J X) :
    J.W (Sieve.shrinkFunctor.{w} S).ι := by
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  rw [← Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
  exact hZ _ hS

variable {D : Type*} [Category* D] {K : GrothendieckTopology D}

/-- SGA 4 III 1.2 (ii) => (i) -/
lemma Presieve.IsSheaf.comp_of_W_map_of_adjunction
    [LocallySmall.{w} C] {F : C ⥤ D} {H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)}
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    (h : ∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ J X → K.W (H.map <| (Sieve.shrinkFunctor.{w} S).ι))
    (G : Dᵒᵖ ⥤ Type w) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  intro X S hS
  rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp, ← Functor.whiskeringLeft_obj_obj,
    ← adj.bijective_map_comp_iff]
  refine h hS _ ?_
  rwa [isSheaf_iff_isSheaf_of_type]

end CategoryTheory

/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Localization.Trifunctor
import Mathlib.CategoryTheory.Monoidal.Multifunctor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.Tactic.CategoryTheory.Coherence

/-!

# Universal property of localized monoidal categories

This file proves that, given a monoidal localization functor `L : C ⥤ D`, and a functor
`F : D ⥤ E` to a monoidal category, such that `L ⋙ F` is monoidal, then `F` is monoidal. See
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`.
-/

universe u

namespace CategoryTheory

open CategoryTheory MonoidalCategory Functor Monoidal LaxMonoidal OplaxMonoidal

namespace Localization.Monoidal

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] [W.ContainsIdentities] [Lifting L W G F]

@[simps]
instance lifting₂CurriedTensorPre :
    Lifting₂ L L W W (curriedTensorPre G) (curriedTensorPre F) where
  iso := curriedTensorPreFunctor.mapIso (Lifting.iso L W G F)

@[simps]
instance lifting₂CurriedTensorPost :
    Lifting₂ L L W W (curriedTensorPost G) (curriedTensorPost F) where
  iso := (postcompose₂.obj F).mapIso (curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

/--
The natural isomorphism of bifunctors `F - ⊗ F - ≅ F (- ⊗ -)`, given that `L ⋙ F` is monoidal.
-/
noncomputable def curriedTensorPreIsoPost : curriedTensorPre F ≅ curriedTensorPost F :=
  lift₂NatIso L L W W (curriedTensorPre G) (curriedTensorPost G) _ _
    (Functor.curriedTensorPreIsoPost G)

@[reassoc]
noncomputable def curriedTensorPreIsoPost_hom_app_app (X₁ X₂ : C) :
    letI e := Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).app (L.obj X₂) =
      (e.hom.app _ ⊗ₘ e.hom.app _) ≫ LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _) := by
  simp [curriedTensorPreIsoPost]


lemma curriedTensorPreIsoPost_hom_app_app' {X₁ X₂ : C} {Y₁ Y₂ : D}
    (e₁ : Y₁ ≅ L.obj X₁) (e₂ : Y₂ ≅ L.obj X₂) :
    letI e := Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app Y₁).app Y₂ =
      ((F.map e₁.hom ≫ e.hom.app _) ⊗ₘ (F.map e₂.hom ≫ e.hom.app _)) ≫
        LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _≫ (e₁.inv ⊗ₘ e₂.inv)) := by
  have h₁ := ((curriedTensorPreIsoPost L W F G).hom.app Y₁).naturality e₂.hom
  have h₂ := congr_app ((curriedTensorPreIsoPost L W F G).hom.naturality e₁.hom)
  dsimp at h₁ h₂ ⊢
  rw [← cancel_mono (F.map (Y₁ ◁ e₂.hom)), ← h₁, ← cancel_mono (F.map (e₁.hom ▷ L.obj X₂)),
    Category.assoc, ← h₂, curriedTensorPreIsoPost_hom_app_app, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc, ← tensorHom_def'_assoc, tensorHom_comp_tensorHom_assoc,
    ← Functor.map_comp, ← tensorHom_def', ← Functor.map_comp, Category.assoc,
    tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, tensorHom_id, id_whiskerRight,
    Category.comp_id]

/--
Monoidal structure on `F`, given that `L ⋙ F` is monoidal, where `L` is a localization functor.
-/
@[simps!]
noncomputable def functorCoreMonoidalOfComp : F.CoreMonoidal := by
  letI e := Lifting.iso L W G F
  refine Functor.CoreMonoidal.ofBifunctor
    (εIso G ≪≫ e.symm.app _ ≪≫ F.mapIso (εIso L).symm) (curriedTensorPreIsoPost L W F G) ?_ ?_ ?_
  · refine natTrans₃_ext L L L W W W (fun X₁ X₂ X₃ ↦ ?_)
    dsimp
    rw [curriedTensorPreIsoPost_hom_app_app, curriedTensorPreIsoPost_hom_app_app,
      curriedTensorPreIsoPost_hom_app_app' L W F G (μIso L _ _) (Iso.refl _),
      curriedTensorPreIsoPost_hom_app_app' L W F G (Iso.refl _) (μIso L _ _)]
    simp only [comp_whiskerRight, map_comp, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    rw [tensorHom_def', tensorHom_def (e.hom.app X₂)]
    have e₁ :
        F.map (δ L X₁ X₂) ▷ F.obj (L.obj X₃) ≫ F.map (μ L X₁ X₂) ▷ F.obj (L.obj X₃) = 𝟙 _ := by
      grind [_=_ MonoidalCategory.comp_whiskerRight, MonoidalCategory.id_whiskerRight, Monoidal.δ_μ]
    have e₂ : G.obj X₁ ◁ F.map (δ L X₂ X₃) ≫ G.obj X₁ ◁ F.map (μ L X₂ X₃) = 𝟙 _ := by
      grind [_=_ MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id, Monoidal.δ_μ]
    monoidal_simps
    congr 2
    dsimp [e]
    simp only [comp_whiskerRight, map_id, Category.id_comp, Category.assoc,
      ← whisker_exchange_assoc, tensor_whiskerLeft, MonoidalCategory.whiskerLeft_comp]
    simp only [← associator_inv_naturality_left_assoc, Iso.inv_hom_id_assoc, whisker_exchange_assoc,
      associator_inv_naturality_right_assoc, reassoc_of% e₁, reassoc_of% e₂]
    congr 1
    simp [← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      - MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc,
      tensor_whiskerLeft_symm, -tensor_whiskerLeft,
      ← LaxMonoidal.associativity_assoc G, ← Functor.map_comp]
  · refine natTrans_ext L W (fun X₂ ↦ ?_)
    have := NatTrans.congr_app ((curriedTensorPreIsoPost L W F G).hom.naturality (εIso L).inv)
      (L.obj X₂)
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, curriedTensorPreIsoPost_hom_app_app, ← comp_whiskerRight_assoc,
      -comp_whiskerRight, tensorHom_def, ← whisker_exchange_assoc, ← map_comp]
  · refine natTrans_ext L W (fun X₁ ↦ ?_)
    have := ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).naturality (εIso L).inv
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, curriedTensorPreIsoPost_hom_app_app, tensorHom_def,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← map_comp]

/--
Monoidal structure on `F`, given that `L ⋙ F` is monoidal, where `L` is a localization functor.
-/
noncomputable def functorMonoidalOfComp : F.Monoidal :=
  (functorCoreMonoidalOfComp L W F G).toMonoidal

@[reassoc]
lemma functorMonoidalOfComp_ε : letI := functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    ε F = ε G ≫ e.inv.app _ ≫ F.map (η L) := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_ε]

@[reassoc]
lemma functorMonoidalOfComp_μ (X Y : C) : letI := functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    μ F (L.obj X) (L.obj Y) = (e.hom.app _ ⊗ₘ e.hom.app _) ≫ μ G X Y ≫ e.inv.app _ ≫
        F.map (δ L _ _) := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_μ, curriedTensorPreIsoPost_hom_app_app]

instance natTrans_isMonoidal :
    letI : F.Monoidal := functorMonoidalOfComp L W F G
    (Lifting.iso L W G F).hom.IsMonoidal := by
  letI : F.Monoidal := functorMonoidalOfComp L W F G
  refine ⟨?_, fun _ _ ↦ ?_⟩
  · simp [functorMonoidalOfComp_ε]
  · simp [functorMonoidalOfComp_μ]

end CategoryTheory.Localization.Monoidal

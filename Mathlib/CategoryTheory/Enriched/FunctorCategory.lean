/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Functor categories are enriched

-/

universe v v' v'' u u' u''

namespace CategoryTheory

open Category Opposite

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C]

open MonoidalCategory

-- `SimplicialCategory` should be an abbrev for this
class EnrichedOrdinaryCategory extends EnrichedCategory V C where
  homEquiv (K L : C) : (K ⟶ L) ≃ (𝟙_ V ⟶ EnrichedCategory.Hom K L)
  homEquiv_id (K : C) : homEquiv K K (𝟙 K) = eId V K := by aesop_cat
  homEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    homEquiv K M (f ≫ g) = (λ_ _).inv ≫ (homEquiv K L f ⊗ homEquiv L M g) ≫
      eComp V K L M := by aesop_cat

section

variable {C} [EnrichedOrdinaryCategory V C]

def eHomEquiv {K L : C} : (K ⟶ L) ≃ (𝟙_ V ⟶ EnrichedCategory.Hom K L) :=
  EnrichedOrdinaryCategory.homEquiv K L

lemma eHomEquiv_id (K : C) : eHomEquiv V (𝟙 K) = eId V K :=
  EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]
lemma eHomEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    eHomEquiv V (f ≫ g) = (λ_ _).inv ≫ (eHomEquiv V f ⊗ eHomEquiv V g) ≫ eComp V K L M :=
  EnrichedOrdinaryCategory.homEquiv_comp _ _

attribute [local simp] eHomEquiv_id eHomEquiv_comp

variable (C)

@[simps]
def eHomBifunctor : Cᵒᵖ ⥤ C ⥤ V where
  obj K :=
    { obj := fun L ↦ K.unop ⟶[V] L
      map := fun {L L'} g ↦ (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V K.unop L L'
      map_comp := fun {L L' L''} f g ↦ by
        dsimp
        rw [eHomEquiv_comp, assoc, assoc, Iso.cancel_iso_inv_left,
          MonoidalCategory.whiskerLeft_comp_assoc,
          MonoidalCategory.whiskerLeft_comp_assoc, ← e_assoc]
        nth_rw 2 [← id_tensorHom]
        rw [associator_inv_naturality_assoc, id_tensorHom, tensorHom_def, assoc,
          whisker_exchange_assoc, MonoidalCategory.whiskerRight_id,
          MonoidalCategory.whiskerRight_id, assoc, assoc, assoc, assoc,
          Iso.inv_hom_id_assoc, triangle_assoc_comp_left_inv_assoc,
          MonoidalCategory.whiskerRight_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] }
  map {K K'} f :=
    { app := fun L ↦ (λ_ _).inv ≫ eHomEquiv V f.unop ▷ _ ≫ eComp V K'.unop K.unop L
      naturality := fun L L' g ↦ by
        dsimp
        have := ((λ_ _).inv ≫ _ ◁ (ρ_ _).inv ≫ _ ◁ _ ◁ eHomEquiv V g ≫
          eHomEquiv V f.unop ▷ _) ≫= (e_assoc V K'.unop K.unop L L').symm
        simp only [assoc] at this ⊢
        conv_lhs at this =>
          rw [← whisker_exchange_assoc,
            whiskerLeft_rightUnitor_inv, id_whiskerLeft, id_whiskerLeft, assoc,
            assoc, assoc, assoc, assoc, Iso.inv_hom_id_assoc, leftUnitor_tensor,
            MonoidalCategory.whiskerRight_id, assoc, assoc, assoc,
            Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
        rw [this, ← MonoidalCategory.whiskerLeft_comp_assoc,
            whisker_exchange_assoc, MonoidalCategory.whiskerLeft_comp,
            whiskerLeft_rightUnitor_inv, assoc, assoc, ← associator_naturality_right_assoc,
            Iso.hom_inv_id_assoc, whisker_exchange_assoc, MonoidalCategory.whiskerRight_id,
            assoc, assoc, Iso.inv_hom_id_assoc] }
  map_comp {K K' K''} f g := by
    ext L
    dsimp
    rw [eHomEquiv_comp, assoc, assoc, Iso.cancel_iso_inv_left, comp_whiskerRight,
      comp_whiskerRight, assoc, assoc, ← e_assoc', tensorHom_def', comp_whiskerRight, assoc,
      id_whiskerLeft, ← comp_whiskerRight_assoc, Iso.inv_hom_id_assoc, comp_whiskerRight_assoc,
      associator_naturality_left_assoc, ← whisker_exchange_assoc, leftUnitor_inv_whiskerRight,
      id_whiskerLeft, assoc, assoc, assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]

end

open Limits

namespace Enriched

variable {C} {J : Type u''} [Category.{v''} J] [EnrichedOrdinaryCategory V C]

namespace FunctorCategory

section

variable (F₁ F₂ F₃ : J ⥤ C)

@[simps!]
def diagram : Jᵒᵖ ⥤ J ⥤ V := F₁.op ⋙ eHomBifunctor V C ⋙ (whiskeringLeft J C V).obj F₂

abbrev HasEnrichedHom := HasEnd (diagram V F₁ F₂)

section

variable [HasEnrichedHom V F₁ F₂]

noncomputable abbrev enrichedHom : V := end_ (diagram V F₁ F₂)

noncomputable abbrev enrichedHomπ (j : J) : enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j :=
  end_.π _ j

@[reassoc]
lemma enrichedHom_condition {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ (ρ_ _).inv ≫
      _ ◁ (eHomEquiv V) (F₂.map f) ≫ eComp V _ _ _  =
    enrichedHomπ V F₁ F₂ j ≫ (λ_ _).inv ≫
      (eHomEquiv V) (F₁.map f) ▷ _ ≫ eComp V _ _ _ :=
  end_.condition (diagram V F₁ F₂) f

variable {F₁ F₂}

noncomputable def homEquiv : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  toFun τ := end_.lift (fun j ↦ eHomEquiv V (τ.app j)) (fun i j f ↦ by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc]
    · dsimp
      simp only [← NatTrans.naturality, eHomEquiv_comp, tensorHom_def', id_whiskerLeft,
        assoc, Iso.inv_hom_id_assoc])
  invFun g :=
    { app := fun j ↦ (eHomEquiv V).symm (g ≫ end_.π _ j)
      naturality := fun i j f ↦ (eHomEquiv V).injective (by
        dsimp
        simp only [eHomEquiv_comp, Equiv.apply_symm_apply, Iso.cancel_iso_inv_left]
        conv_rhs =>
          rw [tensorHom_def_assoc, MonoidalCategory.whiskerRight_id_assoc, assoc,
            enrichedHom_condition V F₁ F₂ f]
        conv_lhs =>
          rw [tensorHom_def'_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
            id_whiskerLeft_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc, unitors_equal]) }
  left_inv τ := by aesop
  right_inv g := by aesop

@[reassoc (attr := simp)]
lemma homEquiv_apply_π (τ : F₁ ⟶ F₂) (j : J) :
    homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.app j) := by
  simp [homEquiv]

end

section

variable [HasEnrichedHom V F₁ F₁]

attribute [local simp] eHomEquiv_id eHomEquiv_comp

noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ := homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]
lemma enrichedId_π (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  simp [enrichedId]

@[simp]
lemma homEquiv_id : homEquiv V (𝟙 F₁) = enrichedId V F₁ := rfl

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

noncomputable def enrichedComp : enrichedHom V F₁ F₂ ⊗ enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j ↦ (end_.π _ j ⊗ end_.π _ j) ≫ eComp V _ _ _) (fun i j f ↦ by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i ⊗ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · sorry
    · have := end_.condition (diagram V F₁ F₂) f
      dsimp at this
      conv_rhs => rw [assoc, tensorHom_def'_assoc]
      conv_lhs =>
        rw [tensorHom_def'_assoc, ← comp_whiskerRight_assoc,
          ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
          assoc, assoc]
        dsimp
        rw [this, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
          comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
          ← associator_inv_naturality_left_assoc, ← e_assoc',
          Iso.inv_hom_id_assoc, ← whisker_exchange_assoc, id_whiskerLeft_assoc,
          Iso.inv_hom_id_assoc])

@[reassoc (attr := simp)]
lemma enrichedComp_π (j : J) :
    enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j =
      (end_.π (diagram V F₁ F₂) j ⊗ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ _ _ := by
  simp [enrichedComp]

variable {F₁ F₂ F₃}

@[reassoc]
lemma homEquiv_comp (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (homEquiv V) (f ≫ g) = (λ_ (𝟙_ V)).inv ≫ ((homEquiv V) f ⊗ (homEquiv V) g) ≫
    enrichedComp V F₁ F₂ F₃ := by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, ← tensor_comp_assoc]

end

end

variable (J C) [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂]

noncomputable def enrichedOrdinaryCategory : EnrichedOrdinaryCategory V (J ⥤ C) where
  Hom F₁ F₂ := enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  id_comp F₁ F₂ := by
    ext j
    rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def, assoc,
      ← comp_whiskerRight_assoc, enrichedId_π, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, assoc, Iso.inv_hom_id_assoc]
    dsimp
    rw [e_id_comp, comp_id]
  comp_id F₁ F₂ := by
    ext j
    rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def', assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, enrichedId_π,
      whisker_exchange_assoc, MonoidalCategory.whiskerRight_id, assoc, assoc,
      Iso.inv_hom_id_assoc]
    dsimp
    rw [e_comp_id, comp_id]
  assoc F₁ F₂ F₃ F₄ := by
    ext j
    conv_lhs =>
      rw [assoc, assoc, enrichedComp_π,
        tensorHom_def_assoc, ← comp_whiskerRight_assoc, enrichedComp_π,
        comp_whiskerRight_assoc, ← whisker_exchange_assoc,
        ← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← associator_inv_naturality_assoc]
    conv_rhs =>
      rw [assoc, enrichedComp_π, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        enrichedComp_π, MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
        whisker_exchange_assoc, ← tensorHom_def_assoc]
    dsimp
    rw [e_assoc]
  homEquiv _ _ := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

end FunctorCategory

end Enriched

end CategoryTheory

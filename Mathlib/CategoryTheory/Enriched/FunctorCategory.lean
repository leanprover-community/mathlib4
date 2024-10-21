/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Functor.Category

/-!
# Functor categories are enriched

-/

universe v v' v'' u u' u''

namespace CategoryTheory

open Category Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C] (F : Jᵒᵖ ⥤ J ⥤ C)

@[simps]
def multicospanIndexEnd : MulticospanIndex C where
  L := J
  R := Arrow J
  fstTo f := f.left
  sndTo f := f.right
  left j := (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

abbrev EndCone := Multifork (multicospanIndexEnd F)

namespace EndCone

variable {F}
variable (c : EndCone F)

@[reassoc]
lemma condition {i j : J} (f : i ⟶ j) :
    c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j :=
  Multifork.condition c (Arrow.mk f)

variable {c} (hc : IsLimit c)

namespace IsLimit

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

abbrev lift : X ⟶ c.pt :=
  Multifork.IsLimit.lift hc (fun j ↦ f j) (fun _ ↦ hf _)

end

include hc in
lemma hom_ext {X : C} {f g : X ⟶ c.pt} (h : ∀ j, f ≫ c.ι j = g ≫ c.ι j) : f = g :=
  Multifork.IsLimit.hom_ext hc h

end IsLimit

end EndCone

section

abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)

variable [HasEnd F]

noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)

section

noncomputable abbrev end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _

@[reassoc]
lemma end_.condition {i j : J} (f : i ⟶ j) :
    π F i ≫ (F.obj (op i)).map f = π F j ≫ (F.map f.op).app j := by
  apply EndCone.condition

variable {F}

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

noncomputable def end_.lift : X ⟶ end_ F :=
  EndCone.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]
lemma end_.lift_π (j : J) : lift f hf ≫ π F j = f j := by
  apply IsLimit.fac

end

@[ext]
lemma hom_ext {X : C} {f g : X ⟶ end_ F} (h : ∀ j, f ≫ end_.π F j = g ≫ end_.π F j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun _ ↦ h _)

end

end


end Limits

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C]

open MonoidalCategory

-- `SimplicialCategory` should be an abbrev for this
class StronglyEnrichedCategory extends EnrichedCategory V C where
  homEquiv (K L : C) : (K ⟶ L) ≃ (𝟙_ V ⟶ EnrichedCategory.Hom K L)
  homEquiv_id (K : C) : homEquiv K K (𝟙 K) = eId V K := by aesop_cat
  homEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    homEquiv K M (f ≫ g) = (λ_ _).inv ≫ (homEquiv K L f ⊗ homEquiv L M g) ≫
      eComp V K L M := by aesop_cat

section

variable {C} [StronglyEnrichedCategory V C]

def eHomEquiv {K L : C} : (K ⟶ L) ≃ (𝟙_ V ⟶ EnrichedCategory.Hom K L) :=
  StronglyEnrichedCategory.homEquiv K L

lemma eHomEquiv_id (K : C) : eHomEquiv V (𝟙 K) = eId V K :=
  StronglyEnrichedCategory.homEquiv_id _

@[reassoc]
lemma eHomEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    eHomEquiv V (f ≫ g) = (λ_ _).inv ≫ (eHomEquiv V f ⊗ eHomEquiv V g) ≫ eComp V K L M :=
  StronglyEnrichedCategory.homEquiv_comp _ _

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

variable {C} {J : Type u''} [Category.{v''} J] [StronglyEnrichedCategory V C]

namespace FunctorCategory

section

variable (F₁ F₂ F₃ : J ⥤ C)

@[simps!]
def diagram : Jᵒᵖ ⥤ J ⥤ V := F₁.op ⋙ eHomBifunctor V C ⋙ (whiskeringLeft J C V).obj F₂

abbrev HasEnrichedHom := HasEnd (diagram V F₁ F₂)

noncomputable abbrev enrichedHom [HasEnrichedHom V F₁ F₂] : V := end_ (diagram V F₁ F₂)

open MonoidalCategory

section

variable [HasEnrichedHom V F₁ F₁]

attribute [local simp] eHomEquiv_id eHomEquiv_comp

noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ :=
  end_.lift (fun _ ↦ eId V _) (fun i j f ↦ by
    dsimp
    simp only [e_id_comp, ← e_comp_id, rightUnitor_inv_naturality_assoc,
      ← whisker_exchange_assoc, id_whiskerLeft, assoc, unitors_equal, Iso.inv_hom_id_assoc])

@[reassoc (attr := simp)]
lemma enrichedId_π (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  simp [enrichedId]

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

noncomputable def enrichedComp : enrichedHom V F₁ F₂ ⊗ enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j ↦ (end_.π _ j ⊗ end_.π _ j) ≫ eComp V _ _ _) (fun i j f ↦ by
    dsimp
    simp only [assoc]
    trans (end_.π (diagram V F₁ F₂) i ⊗ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · sorry
    · sorry)

@[reassoc (attr := simp)]
lemma enrichedComp_π (j : J) :
    enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j =
      (end_.π (diagram V F₁ F₂) j ⊗ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ _ _ := by
  simp [enrichedComp]

end

end

variable [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂]

noncomputable def enriched : EnrichedCategory V (J ⥤ C) where
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

end FunctorCategory

end Enriched

end CategoryTheory

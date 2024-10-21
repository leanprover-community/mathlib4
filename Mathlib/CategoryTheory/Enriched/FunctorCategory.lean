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
  L := ULift.{max u v} J
  R := Arrow J
  fstTo f := ULift.up f.left
  sndTo f := ULift.up f.right
  left j := (F.obj (op j.down)).obj j.down
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

abbrev EndCone := Multifork (multicospanIndexEnd F)

namespace EndCone

variable {F}
variable {c : EndCone F} (hc : IsLimit c)

def π' (j : J) : c.pt ⟶ (F.obj (op j)).obj j := Multifork.ι c ⟨j⟩

namespace IsLimit

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

def lift : X ⟶ c.pt :=
  Multifork.IsLimit.lift hc (fun ⟨j⟩ ↦ f j) (fun _ ↦ hf _)

@[reassoc (attr := simp)]
lemma lift_π' (j : J) : lift hc f hf ≫ c.π' j = f j := by
  apply IsLimit.fac

end

include hc in
lemma hom_ext {X : C} {f g : X ⟶ c.pt} (h : ∀ j, f ≫ c.π' j = g ≫ c.π' j) : f = g :=
  Multifork.IsLimit.hom_ext hc (fun ⟨j⟩ ↦ h j)

end IsLimit

end EndCone

section

abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)

variable [HasEnd F]

noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)

section

noncomputable def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _

variable {F}

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

noncomputable def end_.lift : X ⟶ end_ F :=
  EndCone.IsLimit.lift (F := F) (hc := limit.isLimit _) f hf

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
      map_id := by aesop_cat
      map_comp := fun {L L' L''} f g ↦ by
        dsimp
        simp only [eHomEquiv_comp, MonoidalCategory.whiskerLeft_comp, assoc,
          Iso.cancel_iso_inv_left]
        sorry }
  map {K K'} f :=
    { app := fun L ↦ (λ_ _).inv ≫ eHomEquiv V f.unop ▷ _ ≫ eComp V K'.unop K.unop L
      naturality := fun L L' g ↦ by
        dsimp
        simp only [assoc]
        convert ((λ_ _).inv ≫ _ ◁ (ρ_ _).inv ≫ _ ◁ _ ◁ eHomEquiv V g ≫
          eHomEquiv V f.unop ▷ _) ≫= (e_assoc V K'.unop K.unop L L').symm using 1
        · rw [assoc, assoc, assoc, ← whisker_exchange_assoc,
            whiskerLeft_rightUnitor_inv, id_whiskerLeft, id_whiskerLeft, assoc,
            assoc, assoc, assoc, assoc, Iso.inv_hom_id_assoc]
          simp only [← assoc]; congr 5
          monoidal_coherence
        · dsimp
          rw [assoc, assoc, assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
            whisker_exchange_assoc, MonoidalCategory.whiskerLeft_comp,
            whiskerLeft_rightUnitor_inv, assoc, assoc, ← associator_naturality_right_assoc,
            Iso.hom_inv_id_assoc, whisker_exchange_assoc, MonoidalCategory.whiskerRight_id,
            assoc, assoc, Iso.inv_hom_id_assoc] }
  map_id := by aesop_cat
  map_comp := by aesop_cat

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

noncomputable def enrichedHom [HasEnrichedHom V F₁ F₂] : V := end_ (diagram V F₁ F₂)

open MonoidalCategory

section

variable [HasEnrichedHom V F₁ F₁]

attribute [local simp] eHomEquiv_id eHomEquiv_comp

noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ :=
  end_.lift (fun _ ↦ eId V _) (fun i j f ↦ by
    dsimp
    sorry)

@[reassoc]
lemma enrichedId_π' (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  dsimp [enrichedId]
  rw [end_.lift_π]

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

noncomputable def enrichedComp : enrichedHom V F₁ F₂ ⊗ enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j ↦ (end_.π _ j ⊗ end_.π _ j) ≫ eComp V _ _ _)
    sorry

end

end

variable [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂]

noncomputable def enriched : EnrichedCategory V (J ⥤ C) where
  Hom F₁ F₂ := enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end FunctorCategory

end Enriched

end CategoryTheory

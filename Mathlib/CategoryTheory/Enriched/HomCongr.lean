/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import Mathlib.CategoryTheory.Enriched.Ordinary

/-!
# Congruence of enriched homs

In a `V`-enriched ordinary category `C`, isomorphisms in `C` induce
isomorphisms between hom-objects in `V`.

The treatment here parallels that for unenriched categories in
`Mathlib/CategoryTheory/HomCongr.lean` and that for sorts in
`Mathlib/Logic/Equiv/Defs.lean` (cf. `Equiv.arrowCongr`). Note, however, that
they construct equivalences between `Type`s and `Sort`s, respectively, while
in this file we construct isomorphisms between objects in `V`.
-/

universe v' v u u'

namespace CategoryTheory
namespace Iso

open Category MonoidalCategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- If we have isomorphisms `α : X ≅ X₁` and `β : Y ≅ Y₁` in `C`, then we can
construct an isomorphism between `V` objects `X ⟶[V] Y` and `X₁ ⟶[V] Y₁`. -/
@[simp]
def eHomCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶[V] Y) ≅ (X₁ ⟶[V] Y₁) where
  hom := eHomWhiskerRight V α.inv Y ≫ eHomWhiskerLeft V X₁ β.hom
  inv := eHomWhiskerRight V α.hom Y₁ ≫ eHomWhiskerLeft V X β.inv
  hom_inv_id := by
    rw [← eHom_whisker_exchange, assoc]
    rw [← eHomWhiskerRight_comp_assoc, hom_inv_id, eHomWhiskerRight_id, id_comp]
    rw [← eHomWhiskerLeft_comp, hom_inv_id, eHomWhiskerLeft_id]
  inv_hom_id := by
    rw [← eHom_whisker_exchange, assoc]
    rw [← eHomWhiskerRight_comp_assoc, inv_hom_id, eHomWhiskerRight_id, id_comp]
    rw [← eHomWhiskerLeft_comp, inv_hom_id, eHomWhiskerLeft_id]

@[simp]
lemma eHomCongr_refl {X Y : C} :
    eHomCongr V (Iso.refl X) (Iso.refl Y) = Iso.refl _ := by aesop

@[simp]
lemma eHomCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂)
    (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) :
    eHomCongr V (α₁ ≪≫ α₂) (β₁ ≪≫ β₂) =
      eHomCongr V α₁ β₁ ≪≫ eHomCongr V α₂ β₂ := by
  ext; simp [eHom_whisker_exchange_assoc]

@[simp]
lemma eHomCongr_symm {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (eHomCongr V α β).symm = eHomCongr V α.symm β.symm := rfl

/-- `eHomCongr` respects composition of morphisms. Recall that for any
pair of composable arrows `f : X ⟶ Y` and `g : Y ⟶ Z` in `C`, the composite
`f ≫ g` in `C` defines a morphism `𝟙_ V ⟶ (X ⟶[V] Z)` in `V`. Composing with
the isomorphism `eHomCongr V α γ` yields a morphism in `V` that can be factored
through the enriched composition map as shown:
`𝟙_ V ⟶ 𝟙_ V ⊗ 𝟙_ V ⟶ (X₁ ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z₁) ⟶ (X₁ ⟶[V] Z₁)`. -/
lemma eHomCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).hom =
      (λ_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).hom) ▷ _ ≫
        _ ◁ (eHomEquiv V g ≫ (eHomCongr V β γ).hom) ≫ eComp V X₁ Y₁ Z₁ := by
  dsimp only [eHomCongr]
  simp only [assoc, MonoidalCategory.whiskerRight_id,
    MonoidalCategory.whiskerLeft_comp]
  rw [rightUnitor_inv_naturality_assoc, rightUnitor_inv_naturality_assoc,
    rightUnitor_inv_naturality_assoc, hom_inv_id_assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← eComp_eHomWhiskerLeft]
  rw [eHom_whisker_cancel_assoc]
  rw [← eComp_eHomWhiskerRight_assoc, ← tensorHom_def_assoc,
    ← eHomEquiv_comp_assoc]

/-- The inverse map defined by `eHomCongr` respects composition of morphisms. -/
lemma eHomCongr_inv_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
    (f : X₁ ⟶ Y₁) (g : Y₁ ⟶ Z₁) :
    eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).inv =
      (λ_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).inv) ▷ _ ≫
        _ ◁ (eHomEquiv V g ≫ (eHomCongr V β γ).inv) ≫ eComp V X Y Z :=
  eHomCongr_comp V α.symm β.symm γ.symm f g

end Iso
end CategoryTheory

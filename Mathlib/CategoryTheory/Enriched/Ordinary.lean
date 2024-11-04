/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda

/-!
# Enriched ordinary categories

If `V` is a monoidal category, a `V`-enriched category `C` does not need
to be a category. However, when we have both `Category C` and `EnrichedCategory V C`,
we may require that the type of morphisms `X ⟶ Y` in `C` identify to
`𝟙_ V ⟶ EnrichedCategory.Hom X Y`. This data shall be packaged in the
typeclass `EnrichedOrdinaryCategory V C`.

In particular, if `C` is a `V`-enriched category, it is shown that
the "underlying" category `ForgetEnrichment V C` is equipped with a
`EnrichedOrdinaryCategory V C` instance.

Simplicial categories are implemented in `AlgebraicTopology.SimplicialCategory.Basic`
using an abbreviation for `EnrichedOrdinaryCategory SSet C`.

-/

universe v' v u u'

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C]

/-- An enriched ordinary category is a category `C` that is also enriched
over a category `V` in such a way that morphisms `X ⟶ Y` in `C` identify
to morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V`. -/
class EnrichedOrdinaryCategory extends EnrichedCategory V C where
  /-- morphisms `X ⟶ Y` in the category identify morphisms
    `𝟙_ V ⟶ (X ⟶[V] Y)` in `V` -/
  homEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
  homEquiv_id (X : C) : homEquiv (𝟙 X) = eId V X := by aesop_cat
  homEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv (f ≫ g) = (λ_ _).inv ≫ (homEquiv f ⊗ homEquiv g) ≫
      eComp V X Y Z := by aesop_cat

variable [EnrichedOrdinaryCategory V C] {C}

/-- The bijection `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))` given by a
`EnrichedOrdinaryCategory` instance. -/
def eHomEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y)) :=
  EnrichedOrdinaryCategory.homEquiv

@[simp]
lemma eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = eId V X :=
  EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]
lemma eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = (λ_ _).inv ≫ (eHomEquiv V f ⊗ eHomEquiv V g) ≫ eComp V X Y Z :=
  EnrichedOrdinaryCategory.homEquiv_comp _ _

/-- The morphism `(X' ⟶[V] Y) ⟶ (X ⟶[V] Y)` induced by a morphism `X ⟶ X'`. -/
noncomputable def eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    (X' ⟶[V] Y) ⟶ (X ⟶[V] Y) :=
  (λ_ _).inv ≫ eHomEquiv V f ▷ _ ≫ eComp V X X' Y

@[simp]
lemma eHomWhiskerRight_id (X Y : C) : eHomWhiskerRight V (𝟙 X) Y = 𝟙 _ := by
  simp [eHomWhiskerRight]

@[simp, reassoc]
lemma eHomWhiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    eHomWhiskerRight V (f ≫ f') Y = eHomWhiskerRight V f' Y ≫ eHomWhiskerRight V f Y := by
  dsimp [eHomWhiskerRight]
  rw [assoc, assoc, eHomEquiv_comp, comp_whiskerRight_assoc, comp_whiskerRight_assoc, ← e_assoc',
    tensorHom_def', comp_whiskerRight_assoc, id_whiskerLeft, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight_assoc,
    comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
    ← associator_inv_naturality_left_assoc, Iso.inv_hom_id_assoc,
    ← whisker_exchange_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc]

/-- The morphism `(X ⟶[V] Y) ⟶ (X ⟶[V] Y')` induced by a morphism `Y ⟶ Y'`. -/
noncomputable def eHomWhiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (X ⟶[V] Y) ⟶ (X ⟶[V] Y') :=
  (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V X Y Y'

@[simp]
lemma eHomWhiskerLeft_id (X Y : C) : eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _ := by
  simp [eHomWhiskerLeft]

@[simp, reassoc]
lemma eHomWhiskerLeft_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    eHomWhiskerLeft V X (g ≫ g') = eHomWhiskerLeft V X g ≫ eHomWhiskerLeft V X g' := by
  dsimp [eHomWhiskerLeft]
  rw [assoc, assoc, eHomEquiv_comp, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, ← e_assoc, tensorHom_def,
    MonoidalCategory.whiskerRight_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_rightUnitor_assoc, whiskerLeft_rightUnitor_inv_assoc,
    triangle_assoc_comp_left_inv_assoc, MonoidalCategory.whiskerRight_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc]

@[reassoc]
lemma eHom_whisker_exchange {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    eHomWhiskerLeft V X' g ≫ eHomWhiskerRight V f Y' =
      eHomWhiskerRight V f Y ≫ eHomWhiskerLeft V X g := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  rw [assoc, assoc, assoc, assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, ← e_assoc, leftUnitor_tensor_inv_assoc,
    associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, whisker_exchange_assoc,
    MonoidalCategory.whiskerRight_id_assoc, assoc, Iso.inv_hom_id_assoc,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc]

attribute [local simp] eHom_whisker_exchange

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ V` which sends `X : Cᵒᵖ` and `Y : C` to `X ⟶[V] Y`. -/
@[simps]
noncomputable def eHomFunctor : Cᵒᵖ ⥤ C ⥤ V where
  obj X :=
    { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => eHomWhiskerLeft V X.unop φ }
  map φ :=
    { app := fun Y => eHomWhiskerRight V φ.unop Y }

instance ForgetEnrichment.EnrichedOrdinaryCategory {D : Type*} [EnrichedCategory V D] :
    EnrichedOrdinaryCategory V (ForgetEnrichment V D) where
  toEnrichedCategory := inferInstanceAs (EnrichedCategory V D)
  homEquiv := Equiv.refl _
  homEquiv_id _ := Category.id_comp _
  homEquiv_comp _ _ := Category.assoc _ _ _

end CategoryTheory

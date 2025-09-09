/-
Copyright (c) 2026 Amogh Parab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amogh Parab
-/
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Categorical Groups

A categorical group is a monoidal category equipped with a negator, and cancellation isomorphisms.
In the definition, we provide the negator as a function
* `negatorObj : C ⟶ C`
on objects. We use the notation `X′` for `negatorObj X`.
The unit and counit isomorphisms are provided componentwise. The unit and counit isomorphisms must
satisfy coherence conditions called the zigzag identities.

With the zigzag identities, we can show that the negator extends to a functor and
the unit and counit isomorphisms are natural.

## Implementation note

We make `CategoricalGroupStruct` as a typeclass to carry
only the data fields, but then have `CategoricalGroup` extend this.

## Future work

* Extend `negatorObj` to a functor `negator : C ⥤ C` and
unit and counit isomorphisms to natural isomorphisms.
* Add basic lemmas.
* Extend categorical groups to symmetric categorical groups by adding a braiding.

## References

* John C. Baez and Aaron D. Lauda. Higher-dimensional algebra V: 2-groups. Theory
Appl. Categ., 12:423–491, 2004

-/



universe u v

namespace CategoryTheory

open Category MonoidalCategory


<<<<<<< HEAD
/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`CategoricalGroup`. -/
class CategoricalGroupStruct (C : Type u) [Groupoid.{v} C] [MonoidalCategory.{v} C] where
  /-- The negator of objects -/
  negatorObj : C → C
  /-- The counit isomorphism, usually denoted by ε -/
  counit : ∀ X : C, negatorObj X ⊗ X ≅ 𝟙_ C
  /-- The unit isomorphism, usually denoted by η -/
  unit : ∀ X : C, 𝟙_ C ≅ X ⊗ negatorObj X

namespace CategoricalGroup

export CategoricalGroupStruct (negatorObj counit unit)

end CategoricalGroup


namespace CategoricalGroup

/-- Notation for `negatorObj`, the negator on objects in a categorical group -/
scoped postfix:70 "′" => CategoricalGroup.negatorObj


/-- Notation for the `unit` : `𝟙 ≅ X ⊗ X'` -/
scoped notation "η_ " => CategoricalGroup.unit

/-- Notation for the `counit` : `X' ⊗ X ≅ 𝟙` -/
scoped notation "ε_ " => CategoricalGroup.counit


end CategoricalGroup


open CategoricalGroup

/-- A categorical group is a monoidal category equipped with a negator function `(-)′ : C → C`, and
cancellation natural isomorphisms
`η_ X : 𝟙 ≅ X ⊗ X'`
`ε_ X : X' ⊗ X ≅ 𝟙`,
and also satisfies the cancellation identities.
-/
class CategoricalGroup (C : Type u) [Groupoid.{v} C] [MonoidalCategory.{v} C]
extends CategoricalGroupStruct C where
  /--
  The zigzag identity relating the isomorphisms between
  `𝟙 ⊗ X` and `X ⊗ 𝟙`
  -/
  zigzag_1 :
    ∀ X : C,
      (η_ X).hom ▷ X ≫ (α_ X (X′) X).hom ≫
        X ◁ (ε_ X).hom = (λ_ X).hom ≫ (ρ_ X).inv  := by cat_disch

  /--
  The zigzag identity relating the isomorphisms between
  `X′ ⊗ 𝟙` and `𝟙 ⊗ X′`
  -/
  zigzag_2 :
    ∀ X : C,
      (X′) ◁ (η_ X).hom
      ≫ (α_ (X′) X (X′)).inv ≫ (ε_ X).hom ▷ (X′) =
      (ρ_ (X′)).hom  ≫
      (λ_ (X′)).inv := by cat_disch
=======


/-- A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class CategoricalGroup (C : Type u) [Groupoid.{v} C] [MonoidalCategory.{v} C] where
  /-- The negator functor -/
  negator : C ⥤  C
  /-- Left cancellation isomorphism, usually denoted by ε -/
  cancel_left : ∀ X : C, negator.obj X ⊗ X ≅ 𝟙_ C
  /-- Right cancellation isomorphism, usually denoted by η -/
  cancel_right : ∀ X : C, 𝟙_ C ≅ X ⊗ negator.obj X
  cancel_naturality_left :
    ∀  {X Y : C} (f : X ⟶ Y),
      (negator.map f) ▷ X ≫ (negator.obj Y) ◁ f ≫ (cancel_left Y).hom = (cancel_left X).hom  := by
    cat_disch
  cancel_naturality_right :
    ∀ {X Y : C} (f : X ⟶ Y),
      (X ◁ (negator.map f)) ≫ (f ▷ (negator.obj Y)) ≫ ((cancel_right Y).inv)
        = (cancel_right X).inv := by
    cat_disch
>>>>>>> 1382fcff18 (The definition is complete)

  cancellation_right :
    ∀ X : C,
      (λ_ X).inv ≫ (cancel_right X).hom ▷ X ≫ (α_ X (negator.obj X) X).hom ≫
        X ◁ (cancel_left X).hom ≫ (ρ_ X).hom = 𝟙 X  := by cat_disch

  cancellation_left :
    ∀ X : C,
      (ρ_ (negator.obj X)).inv ≫ (negator.obj X) ◁ (cancel_right X).hom
      ≫ (α_ (negator.obj X) X (negator.obj X)).inv ≫ (cancel_left X).hom ▷ (negator.obj X) ≫
      (λ_ (negator.obj X)).hom = 𝟙 (negator.obj X) := by cat_disch


<<<<<<< HEAD
attribute [reassoc (attr := simp)]
  CategoricalGroup.zigzag_1
attribute [reassoc (attr := simp)]
  CategoricalGroup.zigzag_2


namespace CategoricalGroup

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory.{v} C] [CategoricalGroup C]

=======

attribute [reassoc (attr := simp)]
  CategoricalGroup.cancellation_right
  CategoricalGroup.cancellation_left
-- attribute [reassoc] CategoricalGroup.cancellation_left CategoricalGroup.cancellation_right

open CategoricalGroup

@[inherit_doc]
notation "η_" => CategoricalGroup.cancel_right
notation "ε_" => CategoricalGroup.cancel_left

namespace CategoricalGroup

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory.{v} C] [CategoricalGroup.{v} C]
>>>>>>> 1382fcff18 (The definition is complete)

/-- The negator on morphisms -/
def negatorHom {X Y : C} (f : X ⟶ Y) : X′ ⟶ Y′ :=
  (ρ_ (X′)).inv ≫ (X′) ◁ (η_ Y).hom ≫ (α_ (X′) Y (Y′)).inv ≫ ((X′) ◁ (Groupoid.inv f)) ▷ (Y′) ≫
    (ε_ X).hom ▷ (Y′) ≫ (λ_ (Y′)).hom

end CategoricalGroup

end CategoryTheory

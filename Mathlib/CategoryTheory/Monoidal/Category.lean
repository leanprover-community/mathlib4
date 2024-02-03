/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Products.Basic

#align_import category_theory.monoidal.category from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensorObj : C → C → C`
* `tensorHom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`
and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `leftUnitor_nat_iso`, `rightUnitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files after proving the coherence theorem,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `CategoryTheory.Monoidal.CoherenceLemmas`.

## Implementation notes

In the definition of monoidal categories, we also provide the whiskering operators:
* `whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⊗ Y₁ ⟶ X ⊗ Y₂`, denoted by `X ◁ f`,
* `whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : X₁ ⊗ Y ⟶ X₂ ⊗ Y`, denoted by `f ▷ Y`.
These are products of an object and a morphism (the terminology "whiskering"
is borrowed from 2-category theory). The tensor product of morphisms `tensorHom` can be defined
in terms of the whiskerings. There are two possible such definitions, which are related by
the exchange property of the whiskerings. These two definitions are accessed by `tensorHom_def`
and `tensorHom_def'`. By default, `tensorHom` is defined so that `tensorHom_def` holds
definitionally.

If you want to provide `tensorHom` and define `whiskerLeft` and `whiskerRight` in terms of it,
you can use the alternative constructor `CategoryTheory.MonoidalCategory.ofTensorHom`.

The whiskerings are useful when considering simp-normal forms of morphisms in monoidal categories.

### Simp-normal form for morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any morphisms into the simp-normal
form defined below. Rewriting into simp-normal form is especially useful in preprocessing
performed by the `coherence` tactic.

The simp-normal form of morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of morphisms like `f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅` such that each `fᵢ` is
  either a structural morphisms (morphisms made up only of identities, associators, unitors)
  or non-structural morphisms, and
2. each non-structural morphism in the composition is of the form `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅`,
  where each `Xᵢ` is a object that is not the identity or a tensor and `f` is a non-structural
  morphisms that is not the identity or a composite.

Note that `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅` is actually `X₁ ◁ (X₂ ◁ (X₃ ◁ ((f ▷ X₄) ▷ X₅)))`.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/

universe v u

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`MonoidalCategory`. -/
class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C → C → C
  /-- left whiskering for morphisms -/
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  /-- right whiskering for morphisms -/
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
  /-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  /-- The tensor unity in the monoidal structure `𝟙_ C` -/
  tensorUnit : C
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X

namespace MonoidalCategory

export MonoidalCategoryStruct
  (tensorObj whiskerLeft whiskerRight tensorHom tensorUnit associator leftUnitor rightUnitor)

end MonoidalCategory

namespace MonoidalCategory

/-- Notation for `tensorObj`, the tensor product of objects in a monoidal category -/
scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorObj

/-- Notation for the `whiskerLeft` operator of monoidal categories -/
scoped infixr:81 " ◁ " => MonoidalCategoryStruct.whiskerLeft

/-- Notation for the `whiskerRight` operator of monoidal categories -/
scoped infixl:81 " ▷ " => MonoidalCategoryStruct.whiskerRight

/-- Notation for `tensorHom`, the tensor product of morphisms in a monoidal category -/
scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorHom

/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
scoped notation "𝟙_ " C:max => (MonoidalCategoryStruct.tensorUnit : C)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Used to ensure that `𝟙_` notation is used, as the ascription makes this not automatic. -/
@[delab app.CategoryTheory.MonoidalCategoryStruct.tensorUnit]
def delabTensorUnit : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``MonoidalCategoryStruct.tensorUnit 3
  let C ← withNaryArg 0 delab
  `(𝟙_ $C)

/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z) ≃ X ⊗ (Y ⊗ Z)` -/
scoped notation "α_" => MonoidalCategoryStruct.associator

/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
scoped notation "λ_" => MonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

end MonoidalCategory

open MonoidalCategory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See <https://stacks.math.columbia.edu/tag/0FFK>.
-/
-- Porting note: The Mathport did not translate the temporary notation
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      aesop_cat
  whiskerLeft_id : ∀ (X Y : C), whiskerLeft X (𝟙 Y) = 𝟙 (tensorObj X Y) := by
    aesop_cat
  whiskerLeft_comp :
    ∀ (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      whiskerLeft W (f ≫ g) = whiskerLeft W f ≫ whiskerLeft W g := by
    aesop_cat
  id_whiskerLeft :
    ∀ {X Y : C} (f : X ⟶ Y),
      whiskerLeft tensorUnit f = (leftUnitor X).hom ≫ f ≫ (leftUnitor Y).inv := by
    aesop_cat
  tensor_whiskerLeft :
    ∀ (X Y : C) {Z Z' : C} (f : Z ⟶ Z'),
      whiskerLeft (tensorObj X Y) f =
        (associator X Y Z).hom ≫ whiskerLeft X (whiskerLeft Y f) ≫ (associator X Y Z').inv := by
    aesop_cat
  id_whiskerRight : ∀ (X Y : C), whiskerRight (𝟙 X) Y = 𝟙 (tensorObj X Y) := by
    aesop_cat
  comp_whiskerRight :
    ∀ {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C),
      whiskerRight (f ≫ g) Z = whiskerRight f Z ≫ whiskerRight g Z := by
    aesop_cat
  whiskerRight_id :
    ∀ {X Y : C} (f : X ⟶ Y),
      whiskerRight f tensorUnit = (rightUnitor X).hom ≫ f ≫ (rightUnitor Y).inv := by
    aesop_cat
  whiskerRight_tensor :
    ∀ {X X' : C} (f : X ⟶ X') (Y Z : C),
      whiskerRight f (tensorObj Y Z) =
        (associator X Y Z).inv ≫ whiskerRight (whiskerRight f Y) Z ≫ (associator X' Y Z).hom := by
    aesop_cat
  whisker_assoc :
    ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C),
      whiskerRight (whiskerLeft X f) Z =
        (associator X Y Z).hom ≫ whiskerLeft X (whiskerRight f Z) ≫ (associator X Y' Z).inv := by
    aesop_cat
  /-- The exchange identity for the left and right whiskerings -/
  whisker_exchange :
    ∀ {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z),
      whiskerLeft W g ≫ whiskerRight f Z = whiskerRight f Y ≫ whiskerLeft X g := by
    aesop_cat
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      ((α_ W X Y).hom ▷ Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (W ◁ (α_ X Y Z).hom) =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    aesop_cat
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ (X ◁ (λ_ Y).hom) = ((ρ_ X).hom ▷ Y) := by
    aesop_cat
#align category_theory.monoidal_category CategoryTheory.MonoidalCategory

attribute [reassoc (attr := simp)] MonoidalCategory.pentagon
attribute [reassoc (attr := simp)] MonoidalCategory.triangle

namespace MonoidalCategory

attribute [reassoc]
  whiskerLeft_comp id_whiskerLeft tensor_whiskerLeft comp_whiskerRight whiskerRight_id
  whiskerRight_tensor whisker_assoc whisker_exchange tensorHom_def

attribute [simp]
  whiskerLeft_id whiskerRight_id
  whiskerLeft_comp id_whiskerLeft tensor_whiskerLeft comp_whiskerRight id_whiskerRight
  whiskerRight_tensor whisker_assoc

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C]

@[reassoc]
theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ :=
  whisker_exchange f g ▸ tensorHom_def f g

/-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
theorem tensor_id (X₁ X₂ : C) : (𝟙 X₁) ⊗ (𝟙 X₂) = 𝟙 (X₁ ⊗ X₂) := by
  simp [tensorHom_def]

/--
Composition of tensor products is tensor product of compositions:
`(f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)`
-/
@[reassoc, simp]
theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
      (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
  simp [tensorHom_def, whisker_exchange_assoc]

@[simp]
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    (𝟙 X) ⊗ f = X ◁ f := by
  simp [tensorHom_def]

@[simp]
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⊗ (𝟙 Y) = f ▷ Y := by
  simp [tensorHom_def]

end MonoidalCategory

open scoped MonoidalCategory
open MonoidalCategory

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C]

namespace MonoidalCategory

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.hom ≫ X ◁ f.inv = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.hom ▷ Z ≫ f.inv ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ f ≫ X ◁ inv f = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, IsIso.hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    f ▷ Z ≫ inv f ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ inv f ≫ X ◁ f = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    inv f ▷ Z ≫ f ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight]

/-- The left whiskering of an isomorphism is an isomorphism. -/
@[simps]
def whiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X ⊗ Y ≅ X ⊗ Z where
  hom := X ◁ f.hom
  inv := X ◁ f.inv

instance whiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ f) :=
  IsIso.of_iso (whiskerLeftIso X (asIso f))

@[simp]
theorem inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ f) = X ◁ inv f := by
  aesop_cat

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[simps!]
def whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X ⊗ Z ≅ Y ⊗ Z where
  hom := f.hom ▷ Z
  inv := f.inv ▷ Z

instance whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z) :=
  IsIso.of_iso (whiskerRightIso (asIso f) Z)

@[simp]
theorem inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ Z) = inv f ▷ Z := by
  aesop_cat

end MonoidalCategory

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {C : Type u} {X Y X' Y' : C} [Category.{v} C] [MonoidalCategory.{v} C] (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⊗ g.inv
  hom_inv_id := by rw [← tensor_comp, Iso.hom_inv_id, Iso.hom_inv_id, ← tensor_id]
  inv_hom_id := by rw [← tensor_comp, Iso.inv_hom_id, Iso.inv_hom_id, ← tensor_id]
#align category_theory.tensor_iso CategoryTheory.tensorIso

/-- Notation for `tensorIso`, the tensor product of isomorphisms -/
infixr:70 " ⊗ " => tensorIso

namespace MonoidalCategory

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ g) :=
  IsIso.of_iso (asIso f ⊗ asIso g)
#align category_theory.monoidal_category.tensor_is_iso CategoryTheory.MonoidalCategory.tensor_isIso

@[simp]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ g) = inv f ⊗ inv g := by
  simp [tensorHom_def ,whisker_exchange]
#align category_theory.monoidal_category.inv_tensor CategoryTheory.MonoidalCategory.inv_tensor

variable {U V W X Y Z : C}

theorem whiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P → (Y ⟶ Z)) (f' : ¬P → (Y ⟶ Z)) :
      X ◁ (if h : P then f h else f' h) = if h : P then X ◁ f h else X ◁ f' h := by
  split_ifs <;> rfl

theorem dite_whiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (Z : C):
      (if h : P then f h else f' h) ▷ Z = if h : P then f h ▷ Z else f' h ▷ Z := by
  split_ifs <;> rfl

theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ if h : P then g h else g' h) = if h : P then f ⊗ g h else f ⊗ g' h :=
  by split_ifs <;> rfl
#align category_theory.monoidal_category.tensor_dite CategoryTheory.MonoidalCategory.tensor_dite

theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ f = if h : P then g h ⊗ f else g' h ⊗ f :=
  by split_ifs <;> rfl
#align category_theory.monoidal_category.dite_tensor CategoryTheory.MonoidalCategory.dite_tensor

@[simp]
theorem whiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) :
    X ◁ eqToHom f = eqToHom (congr_arg₂ tensorObj rfl f) := by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]
theorem eqToHom_whiskerRight {X Y : C} (f : X = Y) (Z : C) :
    eqToHom f ▷ Z = eqToHom (congr_arg₂ tensorObj f rfl) := by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc]
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by simp

@[reassoc]
theorem associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z := by simp

@[reassoc]
theorem whiskerRight_tensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv := by simp

@[reassoc]
theorem associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z := by simp

@[reassoc]
theorem associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z := by simp

@[reassoc]
theorem whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom := by simp

@[reassoc]
theorem associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f := by simp

@[reassoc]
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f := by simp

@[reassoc]
theorem tensor_whiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom := by simp

@[reassoc]
theorem leftUnitor_naturality {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f :=
  by simp

@[reassoc]
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv = (λ_ X).inv ≫ (_ ◁ f) := by simp

@[reassoc]
theorem id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (λ_ X).inv ≫ 𝟙_ C ◁ f ≫ (λ_ X').hom := by
  simp

@[reassoc]
theorem rightUnitor_naturality {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  simp

@[reassoc]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ▷ _) := by simp

@[reassoc]
theorem whiskerRight_id_symm {X Y : C} (f : X ⟶ Y) :
    f = (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom := by
  simp

theorem whiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g := by simp

theorem whiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g := by simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/

section

@[reassoc (attr := simp)]
theorem pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc]
theorem pentagon_inv' (W X Y Z : C) :
    (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  CategoryTheory.eq_of_inv_eq_inv (by simp [pentagon])
#align category_theory.monoidal_category.pentagon_inv CategoryTheory.MonoidalCategory.pentagon_inv'

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_hom_inv :
    (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom =
      W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv := by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv), ← cancel_mono (α_ (W ⊗ X) Y Z).inv]
  simp

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_inv :
    (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom =
      (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_inv :
    W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv =
      (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z :=
  by simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_hom_hom :
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv =
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_hom :
    (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv =
      (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z := by
  rw [← cancel_epi (α_ W X (Y ⊗ Z)).inv, ← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_inv_hom :
    (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv =
      (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_hom :
    (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom =
      (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom :=
  by simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_inv_inv :
    (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z =
      W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom := by
  rw [← triangle, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right_inv (X Y : C) :
    (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y).hom = X ◁ (λ_ Y).inv := by
  simp [← cancel_mono (X ◁ (λ_ Y).hom)]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (X ◁ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight X Y : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`.
-/
@[reassoc, simp]
theorem leftUnitor_whiskerRight (X Y : C) :
    (λ_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, ← cancel_epi (α_ _ _ _).hom, ←
      cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_whiskerRight_assoc, triangle, associator_naturality_left]

@[reassoc, simp]
theorem leftUnitor_inv_whiskerRight (X Y : C) :
    (λ_ X).inv ▷ Y = (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ C) X Y).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
theorem whiskerLeft_rightUnitor (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X ⊗ Y)).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv, ←
      cancel_epi (X ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, triangle_assoc_comp_right,
      associator_inv_naturality_right]

@[reassoc, simp]
theorem whiskerLeft_rightUnitor_inv (X Y : C) :
    X ◁ (ρ_ Y).inv = (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc]
theorem leftUnitor_tensor (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y := by simp

@[reassoc]
theorem leftUnitor_tensor_inv (X Y : C) :
    (λ_ (X ⊗ Y)).inv = (λ_ X).inv ▷ Y ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc]
theorem rightUnitor_tensor (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by simp

@[reassoc]
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = X ◁ (ρ_ Y).inv ≫ (α_ X Y (𝟙_ C)).inv := by simp

end

@[reassoc]
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
      ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃)) := by
  simp [tensorHom_def]

@[reassoc]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) := by
  simp [tensorHom_def]
#align category_theory.monoidal_category.associator_inv_naturality CategoryTheory.MonoidalCategory.associator_inv_naturality

@[reassoc, simp]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g) ⊗ h = (α_ X Y Z).hom ≫ (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]
#align category_theory.monoidal_category.associator_conjugation CategoryTheory.MonoidalCategory.associator_conjugation

@[reassoc]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ g ⊗ h = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) ≫ (α_ X' Y' Z').hom := by
  rw [associator_naturality, inv_hom_id_assoc]
#align category_theory.monoidal_category.associator_inv_conjugation CategoryTheory.MonoidalCategory.associator_inv_conjugation

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⊗ g) ≫ (f.inv ⊗ h) = (V ◁ g) ≫ (V ◁ h) := by
  rw [← tensor_comp, f.hom_inv_id, id_tensorHom, whiskerLeft_comp]
#align category_theory.monoidal_category.hom_inv_id_tensor CategoryTheory.MonoidalCategory.hom_inv_id_tensor

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.hom ⊗ h) = (W ◁ g) ≫ (W ◁ h) := by
  rw [← tensor_comp, f.inv_hom_id, id_tensorHom, whiskerLeft_comp]
#align category_theory.monoidal_category.inv_hom_id_tensor CategoryTheory.MonoidalCategory.inv_hom_id_tensor

@[reassoc (attr := simp)]
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.hom) ≫ (h ⊗ f.inv) = (g ▷ V) ≫ (h ▷ V) := by
  rw [← tensor_comp, f.hom_inv_id, tensorHom_id, comp_whiskerRight]
#align category_theory.monoidal_category.tensor_hom_inv_id CategoryTheory.MonoidalCategory.tensor_hom_inv_id

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.hom) = (g ▷ W) ≫ (h ▷ W) := by
  rw [← tensor_comp, f.inv_hom_id, tensorHom_id, comp_whiskerRight]
#align category_theory.monoidal_category.tensor_inv_hom_id CategoryTheory.MonoidalCategory.tensor_inv_hom_id

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ g) ≫ (inv f ⊗ h) = (V ◁ g) ≫ (V ◁ h) := by
  rw [← tensor_comp, IsIso.hom_inv_id, id_tensorHom, whiskerLeft_comp]
#align category_theory.monoidal_category.hom_inv_id_tensor' CategoryTheory.MonoidalCategory.hom_inv_id_tensor'

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ g) ≫ (f ⊗ h) = (W ◁ g) ≫ (W ◁ h) := by
  rw [← tensor_comp, IsIso.inv_hom_id, id_tensorHom, whiskerLeft_comp]
#align category_theory.monoidal_category.inv_hom_id_tensor' CategoryTheory.MonoidalCategory.inv_hom_id_tensor'

@[reassoc (attr := simp)]
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f) ≫ (h ⊗ inv f) = (g ▷ V) ≫ (h ▷ V) := by
  rw [← tensor_comp, IsIso.hom_inv_id, tensorHom_id, comp_whiskerRight]
#align category_theory.monoidal_category.tensor_hom_inv_id' CategoryTheory.MonoidalCategory.tensor_hom_inv_id'

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ inv f) ≫ (h ⊗ f) = (g ▷ W) ≫ (h ▷ W) := by
  rw [← tensor_comp, IsIso.inv_hom_id, tensorHom_id, comp_whiskerRight]
#align category_theory.monoidal_category.tensor_inv_hom_id' CategoryTheory.MonoidalCategory.tensor_inv_hom_id'

/--
A constructor for monoidal categories that requires `tensorHom` instead of `whiskerLeft` and
`whiskerRight`.
-/
abbrev ofTensorHom [MonoidalCategoryStruct C]
    (tensor_id : ∀ X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
      aesop_cat)
    (id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), tensorHom (𝟙 X) f = whiskerLeft X f := by
      aesop_cat)
    (tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), tensorHom f (𝟙 Y) = whiskerRight f Y := by
      aesop_cat)
    (tensor_comp :
      ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
          aesop_cat)
    (associator_naturality :
      ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
            aesop_cat)
    (leftUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom (𝟙 tensorUnit) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
          aesop_cat)
    (rightUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom f (𝟙 tensorUnit) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
          aesop_cat)
    (pentagon :
      ∀ W X Y Z : C,
        tensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
            aesop_cat)
    (triangle :
      ∀ X Y : C,
        (associator X tensorUnit Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
          tensorHom (rightUnitor X).hom (𝟙 Y) := by
            aesop_cat) :
      MonoidalCategory C where
  tensorHom_def := by intros; simp [← id_tensorHom, ← tensorHom_id, ← tensor_comp]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← tensor_id]
  whiskerLeft_comp := by intros; simp [← id_tensorHom, ← tensor_comp]
  id_whiskerLeft := by intros; rw [← assoc, ← leftUnitor_naturality]; simp [← id_tensorHom]
  tensor_whiskerLeft := by
    intros
    simp only [← id_tensorHom, ← tensorHom_id]
    rw [← assoc, ← associator_naturality]
    simp [tensor_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, tensor_id]
  comp_whiskerRight := by intros; simp [← tensorHom_id, ← tensor_comp]
  whiskerRight_id := by intros; rw [← assoc, ← rightUnitor_naturality]; simp [← tensorHom_id]
  whiskerRight_tensor := by
    intros
    simp only [← id_tensorHom, ← tensorHom_id]
    rw [associator_naturality]
    simp [tensor_id]
  whisker_assoc := by
    intros
    simp only [← id_tensorHom, ← tensorHom_id]
    rw [← assoc, ← associator_naturality]
    simp
  whisker_exchange := by simp [← id_tensorHom, ← tensorHom_id, ← tensor_comp]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]
  triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle]

section

/- The lemmas of this section might be redundant because they should be stated in terms of the
whiskering operators. We leave them in order not to break proofs that existed before we
have the whiskering operators. -/

@[reassoc]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) := by
  simp
#align category_theory.monoidal_category.comp_tensor_id CategoryTheory.MonoidalCategory.comp_tensor_id

@[reassoc]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) := by
  simp
#align category_theory.monoidal_category.id_tensor_comp CategoryTheory.MonoidalCategory.id_tensor_comp

@[reassoc]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f := by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.id_tensor_comp_tensor_id CategoryTheory.MonoidalCategory.id_tensor_comp_tensor_id

@[reassoc]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f := by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.tensor_id_comp_id_tensor CategoryTheory.MonoidalCategory.tensor_id_comp_id_tensor

theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by simp
#align category_theory.monoidal_category.tensor_left_iff CategoryTheory.MonoidalCategory.tensor_left_iff

theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by simp
#align category_theory.monoidal_category.tensor_right_iff CategoryTheory.MonoidalCategory.tensor_right_iff

@[reassoc]
theorem triangle' (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ (𝟙 X ⊗ (λ_ Y).hom) = (ρ_ X).hom ⊗ 𝟙 Y := by
  simp
#align category_theory.monoidal_category.triangle CategoryTheory.MonoidalCategory.triangle'

@[reassoc]
theorem pentagon' (W X Y Z : C) :
    ((α_ W X Y).hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (𝟙 W ⊗ (α_ X Y Z).hom) =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  simp
#align category_theory.monoidal_category.pentagon CategoryTheory.MonoidalCategory.pentagon'

@[reassoc]
theorem rightUnitor_tensor' (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ (𝟙 X ⊗ (ρ_ Y).hom) := by
  simp
#align category_theory.monoidal_category.right_unitor_tensor CategoryTheory.MonoidalCategory.rightUnitor_tensor'

@[reassoc]
theorem rightUnitor_tensor_inv' (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = (𝟙 X ⊗ (ρ_ Y).inv) ≫ (α_ X Y (𝟙_ C)).inv :=
  eq_of_inv_eq_inv (by simp)
#align category_theory.monoidal_category.right_unitor_tensor_inv CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv'

@[reassoc]
theorem triangle_assoc_comp_right' (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ⊗ 𝟙 Y) = 𝟙 X ⊗ (λ_ Y).hom := by
  simp
#align category_theory.monoidal_category.triangle_assoc_comp_right CategoryTheory.MonoidalCategory.triangle_assoc_comp_right'

@[reassoc]
theorem triangle_assoc_comp_left_inv' (X Y : C) :
    (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y := by
  simp
#align category_theory.monoidal_category.triangle_assoc_comp_left_inv CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv'

theorem rightUnitor_conjugation {X Y : C} (f : X ⟶ Y) :
    f ⊗ 𝟙 (𝟙_ C) = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  simp
#align category_theory.monoidal_category.right_unitor_conjugation CategoryTheory.MonoidalCategory.rightUnitor_conjugation

theorem leftUnitor_conjugation {X Y : C} (f : X ⟶ Y) :
    𝟙 (𝟙_ C) ⊗ f = (λ_ X).hom ≫ f ≫ (λ_ Y).inv := by
  simp
#align category_theory.monoidal_category.left_unitor_conjugation CategoryTheory.MonoidalCategory.leftUnitor_conjugation

@[reassoc]
theorem leftUnitor_naturality' {X Y : C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ C) ⊗ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f :=
  by simp

@[reassoc]
theorem rightUnitor_naturality' {X Y : C} (f : X ⟶ Y) :
    (f ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  simp

@[reassoc]
theorem leftUnitor_inv_naturality' {X X' : C} (f : X ⟶ X') :
    f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) := by
  simp
#align category_theory.monoidal_category.left_unitor_inv_naturality CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality'

@[reassoc]
theorem rightUnitor_inv_naturality' {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) := by
  simp
#align category_theory.monoidal_category.right_unitor_inv_naturality CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality'

end

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

attribute [local simp] tensorHom_def

/-- The tensor product expressed as a functor. -/
@[simps]
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ f.2
  map_comp := by
    intro X Y Z f g
    simp [whisker_exchange_assoc]
#align category_theory.monoidal_category.tensor CategoryTheory.MonoidalCategory.tensor

/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C
    where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ f.2.1) ⊗ f.2.2
  map_comp := by
    intro X Y Z f g
    simp [-tensorHom_def, tensor_comp]

#align category_theory.monoidal_category.left_assoc_tensor CategoryTheory.MonoidalCategory.leftAssocTensor

@[simp]
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl
#align category_theory.monoidal_category.left_assoc_tensor_obj CategoryTheory.MonoidalCategory.leftAssocTensor_obj

@[simp]
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 :=
  rfl
#align category_theory.monoidal_category.left_assoc_tensor_map CategoryTheory.MonoidalCategory.leftAssocTensor_map

/-- The right-associated triple tensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C
    where
  obj X := X.1 ⊗ X.2.1 ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⊗ f.2.1 ⊗ f.2.2
  map_comp := by
    intro X Y Z f g
    simp [-tensorHom_def, tensor_comp]
#align category_theory.monoidal_category.right_assoc_tensor CategoryTheory.MonoidalCategory.rightAssocTensor

@[simp]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl
#align category_theory.monoidal_category.right_assoc_tensor_obj CategoryTheory.MonoidalCategory.rightAssocTensor_obj

@[simp]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl
#align category_theory.monoidal_category.right_assoc_tensor_map CategoryTheory.MonoidalCategory.rightAssocTensor_map

/-- The functor `fun X ↦ 𝟙_ C ⊗ X`. -/
def tensorUnitLeft : C ⥤ C where
  obj X := 𝟙_ C ⊗ X
  map {X Y : C} (f : X ⟶ Y) := 𝟙_ C ◁ f
#align category_theory.monoidal_category.tensor_unit_left CategoryTheory.MonoidalCategory.tensorUnitLeft

/-- The functor `fun X ↦ X ⊗ 𝟙_ C`. -/
def tensorUnitRight : C ⥤ C where
  obj X := X ⊗ 𝟙_ C
  map {X Y : C} (f : X ⟶ Y) := f ▷ 𝟙_ C
#align category_theory.monoidal_category.tensor_unit_right CategoryTheory.MonoidalCategory.tensorUnitRight

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
-- Porting Note: Had to add a `simps!` because Lean was complaining this wasn't a constructor app.
/-- The associator as a natural isomorphism. -/
@[simps!]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents
    (by
      intros
      apply MonoidalCategory.associator)
    (by
      intros
      apply MonoidalCategory.associator_naturality)
#align category_theory.monoidal_category.associator_nat_iso CategoryTheory.MonoidalCategory.associatorNatIso

-- Porting Note: same as above
/-- The left unitor as a natural isomorphism. -/
@[simps!]
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents
    (by
      intros
      apply MonoidalCategory.leftUnitor)
    (by
      intros
      apply MonoidalCategory.leftUnitor_naturality)
#align category_theory.monoidal_category.left_unitor_nat_iso CategoryTheory.MonoidalCategory.leftUnitorNatIso

-- Porting Note: same as above
/-- The right unitor as a natural isomorphism. -/
@[simps!]
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents
    (by
      intros
      apply MonoidalCategory.rightUnitor)
    (by
      intros
      apply MonoidalCategory.rightUnitor_naturality)
#align category_theory.monoidal_category.right_unitor_nat_iso CategoryTheory.MonoidalCategory.rightUnitorNatIso

section

-- Porting Note: This used to be `variable {C}` but it seems like Lean 4 parses that differently
variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps]
def tensorLeft (X : C) : C ⥤ C where
  obj Y := X ⊗ Y
  map {Y} {Y'} f := X ◁ f
#align category_theory.monoidal_category.tensor_left CategoryTheory.MonoidalCategory.tensorLeft

/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp
#align category_theory.monoidal_category.tensor_left_tensor CategoryTheory.MonoidalCategory.tensorLeftTensor

@[simp]
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl
#align category_theory.monoidal_category.tensor_left_tensor_hom_app CategoryTheory.MonoidalCategory.tensorLeftTensor_hom_app

@[simp]
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensorLeftTensor]
#align category_theory.monoidal_category.tensor_left_tensor_inv_app CategoryTheory.MonoidalCategory.tensorLeftTensor_inv_app

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps]
def tensorRight (X : C) : C ⥤ C where
  obj Y := Y ⊗ X
  map {Y} {Y'} f := f ▷ X
#align category_theory.monoidal_category.tensor_right CategoryTheory.MonoidalCategory.tensorRight

-- Porting Note: This used to be `variable (C)` but it seems like Lean 4 parses that differently
variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
@[simps]
def tensoringLeft : C ⥤ C ⥤ C where
  obj := tensorLeft
  map {X} {Y} f := {
    app := fun Z => f ▷ Z
    naturality := by
      intros
      simp [whisker_exchange] }
#align category_theory.monoidal_category.tensoring_left CategoryTheory.MonoidalCategory.tensoringLeft

instance : Faithful (tensoringLeft C) where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
@[simps]
def tensoringRight : C ⥤ C ⥤ C where
  obj := tensorRight
  map {X} {Y} f := {
    app := fun Z => Z ◁ f
    naturality := by
      intros
      simp [whisker_exchange] }
#align category_theory.monoidal_category.tensoring_right CategoryTheory.MonoidalCategory.tensoringRight

instance : Faithful (tensoringRight C) where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

-- Porting Note: This used to be `variable {C}` but it seems like Lean 4 parses that differently
variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp
#align category_theory.monoidal_category.tensor_right_tensor CategoryTheory.MonoidalCategory.tensorRightTensor

@[simp]
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl
#align category_theory.monoidal_category.tensor_right_tensor_hom_app CategoryTheory.MonoidalCategory.tensorRightTensor_hom_app

@[simp]
theorem tensorRightTensor_inv_app (X Y Z : C) :
    (tensorRightTensor X Y).inv.app Z = (associator Z X Y).hom := by simp [tensorRightTensor]
#align category_theory.monoidal_category.tensor_right_tensor_inv_app CategoryTheory.MonoidalCategory.tensorRightTensor_inv_app

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]

variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon
attribute [local simp] tensorHom_def

@[simps! tensorObj tensorUnit whiskerLeft whiskerRight associator]
instance prodMonoidal : MonoidalCategory (C₁ × C₂) where
  tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom f g := (f.1 ⊗ g.1, f.2 ⊗ g.2)
  whiskerLeft X _ _ f := (whiskerLeft X.1 f.1, whiskerLeft X.2 f.2)
  whiskerRight f X := (whiskerRight f.1 X.1, whiskerRight f.2 X.2)
  whisker_exchange := by simp [whisker_exchange]
  tensorHom_def := by simp [tensorHom_def]
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)
#align category_theory.monoidal_category.prod_monoidal CategoryTheory.MonoidalCategory.prodMonoidal

@[simp]
theorem prodMonoidal_tensorHom {X₁ Y₁ X₂ Y₂ : C₁ × C₂} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = (f.1 ⊗ g.1, f.2 ⊗ g.2) :=
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_hom_fst (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).1 = (λ_ X.1).hom := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_hom_fst CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_fst

@[simp]
theorem prodMonoidal_leftUnitor_hom_snd (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).2 = (λ_ X.2).hom := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_hom_snd CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_snd

@[simp]
theorem prodMonoidal_leftUnitor_inv_fst (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).1 = (λ_ X.1).inv := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_inv_fst CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_fst

@[simp]
theorem prodMonoidal_leftUnitor_inv_snd (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).2 = (λ_ X.2).inv := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_inv_snd CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_snd

@[simp]
theorem prodMonoidal_rightUnitor_hom_fst (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).1 = (ρ_ X.1).hom := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_hom_fst CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_fst

@[simp]
theorem prodMonoidal_rightUnitor_hom_snd (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).2 = (ρ_ X.2).hom := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_hom_snd CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_snd

@[simp]
theorem prodMonoidal_rightUnitor_inv_fst (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).1 = (ρ_ X.1).inv := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_inv_fst CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_fst

@[simp]
theorem prodMonoidal_rightUnitor_inv_snd (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).2 = (ρ_ X.2).inv := by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_inv_snd CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_snd

end

end MonoidalCategory

end CategoryTheory

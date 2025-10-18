/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.ToAdditive

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
  either a structural morphism (morphisms made up only of identities, associators, unitors)
  or a non-structural morphism, and
2. each non-structural morphism in the composition is of the form `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅`,
  where each `Xᵢ` is an object that is not the identity or a tensor and `f` is a non-structural
  morphism that is not the identity or a composite.

Note that `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅` is actually `X₁ ◁ (X₂ ◁ (X₃ ◁ ((f ▷ X₄) ▷ X₅)))`.

Currently, the simp lemmas don't rewrite `𝟙 X ⊗ₘ f` and `f ⊗ₘ 𝟙 Y` into `X ◁ f` and `f ▷ Y`,
respectively, since it requires a huge refactoring. We hope to add these simp lemmas soon.

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
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  /-- The tensor unity in the monoidal structure `𝟙_ C` -/
  tensorUnit (C) : C
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X

/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`AddMonoidalCategory`. -/
class AddMonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried sum of objects -/
  addObj : C → C → C
  /-- left whiskering for morphisms -/
  addWhiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : addObj X Y₁ ⟶ addObj X Y₂
  /-- right whiskering for morphisms -/
  addWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : addObj X₁ Y ⟶ addObj X₂ Y
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊕ₘ 𝟙 X₂ = 𝟙 (X₁ ⊕ₒ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  addHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (addObj X₁ X₂ ⟶ addObj Y₁ Y₂) :=
    addWhiskerRight f X₂ ≫ addWhiskerLeft Y₁ g
  /-- The zero object in the additive monoidal structure `𝟘_ C` -/
  addUnit (C) : C
  /-- The associator isomorphism `(X ⊕ₒ Y) ⊕ₒ Z ≃ X ⊕ₒ (Y ⊕ₒ Z)` -/
  addAssociator : ∀ X Y Z : C, addObj (addObj X Y) Z ≅ addObj X (addObj Y Z)
  /-- The left unitor: `𝟘_ C ⊕ₒ X ≃ X` -/
  leftAddUnitor : ∀ X : C, addObj addUnit X ≅ X
  /-- The right unitor: `X ⊕ₒ 𝟘_ C ≃ X` -/
  rightAddUnitor : ∀ X : C, addObj X addUnit ≅ X

attribute [to_additive] MonoidalCategoryStruct

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
scoped infixr:70 " ⊗ₘ " => MonoidalCategoryStruct.tensorHom
-- TODO: Try setting this notation to `⊗` if the elaborator is improved and performs
-- better than currently on overloaded notations.

/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
scoped notation "𝟙_ " C:arg => MonoidalCategoryStruct.tensorUnit C

/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
scoped notation "α_" => MonoidalCategoryStruct.associator

/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
scoped notation "λ_" => MonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

/-- The property that the pentagon relation is satisfied by four objects
in a category equipped with a `MonoidalCategoryStruct`. -/
@[to_additive AddMonoidalCategory.AddPentagon
/-- The property that the pentagon relation is satisfied by four objects
in a category equipped with an `AddMonoidalCategoryStruct`. -/]
def Pentagon {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ ⊗ Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ ⊗ Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ ⊗ Y₄)).hom

end MonoidalCategory

namespace AddMonoidalCategory

/-- Notation for `addObj`, the sum of objects in an additive monoidal category -/
scoped infixr:70 " ⊕ₒ " => AddMonoidalCategoryStruct.addObj

/-- Notation for the `addWhiskerLeft` operator of additive monoidal categories -/
scoped infixr:81 " ◁⁺ " => AddMonoidalCategoryStruct.addWhiskerLeft

/-- Notation for the `addWhiskerRight` operator of additive monoidal categories -/
scoped infixl:81 " ▷⁺ " => AddMonoidalCategoryStruct.addWhiskerRight

/-- Notation for `addHom`, the sum of morphisms in an additive monoidal category -/
scoped infixr:70 " ⊕ₘ " => AddMonoidalCategoryStruct.addHom

/-- Notation for `addUnit`, the two-sided identity of `⊕ₒ` -/
scoped notation "𝟘_ " C:arg => AddMonoidalCategoryStruct.addUnit C

/-- Notation for the additive monoidal `addAssociator`: `(X ⊕ₒ Y) ⊕ₒ Z ≃ X ⊕ₒ (Y ⊕ₒ Z)` -/
scoped notation "α⁺" => AddMonoidalCategoryStruct.addAssociator

/-- Notation for the `leftAddUnitor`: `𝟘_C ⊕ₒ X ≃ X` -/
scoped notation "λ⁺" => AddMonoidalCategoryStruct.leftAddUnitor

/-- Notation for the `rightAddUnitor`: `X ⊕ₒ 𝟘_C ≃ X` -/
scoped notation "ρ⁺" => AddMonoidalCategoryStruct.rightAddUnitor

end AddMonoidalCategory

open MonoidalCategory

open AddMonoidalCategory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms
`f ⊗ₘ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations. -/
@[stacks 0FFK]
-- Porting note: The Mathport did not translate the temporary notation
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      cat_disch
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/
  id_tensorHom_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by cat_disch
  /--
  Composition of tensor products is tensor product of compositions:
  `(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)`
  -/
  tensorHom_comp_tensorHom :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
    cat_disch
  whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
    cat_disch
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
    cat_disch
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ₘ f₂) ⊗ₘ f₃ ≃ f₁ ⊗ₘ (f₂ ⊗ₘ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
    cat_disch
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
    cat_disch
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
    cat_disch
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    cat_disch
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
    cat_disch

attribute [reassoc] MonoidalCategory.tensorHom_def
attribute [reassoc, simp] MonoidalCategory.whiskerLeft_id
attribute [reassoc, simp] MonoidalCategory.id_whiskerRight
attribute [reassoc (attr := simp)] MonoidalCategory.tensorHom_comp_tensorHom
attribute [reassoc] MonoidalCategory.associator_naturality
attribute [reassoc] MonoidalCategory.leftUnitor_naturality
attribute [reassoc] MonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] MonoidalCategory.pentagon
attribute [reassoc (attr := simp)] MonoidalCategory.triangle

/--
In an additive monoidal category, we can take the sum of objects, `X ⊕ₒ Y` and of morphisms
`f ⊕ₘ g`.
Addition does not need to be strictly associative on objects, but there is a
specified associator, `α⁺ X Y Z : (X ⊕ₒ Y) ⊕ₒ Z ≅ X ⊕ₒ (Y ⊕ₒ Z)`. There is a zero object `𝟘_ C`,
with specified left and right unitor isomorphisms `λ⁺ X : 𝟘_ C ⊕ₒ X ≅ X` and `ρ⁺ X : X ⊕ₒ 𝟘_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations. -/
class AddMonoidalCategory (C : Type u) [𝒞 : Category.{v} C]
    extends AddMonoidalCategoryStruct C where
  addHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊕ₘ g = (f ▷⁺ X₂) ≫ (Y₁ ◁⁺ g) := by
      cat_disch
  /-- Sum of identity maps is the identity: `𝟙 X₁ ⊕ₘ 𝟙 X₂ = 𝟙 (X₁ ⊕ₒ X₂)` -/
  id_addHom_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⊕ₘ 𝟙 X₂ = 𝟙 (X₁ ⊕ₒ X₂) := by cat_disch
  /--
  Composition of sums is sum of compositions:
  `(f₁ ⊕ₘ f₂) ≫ (g₁ ⊕ₘ g₂) = (f₁ ≫ g₁) ⊕ₘ (f₂ ≫ g₂)`
  -/
  addHom_comp_addHom :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⊕ₘ f₂) ≫ (g₁ ⊕ₘ g₂) = (f₁ ≫ g₁) ⊕ₘ (f₂ ≫ g₂) := by
    cat_disch
  addWhiskerLeft_id : ∀ (X Y : C), X ◁⁺ 𝟙 Y = 𝟙 (X ⊕ₒ Y) := by
    cat_disch
  id_addWhiskerRight : ∀ (X Y : C), 𝟙 X ▷⁺ Y = 𝟙 (X ⊕ₒ Y) := by
    cat_disch
  /-- Naturality of the associator isomorphism: `(f₁ ⊕ₘ f₂) ⊕ₘ f₃ ≃ f₁ ⊕ₘ (f₂ ⊕ₘ f₃)` -/
  addAssociator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊕ₘ f₂) ⊕ₘ f₃) ≫ (α⁺ Y₁ Y₂ Y₃).hom = (α⁺ X₁ X₂ X₃).hom ≫ (f₁ ⊕ₘ (f₂ ⊕ₘ f₃)) := by
    cat_disch
  /--
  Naturality of the left unitor, commutativity of `𝟘_ C ⊕ₒ X ⟶ 𝟘_ C ⊕ₒ Y ⟶ Y` and
  `𝟘_ C ⊕ₒ X ⟶ X ⟶ Y`
  -/
  leftAddUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟘_ _ ◁⁺ f ≫ (λ⁺ Y).hom = (λ⁺ X).hom ≫ f := by
    cat_disch
  /--
  Naturality of the right unitor: commutativity of `X ⊕ₒ 𝟘_ C ⟶ Y ⊕ₒ 𝟘_ C ⟶ Y` and
  `X ⊕ₒ 𝟘_ C ⟶ X ⟶ Y`
  -/
  rightAddUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷⁺ 𝟘_ _ ≫ (ρ⁺ Y).hom = (ρ⁺ X).hom ≫ f := by
    cat_disch
  /--
  The pentagon identity relating the isomorphism between `X ⊕ₒ (Y ⊕ₒ (Z ⊕ₒ W))` and
  `((X ⊕ₒ Y) ⊕ₒ Z) ⊕ₒ W`
  -/
  addPentagon :
    ∀ W X Y Z : C,
      (α⁺ W X Y).hom ▷⁺ Z ≫ (α⁺ W (X ⊕ₒ Y) Z).hom ≫ W ◁⁺ (α⁺ X Y Z).hom =
        (α⁺ (W ⊕ₒ X) Y Z).hom ≫ (α⁺ W X (Y ⊕ₒ Z)).hom := by
    cat_disch
  /--
  The identity relating the isomorphisms between `X ⊕ₒ (𝟘_ C ⊕ₒ Y)`, `(X ⊕ₒ 𝟘_ C) ⊕ₒ Y` and `X ⊕ₒ Y`
  -/
  addTriangle :
    ∀ X Y : C, (α⁺ X (𝟘_ _) Y).hom ≫ X ◁⁺ (λ⁺ Y).hom = (ρ⁺ X).hom ▷⁺ Y := by
    cat_disch

attribute [reassoc] AddMonoidalCategory.addHom_def
attribute [reassoc, simp] AddMonoidalCategory.addWhiskerLeft_id
attribute [reassoc, simp] AddMonoidalCategory.id_addWhiskerRight
attribute [reassoc (attr := simp)] AddMonoidalCategory.addHom_comp_addHom
attribute [reassoc] AddMonoidalCategory.addAssociator_naturality
attribute [reassoc] AddMonoidalCategory.leftAddUnitor_naturality
attribute [reassoc] AddMonoidalCategory.rightAddUnitor_naturality
attribute [reassoc (attr := simp)] AddMonoidalCategory.addPentagon
attribute [reassoc (attr := simp)] AddMonoidalCategory.addTriangle

attribute [to_additive] MonoidalCategory

-- NOTE: we disable this warning, which would otherwise fire since some of these are already marked
-- as `simp` lemmas.
set_option linter.existingAttributeWarning false in
attribute [to_additive existing]
  MonoidalCategory.whiskerLeft_id_assoc
  MonoidalCategory.id_whiskerRight_assoc
  MonoidalCategory.tensorHom_comp_tensorHom_assoc
  MonoidalCategory.associator_naturality_assoc
  MonoidalCategory.leftUnitor_naturality_assoc
  MonoidalCategory.rightUnitor_naturality_assoc

set_option linter.existingAttributeWarning false in
attribute [to_additive existing AddMonoidalCategory.addPentagon_assoc]
  MonoidalCategory.pentagon_assoc

set_option linter.existingAttributeWarning false in
attribute [to_additive existing AddMonoidalCategory.addTriangle_assoc]
  MonoidalCategory.triangle_assoc

namespace MonoidalCategory

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C]

@[to_additive (attr := simp)]
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ₘ f = X ◁ f := by
  simp [tensorHom_def]

@[to_additive (attr := simp)]
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⊗ₘ 𝟙 Y = f ▷ Y := by
  simp [tensorHom_def]

@[reassoc]
theorem whiskerLeft_comp (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g := by
  simp [← id_tensorHom]

@[reassoc]
theorem id_whiskerLeft {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f = (λ_ X).hom ≫ f ≫ (λ_ Y).inv := by
  rw [← assoc, ← leftUnitor_naturality]; simp

@[reassoc]
theorem tensor_whiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f ≫ (α_ X Y Z').inv := by
  simp only [← id_tensorHom]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc]
theorem comp_whiskerRight {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) :
    (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z := by
  simp [← tensorHom_id]

@[reassoc]
theorem whiskerRight_id {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← assoc, ← rightUnitor_naturality]; simp

@[reassoc]
theorem whiskerRight_tensor {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom := by
  simp only [← tensorHom_id]
  rw [associator_naturality]
  simp

@[reassoc]
theorem whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X Y' Z).inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

attribute [to_additive (attr := simp)]
  whiskerLeft_comp id_whiskerLeft tensor_whiskerLeft comp_whiskerRight whiskerRight_id
  whiskerRight_tensor whisker_assoc
attribute [to_additive]
  whiskerLeft_comp_assoc id_whiskerLeft_assoc tensor_whiskerLeft_assoc comp_whiskerRight_assoc
  whiskerRight_id_assoc whiskerRight_tensor_assoc whisker_assoc_assoc

@[reassoc (attr := to_additive)]
theorem whisker_exchange {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := to_additive)]
theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = X₁ ◁ g ≫ f ▷ Y₂ :=
  whisker_exchange f g ▸ tensorHom_def f g

@[reassoc (attr := to_additive)]
theorem whiskerLeft_comp_tensorHom {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (V ◁ g) ≫ (f ⊗ₘ h) = f ⊗ₘ (g ≫ h) := by
  simp [tensorHom_def']

@[reassoc (attr := to_additive)]
theorem whiskerRight_comp_tensorHom {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ▷ V) ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  simp [tensorHom_def]

@[reassoc (attr := to_additive)]
theorem tensorHom_comp_whiskerLeft {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ₘ g) ≫ (W ◁ h) = f ⊗ₘ (g ≫ h) := by
  simp [tensorHom_def]

@[reassoc (attr := to_additive)]
theorem tensorHom_comp_whiskerRight {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ⊗ₘ h) ≫ (g ▷ W) = (f ≫ g) ⊗ₘ h := by
  simp [tensorHom_def, whisker_exchange]

@[reassoc (attr := to_additive)]
lemma leftUnitor_inv_comp_tensorHom {X Y Z : C} (f : 𝟙_ C ⟶ Y) (g : X ⟶ Z) :
    (λ_ X).inv ≫ (f ⊗ₘ g) = g ≫ (λ_ Z).inv ≫ f ▷ Z := by simp [tensorHom_def']

@[reassoc (attr := to_additive)]
lemma rightUnitor_inv_comp_tensorHom {X Y Z : C} (f : X ⟶ Y) (g : 𝟙_ C ⟶ Z) :
    (ρ_ X).inv ≫ (f ⊗ₘ g) = f ≫ (ρ_ Y).inv ≫ Y ◁ g := by simp [tensorHom_def]

@[reassoc (attr := to_additive (attr := simp))]
theorem whiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.hom ≫ X ◁ f.inv = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := to_additive (attr := simp))]
theorem hom_inv_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.hom ▷ Z ≫ f.inv ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := to_additive (attr := simp))]
theorem whiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := to_additive (attr := simp))]
theorem inv_hom_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := to_additive (attr := simp))]
theorem whiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ f ≫ X ◁ inv f = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, IsIso.hom_inv_id, whiskerLeft_id]

@[reassoc (attr := to_additive (attr := simp))]
theorem hom_inv_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    f ▷ Z ≫ inv f ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight]

@[reassoc (attr := to_additive (attr := simp))]
theorem whiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ inv f ≫ X ◁ f = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id]

@[reassoc (attr := to_additive (attr := simp))]
theorem inv_hom_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    inv f ▷ Z ≫ f ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight]

/-- The left whiskering of an isomorphism is an isomorphism. -/
@[to_additive (attr := simps) /-- The left whiskering of an isomorphism is an isomorphism. -/]
def whiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X ⊗ Y ≅ X ⊗ Z where
  hom := X ◁ f.hom
  inv := X ◁ f.inv

@[to_additive]
instance whiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ f) :=
  (whiskerLeftIso X (asIso f)).isIso_hom

@[to_additive (attr := simp)]
theorem inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ f) = X ◁ inv f := by
  cat_disch

@[to_additive (attr := simp)]
lemma whiskerLeftIso_refl (W X : C) :
    whiskerLeftIso W (Iso.refl X) = Iso.refl (W ⊗ X) :=
  Iso.ext (whiskerLeft_id W X)

@[to_additive (attr := simp)]
lemma whiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
    whiskerLeftIso W (f ≪≫ g) = whiskerLeftIso W f ≪≫ whiskerLeftIso W g :=
  Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[to_additive (attr := simp)]
lemma whiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) :
    (whiskerLeftIso W f).symm = whiskerLeftIso W f.symm := rfl

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[to_additive (attr := simps!) /-- The right whiskering of an isomorphism is an isomorphism. -/]
def whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X ⊗ Z ≅ Y ⊗ Z where
  hom := f.hom ▷ Z
  inv := f.inv ▷ Z

@[to_additive]
instance whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z) :=
  (whiskerRightIso (asIso f) Z).isIso_hom

@[to_additive (attr := simp)]
theorem inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ Z) = inv f ▷ Z := by
  cat_disch

@[to_additive (attr := simp)]
lemma whiskerRightIso_refl (X W : C) :
    whiskerRightIso (Iso.refl X) W = Iso.refl (X ⊗ W) :=
  Iso.ext (id_whiskerRight X W)

@[to_additive (attr := simp)]
lemma whiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) :
    whiskerRightIso (f ≪≫ g) W = whiskerRightIso f W ≪≫ whiskerRightIso g W :=
  Iso.ext (comp_whiskerRight f.hom g.hom W)

@[to_additive (attr := simp)]
lemma whiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) :
    (whiskerRightIso f W).symm = whiskerRightIso f.symm W := rfl

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[to_additive (attr := simps) /-- The tensor product of two isomorphisms is an isomorphism. -/]
def tensorIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ₘ g.hom
  inv := f.inv ⊗ₘ g.inv
  hom_inv_id := by simp [Iso.hom_inv_id, Iso.hom_inv_id]
  inv_hom_id := by simp [Iso.inv_hom_id, Iso.inv_hom_id]

/-- Notation for `tensorIso`, the tensor product of isomorphisms -/
scoped infixr:70 " ⊗ᵢ " => tensorIso
-- TODO: Try setting this notation to `⊗` if the elaborator is improved and performs
-- better than currently on overloaded notations.

@[to_additive]
theorem tensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ᵢ g = whiskerRightIso f X' ≪≫ whiskerLeftIso Y g :=
  Iso.ext (tensorHom_def f.hom g.hom)

@[to_additive]
theorem tensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ᵢ g = whiskerLeftIso X g ≪≫ whiskerRightIso f Y' :=
  Iso.ext (tensorHom_def' f.hom g.hom)

@[to_additive]
instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ₘ g) :=
  (asIso f ⊗ᵢ asIso g).isIso_hom

@[to_additive (attr := simp) inv_add]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ₘ g) = inv f ⊗ₘ inv g := by
  simp [tensorHom_def, whisker_exchange]

variable {W X Y Z : C}

@[to_additive]
theorem whiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P → (Y ⟶ Z)) (f' : ¬P → (Y ⟶ Z)) :
      X ◁ (if h : P then f h else f' h) = if h : P then X ◁ f h else X ◁ f' h := by
  split_ifs <;> rfl

@[to_additive]
theorem dite_whiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (Z : C) :
      (if h : P then f h else f' h) ▷ Z = if h : P then f h ▷ Z else f' h ▷ Z := by
  split_ifs <;> rfl

@[to_additive]
theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ₘ if h : P then g h else g' h) =
    if h : P then f ⊗ₘ g h else f ⊗ₘ g' h := by split_ifs <;> rfl

@[to_additive]
theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ₘ f =
    if h : P then g h ⊗ₘ f else g' h ⊗ₘ f := by split_ifs <;> rfl

@[to_additive (attr := simp)]
theorem whiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) :
    X ◁ eqToHom f = eqToHom (congr_arg₂ tensorObj rfl f) := by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[to_additive (attr := simp)]
theorem eqToHom_whiskerRight {X Y : C} (f : X = Y) (Z : C) :
    eqToHom f ▷ Z = eqToHom (congr_arg₂ tensorObj f rfl) := by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc (attr := to_additive)]
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by simp

@[reassoc (attr := to_additive)]
theorem associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z := by simp

@[reassoc (attr := to_additive)]
theorem whiskerRight_tensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv := by simp

@[reassoc (attr := to_additive)]
theorem associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z := by simp

@[reassoc (attr := to_additive)]
theorem associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z := by simp

@[reassoc (attr := to_additive)]
theorem whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom := by simp

@[reassoc (attr := to_additive)]
theorem associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f := by simp

@[reassoc (attr := to_additive)]
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f := by simp

@[reassoc (attr := to_additive)]
theorem tensor_whiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom := by simp

@[reassoc (attr := to_additive)]
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv = (λ_ X).inv ≫ _ ◁ f := by simp

@[reassoc (attr := to_additive)]
theorem id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (λ_ X).inv ≫ 𝟙_ C ◁ f ≫ (λ_ X').hom := by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc (attr := to_additive)]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ f ▷ _ := by simp

@[reassoc (attr := to_additive)]
theorem whiskerRight_id_symm {X Y : C} (f : X ⟶ Y) :
    f = (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom := by
  simp

@[to_additive]
theorem whiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g := by simp

@[to_additive]
theorem whiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g := by simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/

section

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_inv_inv_hom_hom_inv :
    (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom =
      W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv := by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv), ← cancel_mono (α_ (W ⊗ X) Y Z).inv]
  simp

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_inv_hom_hom_hom_inv :
    (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom =
      (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_hom_inv_inv_inv_inv :
    W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv =
      (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z := by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_hom_hom_inv_hom_hom :
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv =
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_hom_inv_inv_inv_hom :
    (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv =
      (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z := by
  rw [← cancel_epi (α_ W X (Y ⊗ Z)).inv, ← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_hom_hom_inv_inv_hom :
    (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv =
      (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_inv_hom_hom_hom_hom :
    (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom =
      (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom := by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := to_additive (attr := simp))]
theorem pentagon_inv_inv_hom_inv_inv :
    (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z =
      W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := to_additive (attr := simp))]
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom := by
  rw [← triangle, Iso.inv_hom_id_assoc]

@[reassoc (attr := to_additive (attr := simp))]
theorem triangle_assoc_comp_right_inv (X Y : C) :
    (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y).hom = X ◁ (λ_ Y).inv := by
  simp [← cancel_mono (X ◁ (λ_ Y).hom)]

@[reassoc (attr := to_additive (attr := simp))]
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (X ◁ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight X Y : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`.
-/
@[reassoc]
theorem leftUnitor_whiskerRight (X Y : C) :
    (λ_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, ← cancel_epi (α_ _ _ _).hom, ←
      cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_whiskerRight_assoc, triangle, associator_naturality_left]

attribute [to_additive (attr := simp)] leftUnitor_whiskerRight
attribute [to_additive] leftUnitor_whiskerRight_assoc

@[reassoc]
theorem leftUnitor_inv_whiskerRight (X Y : C) :
    (λ_ X).inv ▷ Y = (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ C) X Y).inv :=
  eq_of_inv_eq_inv (by simp)

attribute [to_additive (attr := simp)] leftUnitor_inv_whiskerRight
attribute [to_additive] leftUnitor_inv_whiskerRight_assoc

@[reassoc]
theorem whiskerLeft_rightUnitor (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X ⊗ Y)).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv, ←
      cancel_epi (X ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, triangle_assoc_comp_right,
      associator_inv_naturality_right]

attribute [to_additive (attr := simp)] whiskerLeft_rightUnitor
attribute [to_additive] whiskerLeft_rightUnitor_assoc

@[reassoc]
theorem whiskerLeft_rightUnitor_inv (X Y : C) :
    X ◁ (ρ_ Y).inv = (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom :=
  eq_of_inv_eq_inv (by simp)

attribute [to_additive (attr := simp)] whiskerLeft_rightUnitor_inv
attribute [to_additive] whiskerLeft_rightUnitor_inv_assoc

@[reassoc (attr := to_additive)]
theorem leftUnitor_tensor_hom (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y := by simp

@[deprecated (since := "2025-06-24")] alias leftUnitor_tensor := leftUnitor_tensor_hom

@[reassoc (attr := to_additive)]
theorem leftUnitor_tensor_inv (X Y : C) :
    (λ_ (X ⊗ Y)).inv = (λ_ X).inv ▷ Y ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc (attr := to_additive)]
theorem rightUnitor_tensor_hom (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by simp

@[deprecated (since := "2025-06-24")] alias rightUnitor_tensor := rightUnitor_tensor_hom

@[reassoc (attr := to_additive)]
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = X ◁ (ρ_ Y).inv ≫ (α_ X Y (𝟙_ C)).inv := by simp

end

@[reassoc (attr := to_additive)]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
  simp [tensorHom_def]

@[reassoc]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g) ⊗ₘ h = (α_ X Y Z).hom ≫ (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

attribute [to_additive (attr := simp)] associator_conjugation
attribute [to_additive] associator_conjugation_assoc

@[reassoc (attr := to_additive)]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ₘ g ⊗ₘ h = (α_ X Y Z).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom := by
  rw [associator_naturality, inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc (attr := to_additive)]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ₘ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 Y ⊗ₘ h) := by
  rw [← id_tensorHom_id, associator_naturality]

@[reassoc (attr := to_additive)]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ₘ 𝟙 Y) ⊗ₘ 𝟙 Z) := by
  rw [← id_tensorHom_id, associator_inv_naturality]

@[reassoc (attr := to_additive)]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⊗ₘ g) ≫ (f.inv ⊗ₘ h) = (𝟙 V ⊗ₘ g) ≫ (𝟙 V ⊗ₘ h) := by simp

@[reassoc (attr := to_additive)]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ₘ g) ≫ (f.hom ⊗ₘ h) = (𝟙 W ⊗ₘ g) ≫ (𝟙 W ⊗ₘ h) := by simp

@[reassoc (attr := to_additive)]
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ f.hom) ≫ (h ⊗ₘ f.inv) = (g ⊗ₘ 𝟙 V) ≫ (h ⊗ₘ 𝟙 V) := by simp

@[reassoc (attr := to_additive)]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ f.inv) ≫ (h ⊗ₘ f.hom) = (g ⊗ₘ 𝟙 W) ≫ (h ⊗ₘ 𝟙 W) := by simp

@[reassoc (attr := to_additive)]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ₘ g) ≫ (inv f ⊗ₘ h) = (𝟙 V ⊗ₘ g) ≫ (𝟙 V ⊗ₘ h) := by simp

@[reassoc (attr := to_additive)]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ₘ g) ≫ (f ⊗ₘ h) = (𝟙 W ⊗ₘ g) ≫ (𝟙 W ⊗ₘ h) := by simp

@[reassoc (attr := to_additive)]
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ f) ≫ (h ⊗ₘ inv f) = (g ⊗ₘ 𝟙 V) ≫ (h ⊗ₘ 𝟙 V) := by simp

@[reassoc (attr := to_additive)]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ inv f) ≫ (h ⊗ₘ f) = (g ⊗ₘ 𝟙 W) ≫ (h ⊗ₘ 𝟙 W) := by simp

/--
A constructor for monoidal categories that requires `tensorHom` instead of `whiskerLeft` and
`whiskerRight`.
-/
abbrev ofTensorHom [MonoidalCategoryStruct C]
    (id_tensorHom_id : ∀ X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
      cat_disch)
    (id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), tensorHom (𝟙 X) f = whiskerLeft X f := by
      cat_disch)
    (tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), tensorHom f (𝟙 Y) = whiskerRight f Y := by
      cat_disch)
    (tensorHom_comp_tensorHom :
      ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
          cat_disch)
    (associator_naturality :
      ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
            cat_disch)
    (leftUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom (𝟙 (𝟙_ C)) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
          cat_disch)
    (rightUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom f (𝟙 (𝟙_ C)) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
          cat_disch)
    (pentagon :
      ∀ W X Y Z : C,
        tensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
            cat_disch)
    (triangle :
      ∀ X Y : C,
        (associator X (𝟙_ C) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
          tensorHom (rightUnitor X).hom (𝟙 Y) := by
            cat_disch) :
      MonoidalCategory C where
  tensorHom_def := by intros; simp [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← id_tensorHom_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, id_tensorHom_id]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]
  triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle]

@[reassoc (attr := to_additive)]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ₘ 𝟙 Z = (f ⊗ₘ 𝟙 Z) ≫ (g ⊗ₘ 𝟙 Z) := by
  simp

@[reassoc (attr := to_additive)]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ₘ f ≫ g = (𝟙 Z ⊗ₘ f) ≫ (𝟙 Z ⊗ₘ g) := by
  simp

@[reassoc (attr := to_additive)]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ₘ f) ≫ (g ⊗ₘ 𝟙 X) = g ⊗ₘ f := by
  simp [tensorHom_def']

@[reassoc (attr := to_additive)]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ₘ 𝟙 W) ≫ (𝟙 Z ⊗ₘ f) = g ⊗ₘ f := by
  simp [tensorHom_def]

theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ₘ f = 𝟙 (𝟙_ C) ⊗ₘ g ↔ f = g := by simp

theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ₘ 𝟙 (𝟙_ C) = g ⊗ₘ 𝟙 (𝟙_ C) ↔ f = g := by simp

section

variable (C)

attribute [local simp] whisker_exchange

/-- The tensor product expressed as a functor. -/
@[to_additive (attr := simps) /-- The sum of objects expressed as a functor. -/]
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ₘ f.2

/-- The left-associated triple tensor product as a functor. -/
@[to_additive /-- The left-associated triple sum of objects as a functor. -/]
def leftAssocTensor : C × C × C ⥤ C where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2

@[to_additive (attr := simp)]
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl

@[to_additive (attr := simp)]
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) :
    (leftAssocTensor C).map f = (f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2 :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
@[to_additive /-- The right-associated triple sum of objects as a functor. -/]
def rightAssocTensor : C × C × C ⥤ C where
  obj X := X.1 ⊗ X.2.1 ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⊗ₘ f.2.1 ⊗ₘ f.2.2

@[to_additive (attr := simp)]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl

@[to_additive (attr := simp)]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) :
    (rightAssocTensor C).map f = f.1 ⊗ₘ f.2.1 ⊗ₘ f.2.2 :=
  rfl

/-- The tensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category. -/
@[to_additive (attr := simps) /-- The sum bifunctor `C ⥤ C ⥤ C` of an additive category. -/]
def curriedTensor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⊗ Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
@[to_additive /-- Adding on the left with a fixed object, as a functor. -/]
abbrev tensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X

/-- Tensoring on the right with a fixed object, as a functor. -/
@[to_additive /-- Adding on the right with a fixed object, as a functor. -/]
abbrev tensorRight (X : C) : C ⥤ C := (curriedTensor C).flip.obj X

variable (C)

/-- The functor `fun X ↦ 𝟙_ C ⊗ X`. -/
@[to_additive /-- The functor `fun X ↦ 0 + X`. -/]
abbrev tensorUnitLeft : C ⥤ C := tensorLeft (𝟙_ C)

/-- The functor `fun X ↦ X ⊗ 𝟙_ C`. -/
@[to_additive /-- The functor `fun X ↦ X + 0`. -/]
abbrev tensorUnitRight : C ⥤ C := tensorRight (𝟙_ C)

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
/-- The associator as a natural isomorphism. -/
@[to_additive (attr := simps!) /-- The associator for sums as a natural isomorphism. -/]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

/-- The left unitor as a natural isomorphism. -/
@[to_additive (attr := simps!) /-- The left unitor for sums as a natural isomorphism. -/]
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.leftUnitor

/-- The right unitor as a natural isomorphism. -/
@[to_additive (attr := simps!) /-- The right unitor for sums as a natural isomorphism. -/]
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.rightUnitor

/-- The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/
@[to_additive (attr := simps!)
/-- The associator for sums as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/]
def curriedAssociatorNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedTensor C) ≅
      bifunctorComp₂₃ (curriedTensor C) (curriedTensor C) :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α_ X₁ X₂ X₃)))

section

variable {C}

/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
@[to_additive
/-- Adding on the left with `X ⊕ Y` is naturally isomorphic to
adding on the left with `Y`, and then again with `X`.
-/]
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[to_additive (attr := simp)]
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl

@[to_additive (attr := simp)]
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensorLeftTensor]

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
@[to_additive /-- Adding on the left, as a functor from `C` into endofunctors of `C`. -/]
abbrev tensoringLeft : C ⥤ C ⥤ C := curriedTensor C

@[to_additive]
instance : (tensoringLeft C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
@[to_additive /-- Adding on the right, as a functor from `C` into endofunctors of `C`. -/]
abbrev tensoringRight : C ⥤ C ⥤ C := (curriedTensor C).flip

@[to_additive]
instance : (tensoringRight C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

variable {C}

/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
@[to_additive
/-- Adding on the right with `X ⊕ Y` is naturally isomorphic to
adding on the right with `X`, and then again with `Y`.
-/]
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[to_additive (attr := simp)]
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl

@[to_additive (attr := simp) addRightAdd_inv_app]
theorem tensorRightTensor_inv_app (X Y Z : C) :
    (tensorRightTensor X Y).inv.app Z = (associator Z X Y).hom := by simp [tensorRightTensor]

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]
variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

@[simps! tensorObj tensorHom tensorUnit whiskerLeft whiskerRight associator]
instance prodMonoidal : MonoidalCategory (C₁ × C₂) where
  tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom f g := (f.1 ⊗ₘ g.1, f.2 ⊗ₘ g.2)
  whiskerLeft X _ _ f := (whiskerLeft X.1 f.1, whiskerLeft X.2 f.2)
  whiskerRight f X := (whiskerRight f.1 X.1, whiskerRight f.2 X.2)
  tensorHom_def := by simp [tensorHom_def]
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)

@[simp]
theorem prodMonoidal_leftUnitor_hom_fst (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).1 = (λ_ X.1).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_hom_snd (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).2 = (λ_ X.2).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_inv_fst (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).1 = (λ_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_inv_snd (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).2 = (λ_ X.2).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_hom_fst (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).1 = (ρ_ X.1).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_hom_snd (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).2 = (ρ_ X.2).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_inv_fst (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).1 = (ρ_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_inv_snd (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).2 = (ρ_ X.2).inv := by
  cases X
  rfl

end

end MonoidalCategory

namespace NatTrans

variable {J : Type*} [Category J] {C : Type*} [Category C] [MonoidalCategory C]
  {F G F' G' : J ⥤ C} (α : F ⟶ F') (β : G ⟶ G')

@[reassoc (attr := to_additive)]
lemma tensor_naturality {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⊗ₘ G.map g) ≫ (α.app Y ⊗ₘ β.app Y') =
      (α.app X ⊗ₘ β.app X') ≫ (F'.map f ⊗ₘ G'.map g) := by simp

@[reassoc (attr := to_additive)]
lemma whiskerRight_app_tensor_app {X Y : J} (f : X ⟶ Y) (X' : J) :
    F.map f ▷ G.obj X' ≫ (α.app Y ⊗ₘ β.app X') =
      (α.app X ⊗ₘ β.app X') ≫ F'.map f ▷ (G'.obj X') := by
  simpa using tensor_naturality α β f (𝟙 X')

@[reassoc (attr := to_additive)]
lemma whiskerLeft_app_tensor_app {X' Y' : J} (f : X' ⟶ Y') (X : J) :
    F.obj X ◁ G.map f ≫ (α.app X ⊗ₘ β.app Y') =
      (α.app X ⊗ₘ β.app X') ≫ F'.obj X ◁ G'.map f := by
  simpa using tensor_naturality α β (𝟙 X) f

end NatTrans

section ObjectProperty

/-- The restriction of a monoidal category along an object property
that's closed under the monoidal structure. -/
-- See note [reducible non-instances]
@[to_additive
/-- The restriction of an additive category along an object property
that's closed under the additive structure.
-/]
abbrev MonoidalCategory.fullSubcategory
    {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : ObjectProperty C)
    (tensorUnit : P (𝟙_ C))
    (tensorObj : ∀ X Y, P X → P Y → P (X ⊗ Y)) :
    MonoidalCategory P.FullSubcategory where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, tensorObj X.1 Y.1 X.2 Y.2⟩
  whiskerLeft X _ _ f := X.1 ◁ f
  whiskerRight f X := MonoidalCategoryStruct.whiskerRight (C := C) f X.1
  tensorHom f g := MonoidalCategoryStruct.tensorHom (C := C) f g
  tensorUnit := ⟨𝟙_ C, tensorUnit⟩
  associator X Y Z := P.fullyFaithfulι.preimageIso (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.fullyFaithfulι.preimageIso (λ_ X.1)
  rightUnitor X := P.fullyFaithfulι.preimageIso (ρ_ X.1)
  tensorHom_def := tensorHom_def (C := C)
  id_tensorHom_id X Y := id_tensorHom_id X.1 Y.1
  tensorHom_comp_tensorHom := tensorHom_comp_tensorHom (C := C)
  whiskerLeft_id X Y := MonoidalCategory.whiskerLeft_id X.1 Y.1
  id_whiskerRight X Y := MonoidalCategory.id_whiskerRight X.1 Y.1
  associator_naturality := associator_naturality (C := C)
  leftUnitor_naturality := leftUnitor_naturality (C := C)
  rightUnitor_naturality := rightUnitor_naturality (C := C)
  pentagon W X Y Z := pentagon W.1 X.1 Y.1 Z.1
  triangle X Y := triangle X.1 Y.1

end ObjectProperty

end CategoryTheory

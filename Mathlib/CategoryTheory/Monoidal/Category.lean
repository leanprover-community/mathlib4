/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Basic

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

Currently, the simp lemmas don't rewrite `𝟙 X ⊗ f` and `f ⊗ 𝟙 Y` into `X ◁ f` and `f ▷ Y`,
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
  /-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
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
@[app_delab CategoryTheory.MonoidalCategoryStruct.tensorUnit]
def delabTensorUnit : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  let e ← getExpr
  guard <| e.isAppOfArity ``MonoidalCategoryStruct.tensorUnit 3
  let C ← withNaryArg 0 delab
  `(𝟙_ $C)

/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
scoped notation "α_" => MonoidalCategoryStruct.associator

/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
scoped notation "λ_" => MonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

end MonoidalCategory

namespace PremonoidalCategory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]

/-- Left tensor product `f ⋉ g = f ▷ _ ≫ _ ◁ g` -/
abbrev ltimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊗ X' ⟶ Y ⊗ Y' :=
  f ▷ X' ≫ Y ◁ g

/-- Right tensor product `f ⋊ g = g ▷ _ ≫ _ ◁ f` -/
abbrev rtimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊗ X' ⟶ Y ⊗ Y' :=
  X ◁ g ≫ f ▷ Y'

/-- Notation for the `ltimes` operator of premonoidal categories -/
scoped infixr:81 " ⋉ " => PremonoidalCategory.ltimes

/-- Notation for the `rtimes` operator of premonoidal categories -/
scoped infixl:81 " ⋊ " => PremonoidalCategory.rtimes

/-- Whether a morphism is _central_, i.e. commutes with all other morphisms in the category `C` -/
class Central {X Y : C} (f : X ⟶ Y) : Prop where
  left_exchange : ∀ {X' Y' : C} (g : X' ⟶ Y'), f ⋉ g = f ⋊ g
  right_exchange : ∀ {X' Y' : C} (g : X' ⟶ Y'), g ⋉ f = g ⋊ f

attribute [reassoc] Central.left_exchange Central.right_exchange

theorem central_iff {X Y : C} (f : X ⟶ Y) : Central f ↔ (∀ {X' Y' : C} (g : X' ⟶ Y'),
  f ⋉ g = f ⋊ g ∧ g ⋉ f = g ⋊ f) := ⟨
    fun h _ _ g => ⟨h.left_exchange g, h.right_exchange g⟩,
    fun h => { left_exchange g := (h g).1, right_exchange g := (h g).2 }⟩

/-- The property that the pentagon relation is satisfied by four objects
in a category equipped with a `MonoidalCategoryStruct`. -/
def Pentagon {C :Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ ⊗ Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ ⊗ Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ ⊗ Y₄)).hom

end PremonoidalCategory

namespace MonoidalCategory

export PremonoidalCategory (ltimes rtimes Pentagon)

end MonoidalCategory

open PremonoidalCategory

open MonoidalCategory

/--
In a premonoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms
`f ⊗ g`. Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations. -/
class PremonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      aesop_cat
  whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  /--
  Left whiskering is compatible with composition of morphisms:
  `(f ≫ g) ◁ X = f ◁ X ≫ g ◁ X`
  -/
  whiskerLeft_comp :
    ∀(W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g := by
    aesop_cat
  /--
  Right whiskering is compatible with composition of morphisms:
  -/
  comp_whiskerRight :
    ∀ {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C),
      (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z := by
    aesop_cat
  /--
  The associator is a central isomorphism
  -/
  associator_central : ∀ {X Y Z : C}, Central (α_ X Y Z).hom := by
    aesop_cat
  /--
  The left unitor is a central isomorphism
  -/
  leftUnitor_central : ∀ {X : C}, Central (λ_ X).hom := by
    aesop_cat
  /--
  The right unitor is a central isomorphism
  -/
  rightUnitor_central : ∀ {X : C}, Central (ρ_ X).hom := by
    aesop_cat
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ f₂) ⊗ f₃ ≃ f₁ ⊗ (f₂ ⊗ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃)) := by
    aesop_cat
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
    aesop_cat
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
    aesop_cat
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    aesop_cat
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
    aesop_cat

attribute [reassoc] PremonoidalCategory.tensorHom_def
attribute [reassoc, simp] PremonoidalCategory.whiskerLeft_id
attribute [reassoc, simp] PremonoidalCategory.id_whiskerRight
attribute [reassoc, simp] PremonoidalCategory.whiskerLeft_comp
attribute [reassoc, simp] PremonoidalCategory.comp_whiskerRight
attribute [reassoc] PremonoidalCategory.associator_naturality
attribute [reassoc] PremonoidalCategory.leftUnitor_naturality
attribute [reassoc] PremonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] PremonoidalCategory.pentagon
attribute [reassoc (attr := simp)] PremonoidalCategory.triangle
attribute [instance] PremonoidalCategory.associator_central
attribute [instance] PremonoidalCategory.leftUnitor_central
attribute [instance] PremonoidalCategory.rightUnitor_central

--TODO: move to PremonoidalCategory?
namespace PremonoidalCategory

variable {C : Type u} [𝒞 : Category.{v} C] [PremonoidalCategory C]

theorem tensor_eq_ltimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : f ⊗ g = f ⋉ g
  := tensorHom_def f g

@[simp]
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ f = X ◁ f := by
  simp only [tensorHom_def, id_whiskerRight, id_comp]

@[simp]
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⊗ 𝟙 Y = f ▷ Y := by
  simp only [tensorHom_def, whiskerLeft_id, comp_id]

theorem tensor_id (X Y : C) : 𝟙 X ⊗ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp

@[reassoc, simp]
theorem id_whiskerLeft {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f = (λ_ X).hom ≫ f ≫ (λ_ Y).inv := by
  rw [← assoc, ← leftUnitor_naturality]; simp [id_tensorHom]

@[reassoc, simp]
theorem tensor_whiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f ≫ (α_ X Y Z').inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc, simp]
theorem whiskerRight_id {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← assoc, ← rightUnitor_naturality]; simp [tensorHom_id]

@[reassoc, simp]
theorem whiskerRight_tensor {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [associator_naturality]
  simp [tensor_id]

@[reassoc, simp]
theorem whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X Y' Z).inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

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
  (whiskerLeftIso X (asIso f)).isIso_hom


@[simp]
theorem inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ f) = X ◁ inv f := by
  aesop_cat

@[simp]
lemma whiskerLeftIso_refl (W X : C) :
    whiskerLeftIso W (Iso.refl X) = Iso.refl (W ⊗ X) :=
  Iso.ext (whiskerLeft_id W X)

@[simp]
lemma whiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
    whiskerLeftIso W (f ≪≫ g) = whiskerLeftIso W f ≪≫ whiskerLeftIso W g :=
  Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[simp]
lemma whiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) :
    (whiskerLeftIso W f).symm = whiskerLeftIso W f.symm := rfl

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[simps!]
def whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X ⊗ Z ≅ Y ⊗ Z where
  hom := f.hom ▷ Z
  inv := f.inv ▷ Z

instance whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z) :=
  (whiskerRightIso (asIso f) Z).isIso_hom

@[simp]
theorem inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ Z) = inv f ▷ Z := by
  aesop_cat

@[simp]
lemma whiskerRightIso_refl (X W : C) :
    whiskerRightIso (Iso.refl X) W = Iso.refl (X ⊗ W) :=
  Iso.ext (id_whiskerRight X W)

@[simp]
lemma whiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) :
    whiskerRightIso (f ≪≫ g) W = whiskerRightIso f W ≪≫ whiskerRightIso g W :=
  Iso.ext (comp_whiskerRight f.hom g.hom W)

@[simp]
lemma whiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) :
    (whiskerRightIso f W).symm = whiskerRightIso f.symm W := rfl

/-- The left tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def ltimesIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⋉ g.hom
  inv := f.inv ⋊ g.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

theorem ltimesIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    ltimesIso f g = whiskerRightIso f X' ≪≫ whiskerLeftIso Y g := rfl

instance ltimes_isIso {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [IsIso f] [IsIso g] :
    IsIso (f ⋉ g) :=
  (ltimesIso (asIso f) (asIso g)).isIso_hom

theorem inv_ltimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [IsIso f] [IsIso g] :
    inv (f ⋉ g) = inv f ⋊ inv g := by simp

/-- The right tensor product of two isomorphisms is an isomorphism. -/
def rtimesIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⋊ g.hom
  inv := f.inv ⋉ g.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

theorem rtimesIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    rtimesIso f g = whiskerLeftIso _ g ≪≫ whiskerRightIso f _ := rfl

instance rtimes_isIso {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [IsIso f] [IsIso g] :
    IsIso (f ⋊ g) :=
  (rtimesIso (asIso f) (asIso g)).isIso_hom

theorem inv_rtimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [IsIso f] [IsIso g] :
    inv (f ⋊ g) = inv f ⋉ inv g := by simp

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⋊ g.inv
  hom_inv_id := by simp [tensorHom_def]
  inv_hom_id := by simp [tensorHom_def]

instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ g) :=
  (tensorIso (asIso f) (asIso g)).isIso_hom

theorem inv_tensor_eq_rtimes {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ g) = inv f ⋊ inv g := by simp [tensor_eq_ltimes]

theorem tensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    tensorIso f g = whiskerRightIso f X' ≪≫ whiskerLeftIso Y g :=
  Iso.ext (tensorHom_def f.hom g.hom)

-- TODO: central tensor iso

variable {W X Y Z : C}

theorem whiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P → (Y ⟶ Z)) (f' : ¬P → (Y ⟶ Z)) :
      X ◁ (if h : P then f h else f' h) = if h : P then X ◁ f h else X ◁ f' h := by
  split_ifs <;> rfl

theorem dite_whiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (Z : C) :
      (if h : P then f h else f' h) ▷ Z = if h : P then f h ▷ Z else f' h ▷ Z := by
  split_ifs <;> rfl

theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ if h : P then g h else g' h) =
    if h : P then f ⊗ g h else f ⊗ g' h := by split_ifs <;> rfl

theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ f =
    if h : P then g h ⊗ f else g' h ⊗ f := by split_ifs <;> rfl

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
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv = (λ_ X).inv ≫ _ ◁ f := by simp

@[reassoc]
theorem id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (λ_ X).inv ≫ 𝟙_ C ◁ f ≫ (λ_ X').hom := by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ f ▷ _ := by simp

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
      (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z := by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

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
      (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom := by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

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
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) := by
  simp [tensorHom_def]

@[reassoc, simp]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g) ⊗ h = (α_ X Y Z).hom ≫ (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

@[reassoc]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ g ⊗ h = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) ≫ (α_ X' Y' Z').hom := by
  rw [associator_naturality, inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ h) := by
  rw [← tensor_id, associator_naturality]

@[reassoc]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) := by
  rw [← tensor_id, associator_inv_naturality]

@[reassoc]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) := by
  simp

@[reassoc]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) := by
  simp

@[reassoc]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f := by
  simp [tensor_eq_ltimes, ltimes]

theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by simp

theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by simp

@[simp]
instance Central.id {X : C} : Central (𝟙 X) where
  left_exchange := by simp [ltimes, rtimes]
  right_exchange := by simp [ltimes, rtimes]

@[simp]
instance Central.eqToHom {X Y : C} (p : X = Y) : Central (eqToHom p) := by cases p; simp

instance Central.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  [hf : Central f] [hg : Central g] : Central (f ≫ g) where
  left_exchange h := by simp [ltimes, rtimes, Central.left_exchange, Central.left_exchange_assoc]
  right_exchange h := by simp [ltimes, rtimes, Central.right_exchange, Central.right_exchange_assoc]

instance Central.inv {X Y : C} {f : X ⟶ Y} [IsIso f] [Central f] : Central (inv f) where
  left_exchange g := by
    rw [ltimes, rtimes, <-cancel_epi (f ▷ _)]
    simp [left_exchange_assoc]
  right_exchange g := by
    rw [ltimes, rtimes, <-cancel_epi (_ ◁ f)]
    simp [<-right_exchange_assoc]

instance Central.iso_inv_of_hom {X Y : C} {f : X ≅ Y} [hf : Central f.hom] : Central f.inv := by
  convert Central.inv (f := f.hom)
  simp

theorem Central.iso_hom_of_inv {X Y : C} {f : X ≅ Y} [hf : Central f.inv] : Central f.hom := by
  convert Central.inv (f := f.inv)
  simp

instance Central.iso_refl {X : C} : Central (Iso.refl X).hom := id

instance Central.iso_symm {X Y : C} {f : X ≅ Y} [hf : Central f.hom] : Central f.symm.hom
  := Central.iso_inv_of_hom

instance Central.iso_comp {X Y Z : C} {f : X ≅ Y} {g : Y ≅ Z}
  [hf : Central f.hom] [hg : Central g.hom] :
  Central (f ≪≫ g).hom := Central.comp

instance Central.whiskerRight {X Y Z : C} (f : X ⟶ Y) [hf : Central f] : Central (f ▷ Z) where
  left_exchange g := by
    simp only [ltimes, tensor_whiskerLeft, rtimes, assoc]
    rw [associator_naturality_left_assoc, <-associator_inv_naturality_left, left_exchange_assoc]
  right_exchange g := by
    simp only [ltimes, whiskerRight_tensor, assoc, rtimes]
    rw [associator_inv_naturality_middle_assoc, <-associator_naturality_middle]
    simp only [ <-comp_whiskerRight_assoc, right_exchange]

instance Central.whiskerRightIso {X Y Z : C} (f : X ≅ Y)
  [hf : Central f.hom] : Central (whiskerRightIso f Z).hom := Central.whiskerRight (f := f.hom)

instance Central.whiskerLeft {X Y Z : C} (f : X ⟶ Y) [hf : Central f] : Central (Z ◁ f) where
  left_exchange g := by simp [ltimes, rtimes, <-whiskerLeft_comp, left_exchange]
  right_exchange g := by
    simp only [ltimes, whiskerRight_tensor, assoc, rtimes]
    rw [associator_inv_naturality_right_assoc, <-associator_naturality_right, right_exchange_assoc]

instance Central.whiskerLeftIso {X Y Z : C} (f : X ≅ Y)
  [hf : Central f.hom] : Central (whiskerLeftIso Z f).hom := Central.whiskerLeft (f := f.hom)

theorem Central.ltimes  {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  [hf : Central f] [hg : Central g] : Central (f ⋉ g) := inferInstance

theorem Central.rtimes  {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  [hf : Central f] [hg : Central g] : Central (f ⋊ g) := inferInstance

instance Central.tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  [hf : Central f] [hg : Central g] : Central (f ⊗ g) := by rw [tensorHom_def]; infer_instance

instance Central.tensorIso {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ≅ Y₁) (g : X₂ ≅ Y₂)
  [hf : Central f.hom] [hg : Central g.hom] : Central (tensorIso f g).hom
  := Central.tensorHom f.hom g.hom

/-- Alternate definition for the tensor product of isomorphisms if the left morphism is central -/
@[simps]
def Central.leftTensorIso {X Y X' Y' : C} (f : X ≅ Y) [Central f.hom] (g : X' ≅ Y')
  : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⊗ g.inv
  hom_inv_id := by simp [tensorHom_def, left_exchange_assoc]
  inv_hom_id := by simp [tensorHom_def, left_exchange_assoc]

theorem Central.leftTensorIso_def {X Y X' Y' : C}
  (f : X ≅ Y) [Central f.hom] (g : X' ≅ Y')
  : Central.leftTensorIso f g = PremonoidalCategory.tensorIso f g
  := Iso.ext rfl

/-- Alternate definition for the tensor product of isomorphisms if the right morphism is central -/
@[simps]
def Central.rightTensorIso {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') [Central g.hom]
  : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⊗ g.inv
  hom_inv_id := by simp [tensorHom_def, right_exchange_assoc]
  inv_hom_id := by simp [tensorHom_def, right_exchange_assoc]

theorem Central.rightTensorIso_def {X Y X' Y' : C}
  (f : X ≅ Y) (g : X' ≅ Y') [Central g.hom]
  : Central.rightTensorIso f g = PremonoidalCategory.tensorIso f g
  := Iso.ext rfl

end PremonoidalCategory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations. -/
@[stacks 0FFK]
-- Porting note: The Mathport did not translate the temporary notation
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends PremonoidalCategory C where
  whisker_exchange :
    ∀ {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z),
      W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
    aesop_cat

attribute [reassoc] MonoidalCategory.whisker_exchange

namespace MonoidalCategory

export PremonoidalCategory (
  tensorHom_def tensorHom_def_assoc
  tensor_id
  whiskerLeft_id whiskerLeft_id_assoc
  id_whiskerRight id_whiskerRight_assoc
  whiskerLeft_comp whiskerLeft_comp_assoc
  comp_whiskerRight comp_whiskerRight_assoc
  associator_naturality associator_naturality_assoc
  leftUnitor_naturality leftUnitor_naturality_assoc
  rightUnitor_naturality rightUnitor_naturality_assoc
  pentagon pentagon_assoc
  triangle triangle_assoc
  id_tensorHom
  tensorHom_id
  id_whiskerLeft id_whiskerLeft_assoc
  tensor_whiskerLeft tensor_whiskerLeft_assoc
  whiskerRight_id whiskerRight_id_assoc
  whiskerRight_tensor whiskerRight_tensor_assoc
  whisker_assoc whisker_assoc_assoc
  whiskerLeft_hom_inv whiskerLeft_hom_inv_assoc
  hom_inv_whiskerRight hom_inv_whiskerRight_assoc
  whiskerLeft_inv_hom whiskerLeft_inv_hom_assoc
  inv_hom_whiskerRight inv_hom_whiskerRight_assoc
  whiskerLeft_hom_inv' whiskerLeft_hom_inv'_assoc
  hom_inv_whiskerRight' hom_inv_whiskerRight'_assoc
  whiskerLeft_inv_hom' whiskerLeft_inv_hom'_assoc
  inv_hom_whiskerRight' inv_hom_whiskerRight'_assoc
  whiskerLeftIso whiskerLeftIso_hom whiskerLeft_isIso
  inv_whiskerLeft
  whiskerLeftIso_refl whiskerLeftIso_trans whiskerLeftIso_symm
  whiskerRightIso whiskerRightIso_hom whiskerRight_isIso
  inv_whiskerRight
  whiskerRightIso_refl whiskerRightIso_trans whiskerRightIso_symm
  tensorIso tensorIso_hom tensor_isIso tensorIso_def
  whiskerLeft_dite dite_whiskerRight tensor_dite dite_tensor
  whiskerLeft_eqToHom eqToHom_whiskerRight
  associator_naturality_left associator_naturality_left_assoc
  associator_inv_naturality_left associator_inv_naturality_left_assoc
  whiskerRight_tensor_symm whiskerRight_tensor_symm_assoc
  associator_naturality_middle associator_naturality_middle_assoc
  associator_inv_naturality_middle associator_inv_naturality_middle_assoc
  whisker_assoc_symm whisker_assoc_symm_assoc
  associator_naturality_right associator_naturality_right_assoc
  associator_inv_naturality_right associator_inv_naturality_right_assoc
  tensor_whiskerLeft_symm tensor_whiskerLeft_symm_assoc
  leftUnitor_inv_naturality leftUnitor_inv_naturality_assoc
  id_whiskerLeft_symm id_whiskerLeft_symm_assoc
  rightUnitor_inv_naturality rightUnitor_inv_naturality_assoc
  whiskerRight_id_symm whiskerRight_id_symm_assoc
  whiskerLeft_iff whiskerRight_iff
  pentagon_inv pentagon_inv_assoc
  pentagon_inv_inv_hom_hom_inv pentagon_inv_inv_hom_hom_inv_assoc
  pentagon_inv_hom_hom_hom_inv pentagon_inv_hom_hom_hom_inv_assoc
  pentagon_hom_inv_inv_inv_inv pentagon_hom_inv_inv_inv_inv_assoc
  pentagon_hom_hom_inv_hom_hom pentagon_hom_hom_inv_hom_hom_assoc
  pentagon_hom_inv_inv_inv_hom pentagon_hom_inv_inv_inv_hom_assoc
  pentagon_hom_hom_inv_inv_hom pentagon_hom_hom_inv_inv_hom_assoc
  pentagon_inv_hom_hom_hom_hom pentagon_inv_hom_hom_hom_hom_assoc
  pentagon_inv_inv_hom_inv_inv pentagon_inv_inv_hom_inv_inv_assoc
  pentagon_hom_hom_inv_inv_hom pentagon_hom_hom_inv_inv_hom_assoc
  triangle_assoc_comp_right triangle_assoc_comp_right_assoc
  triangle_assoc_comp_right_inv triangle_assoc_comp_right_inv_assoc
  triangle_assoc_comp_left_inv triangle_assoc_comp_left_inv_assoc
  leftUnitor_whiskerRight leftUnitor_whiskerRight_assoc
  leftUnitor_inv_whiskerRight leftUnitor_inv_whiskerRight_assoc
  whiskerLeft_rightUnitor whiskerLeft_rightUnitor_assoc
  whiskerLeft_rightUnitor_inv whiskerLeft_rightUnitor_inv_assoc
  leftUnitor_tensor leftUnitor_tensor_assoc
  leftUnitor_tensor_inv leftUnitor_tensor_inv_assoc
  rightUnitor_tensor rightUnitor_tensor_assoc
  rightUnitor_tensor_inv rightUnitor_tensor_inv_assoc
  associator_inv_naturality associator_inv_naturality_assoc
  associator_conjugation associator_conjugation_assoc
  associator_inv_conjugation associator_inv_conjugation_assoc
  id_tensor_associator_naturality id_tensor_associator_naturality_assoc
  id_tensor_associator_inv_naturality id_tensor_associator_inv_naturality_assoc
  comp_tensor_id comp_tensor_id_assoc
  id_tensor_comp id_tensor_comp_assoc
  tensor_id_comp_id_tensor tensor_id_comp_id_tensor_assoc
  tensor_left_iff tensor_right_iff
)

variable {C : Type u} [𝒞 : Category.{v} C]

theorem whisker_exchange_helper [MonoidalCategoryStruct C]
  (tensorHom_def : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by aesop_cat)
  (whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by aesop_cat)
  (id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by aesop_cat)
  (tensor_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by aesop_cat)
  {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  have id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), 𝟙 X ⊗ f = X ◁ f
    := by intros; simp only [tensorHom_def, id_whiskerRight, id_comp]
  have tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), f ⊗ 𝟙 Y = f ▷ Y
    := by intros; simp only [tensorHom_def, whiskerLeft_id, comp_id]
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

theorem central_helper  [MonoidalCategoryStruct C]
  (tensorHom_def : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by aesop_cat)
  (whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by aesop_cat)
  (id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by aesop_cat)
  (tensor_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by aesop_cat)
  {X Y : C} (f : X ⟶ Y) : Central f where
  left_exchange g := by simp [ltimes, rtimes,
    whisker_exchange_helper tensorHom_def whiskerLeft_id id_whiskerRight tensor_comp]
  right_exchange g := by simp [ltimes, rtimes,
    whisker_exchange_helper tensorHom_def whiskerLeft_id id_whiskerRight tensor_comp]


/--
A constructor for monoidal categories that requires `tensor_comp` instead of `whiskerLeft_comp`,
`comp_whiskerRight`, and `whisker_exchange`.
-/
abbrev ofTensorComp [MonoidalCategoryStruct C]
  (tensorHom_def : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by aesop_cat)
  (tensor_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by aesop_cat)
  (whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by aesop_cat)
  (id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by aesop_cat)
  (associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃)) := by aesop_cat)
  (leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by aesop_cat)
  (rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by aesop_cat)
  (pentagon : ∀ W X Y Z : C,
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by aesop_cat)
  (triangle : ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by aesop_cat)
  : MonoidalCategory C where
  tensorHom_def := tensorHom_def
  whiskerLeft_id := whiskerLeft_id
  id_whiskerRight := id_whiskerRight
  whiskerLeft_comp := by
    have id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), 𝟙 X ⊗ f = X ◁ f
      := by intros; simp only [tensorHom_def, id_whiskerRight, id_comp]
    intros; simp only [← id_tensorHom, ← tensor_comp, comp_id]
  comp_whiskerRight := by
    have tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), f ⊗ 𝟙 Y = f ▷ Y
      := by intros; simp only [tensorHom_def, whiskerLeft_id, comp_id]
    intros; simp only [← tensorHom_id, ← tensor_comp, id_comp]
  associator_central := by intros; apply central_helper <;> assumption
  leftUnitor_central := by intros; apply central_helper <;> assumption
  rightUnitor_central := by intros; apply central_helper <;> assumption
  associator_naturality := associator_naturality
  leftUnitor_naturality := leftUnitor_naturality
  rightUnitor_naturality := rightUnitor_naturality
  pentagon := pentagon
  triangle := triangle
  whisker_exchange :=
    whisker_exchange_helper tensorHom_def whiskerLeft_id id_whiskerRight tensor_comp

variable [MonoidalCategory C]

-- In a monoidal category, everything is central
instance Central.ofMonoidal {X Y : C} (f : X ⟶ Y) : Central f where
  left_exchange := by simp [whisker_exchange]
  right_exchange := by simp [whisker_exchange]

@[reassoc, simp]
theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)
    := by simp [tensorHom_def, whisker_exchange, whisker_exchange_assoc]

@[reassoc]
theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ :=
  whisker_exchange f g ▸ tensorHom_def f g

/-- Notation for `tensorIso`, the tensor product of isomorphisms -/
scoped infixr:70 " ⊗ " => tensorIso

theorem tensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ g = whiskerLeftIso X g ≪≫ whiskerRightIso f Y' :=
  Iso.ext (tensorHom_def' f.hom g.hom)

@[simp]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ g) = inv f ⊗ inv g := by
  simp [tensorHom_def ,whisker_exchange]

variable {W X Y Z : C}

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⊗ g) ≫ (f.inv ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, f.hom_inv_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.hom ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, f.inv_hom_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.hom) ≫ (h ⊗ f.inv) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, f.hom_inv_id]; simp [tensorHom_id]

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.hom) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, f.inv_hom_id]; simp [tensorHom_id]

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ g) ≫ (inv f ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, IsIso.hom_inv_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ g) ≫ (f ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, IsIso.inv_hom_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f) ≫ (h ⊗ inv f) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, IsIso.hom_inv_id]; simp [tensorHom_id]

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ inv f) ≫ (h ⊗ f) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, IsIso.inv_hom_id]; simp [tensorHom_id]

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
      MonoidalCategory C :=
  ofTensorComp
    (tensorHom_def := by intros; simp [← id_tensorHom, ← tensorHom_id, ← tensor_comp])
    (whiskerLeft_id := by intros; simp [← id_tensorHom, ← tensor_id])
    (id_whiskerRight := by intros; simp [← tensorHom_id, tensor_id])
    (pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon])
    (triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle])

@[reassoc]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f := by
  rw [← tensor_comp]
  simp

section

variable (C)

attribute [local simp] whisker_exchange

/-- The tensor product expressed as a functor. -/
@[simps]
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ f.2

/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ f.2.1) ⊗ f.2.2

@[simp]
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl

@[simp]
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C where
  obj X := X.1 ⊗ X.2.1 ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⊗ f.2.1 ⊗ f.2.2

@[simp]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl

@[simp]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl

/-- The tensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category. -/
@[simps]
def curriedTensor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⊗ Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps!]
def tensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps!]
def tensorRight (X : C) : C ⥤ C := (curriedTensor C).flip.obj X

variable (C)

/-- The functor `fun X ↦ 𝟙_ C ⊗ X`. -/
abbrev tensorUnitLeft : C ⥤ C := tensorLeft (𝟙_ C)

/-- The functor `fun X ↦ X ⊗ 𝟙_ C`. -/
abbrev tensorUnitRight : C ⥤ C := tensorRight (𝟙_ C)

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
/-- The associator as a natural isomorphism. -/
@[simps!]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

/-- The left unitor as a natural isomorphism. -/
@[simps!]
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.leftUnitor

/-- The right unitor as a natural isomorphism. -/
@[simps!]
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.rightUnitor

/-- The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/
@[simps!]
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
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl

@[simp]
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensorLeftTensor]

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
abbrev tensoringLeft : C ⥤ C ⥤ C := curriedTensor C

instance : (tensoringLeft C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
abbrev tensoringRight : C ⥤ C ⥤ C := (curriedTensor C).flip

instance : (tensoringRight C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

variable {C}

/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl

@[simp]
theorem tensorRightTensor_inv_app (X Y Z : C) :
    (tensorRightTensor X Y).inv.app Z = (associator Z X Y).hom := by simp [tensorRightTensor]

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]
variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

@[simps! tensorObj tensorHom tensorUnit whiskerLeft whiskerRight associator, reducible]
instance prodMonoidal : MonoidalCategory (C₁ × C₂) :=
  letI _ : MonoidalCategoryStruct (C₁ × C₂) := {
      tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
      tensorHom f g := (f.1 ⊗ g.1, f.2 ⊗ g.2)
      whiskerLeft X _ _ f := (whiskerLeft X.1 f.1, whiskerLeft X.2 f.2)
      whiskerRight f X := (whiskerRight f.1 X.1, whiskerRight f.2 X.2)
      tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
      associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
      leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).prod (λ_ X₂)
      rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)
  };
  ofTensorHom

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

@[reassoc]
lemma tensor_naturality {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⊗ G.map g) ≫ (α.app Y ⊗ β.app Y') =
      (α.app X ⊗ β.app X') ≫ (F'.map f ⊗ G'.map g) := by
  simp only [← tensor_comp, naturality]

@[reassoc]
lemma whiskerRight_app_tensor_app {X Y : J} (f : X ⟶ Y) (X' : J) :
    F.map f ▷ G.obj X' ≫ (α.app Y ⊗ β.app X') =
      (α.app X ⊗ β.app X') ≫ F'.map f ▷ (G'.obj X') := by
  simpa using tensor_naturality α β f (𝟙 X')

@[reassoc]
lemma whiskerLeft_app_tensor_app {X' Y' : J} (f : X' ⟶ Y') (X : J) :
    F.obj X ◁ G.map f ≫ (α.app X ⊗ β.app Y') =
      (α.app X ⊗ β.app X') ≫ F'.obj X ◁ G'.map f := by
  simpa using tensor_naturality α β (𝟙 X) f

end NatTrans

end CategoryTheory

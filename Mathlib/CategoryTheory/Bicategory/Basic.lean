/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.NatIso

/-!
# Bicategories

In this file we define typeclass for bicategories.

A bicategory `B` consists of
* objects `a : B`,
* 1-morphisms `f : a ⟶ b` between objects `a b : B`, and
* 2-morphisms `η : f ⟶ g` between 1-morphisms `f g : a ⟶ b` between objects `a b : B`.

We use `u`, `v`, and `w` as the universe variables for objects, 1-morphisms, and 2-morphisms,
respectively.

A typeclass for bicategories extends `CategoryTheory.CategoryStruct` typeclass. This means that
we have
* a composition `f ≫ g : a ⟶ c` for each 1-morphisms `f : a ⟶ b` and `g : b ⟶ c`, and
* an identity `𝟙 a : a ⟶ a` for each object `a : B`.

For each object `a b : B`, the collection of 1-morphisms `a ⟶ b` has a category structure. The
2-morphisms in the bicategory are implemented as the morphisms in this family of categories.

The composition of 1-morphisms is in fact an object part of a functor
`(a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c)`. The definition of bicategories in this file does not
require this functor directly. Instead, it requires the whiskering functions. For a 1-morphism
`f : a ⟶ b` and a 2-morphism `η : g ⟶ h` between 1-morphisms `g h : b ⟶ c`, there is a
2-morphism `whiskerLeft f η : f ≫ g ⟶ f ≫ h`. Similarly, for a 2-morphism `η : f ⟶ g`
between 1-morphisms `f g : a ⟶ b` and a 1-morphism `f : b ⟶ c`, there is a 2-morphism
`whiskerRight η h : f ≫ h ⟶ g ≫ h`. These satisfy the exchange law
`whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ`,
which is required as an axiom in the definition here.
-/

namespace CategoryTheory

universe w v u

open Category Iso

-- intended to be used with explicit universe parameters
/-- In a bicategory, we can compose the 1-morphisms `f : a ⟶ b` and `g : b ⟶ c` to obtain
a 1-morphism `f ≫ g : a ⟶ c`. This composition does not need to be strictly associative,
but there is a specified associator, `α_ f g h : (f ≫ g) ≫ h ≅ f ≫ (g ≫ h)`.
There is an identity 1-morphism `𝟙 a : a ⟶ a`, with specified left and right unitor
isomorphisms `λ_ f : 𝟙 a ≫ f ≅ f` and `ρ_ f : f ≫ 𝟙 a ≅ f`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://ncatlab.org/nlab/show/bicategory.
-/
@[nolint checkUnivs]
class Bicategory (B : Type u) extends CategoryStruct.{v} B where
  /-- The category structure on the collection of 1-morphisms -/
  homCategory : ∀ a b : B, Category.{w} (a ⟶ b) := by infer_instance
  /-- Left whiskering for morphisms -/
  whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h
  /-- Right whiskering for morphisms -/
  whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h
  /-- The associator isomorphism: `(f ≫ g) ≫ h ≅ f ≫ g ≫ h` -/
  associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h ≅ f ≫ g ≫ h
  /-- The left unitor: `𝟙 a ≫ f ≅ f` -/
  leftUnitor {a b : B} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f
  /-- The right unitor: `f ≫ 𝟙 b ≅ f` -/
  rightUnitor {a b : B} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f
  -- axioms for left whiskering:
  whiskerLeft_id : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := by
    cat_disch
  whiskerLeft_comp :
    ∀ {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
      whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := by
    cat_disch
  id_whiskerLeft :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerLeft (𝟙 a) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := by
    cat_disch
  comp_whiskerLeft :
    ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
      whiskerLeft (f ≫ g) η =
        (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv := by
    cat_disch
  -- axioms for right whiskering:
  id_whiskerRight : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := by
    cat_disch
  comp_whiskerRight :
    ∀ {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
      whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := by
    cat_disch
  whiskerRight_id :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := by
    cat_disch
  whiskerRight_comp :
    ∀ {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
      whiskerRight η (g ≫ h) =
        (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom := by
    cat_disch
  -- associativity of whiskerings:
  whisker_assoc :
    ∀ {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
      whiskerRight (whiskerLeft f η) h =
        (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv := by
    cat_disch
  -- exchange law of left and right whiskerings:
  whisker_exchange :
    ∀ {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
      whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := by
    cat_disch
  -- pentagon identity:
  pentagon :
    ∀ {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
      whiskerRight (associator f g h).hom i ≫
          (associator f (g ≫ h) i).hom ≫ whiskerLeft f (associator g h i).hom =
        (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom := by
    cat_disch
  -- triangle identity:
  triangle :
    ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      (associator f (𝟙 b) g).hom ≫ whiskerLeft f (leftUnitor g).hom
      = whiskerRight (rightUnitor f).hom g := by
    cat_disch

namespace Bicategory

@[inherit_doc] scoped infixr:81 " ◁ " => Bicategory.whiskerLeft
@[inherit_doc] scoped infixl:81 " ▷ " => Bicategory.whiskerRight
@[inherit_doc] scoped notation "α_" => Bicategory.associator
@[inherit_doc] scoped notation "λ_" => Bicategory.leftUnitor
@[inherit_doc] scoped notation "ρ_" => Bicategory.rightUnitor

/-!
### Simp-normal form for 2-morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any 2-morphisms into simp-normal
form defined below. Rewriting into simp-normal form is also useful when applying (forthcoming)
`coherence` tactic.

The simp-normal form of 2-morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of 2-morphisms like `η₁ ≫ η₂ ≫ η₃ ≫ η₄ ≫ η₅` such that each `ηᵢ` is
  either a structural 2-morphisms (2-morphisms made up only of identities, associators, unitors)
  or non-structural 2-morphisms, and
2. each non-structural 2-morphism in the composition is of the form `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅`,
  where each `fᵢ` is a 1-morphism that is not the identity or a composite and `η` is a
  non-structural 2-morphisms that is also not the identity or a composite.

Note that `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅` is actually `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))`.
-/

attribute [instance] homCategory

attribute [reassoc]
  whiskerLeft_comp id_whiskerLeft comp_whiskerLeft comp_whiskerRight whiskerRight_id
  whiskerRight_comp whisker_assoc whisker_exchange

attribute [reassoc (attr := simp)] pentagon triangle
/-
The following simp attributes are put in order to rewrite any 2-morphisms into normal forms. There
are associators and unitors in the RHS in the several simp lemmas here (e.g. `id_whiskerLeft`),
which at first glance look more complicated than the LHS, but they will be eventually reduced by
the pentagon or the triangle identities, and more generally, (forthcoming) `coherence` tactic.
-/
attribute [simp]
  whiskerLeft_id whiskerLeft_comp id_whiskerLeft comp_whiskerLeft id_whiskerRight comp_whiskerRight
  whiskerRight_id whiskerRight_comp whisker_assoc


variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g) := by rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
    η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h) := by rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_inv_hom (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h) := by rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
    η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h) := by rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_whiskerLeft_hom_inv (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k) :
    f ◁ g ◁ η.hom ≫ f ◁ g ◁ η.inv = 𝟙 (f ≫ g ≫ h) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem hom_inv_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d) :
    η.hom ▷ h ▷ k ≫ η.inv ▷ h ▷ k = 𝟙 ((f ≫ h) ≫ k) := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_whiskerLeft_inv_hom (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k) :
    f ◁ g ◁ η.inv ≫ f ◁ g ◁ η.hom = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem inv_hom_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d) :
    η.inv ▷ h ▷ k ≫ η.hom ▷ h ▷ k = 𝟙 ((g ≫ h) ≫ k) := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.hom ▷ k ≫ f ◁ η.inv ▷ k = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem whiskerLeft_inv_hom_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.inv ▷ k ≫ f ◁ η.hom ▷ k = 𝟙 (f ≫ h ≫ k) := by
  simp [← whiskerLeft_comp]

/-- The left whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps]
def whiskerLeftIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ≫ g ≅ f ≫ h where
  hom := f ◁ η.hom
  inv := f ◁ η.inv

instance whiskerLeft_isIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : IsIso (f ◁ η) :=
  (whiskerLeftIso f (asIso η)).isIso_hom

@[simp]
theorem inv_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] :
    inv (f ◁ η) = f ◁ inv η := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← whiskerLeft_comp, whiskerLeft_id, IsIso.hom_inv_id]

/-- The right whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps!]
def whiskerRightIso {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h where
  hom := η.hom ▷ h
  inv := η.inv ▷ h

instance whiskerRight_isIso {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : IsIso (η ▷ h) :=
  (whiskerRightIso (asIso η) h).isIso_hom

@[simp]
theorem inv_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] :
    inv (η ▷ h) = inv η ▷ h := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← comp_whiskerRight, id_whiskerRight, IsIso.hom_inv_id]

@[reassoc (attr := simp)]
theorem pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i =
      (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom =
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv := by
  rw [← cancel_epi (f ◁ (α_ g h i).inv), ← cancel_mono (α_ (f ≫ g) h i).inv]
  simp

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom =
      (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
      (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  simp [← cancel_epi (f ◁ (α_ g h i).inv)]

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv =
      (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv =
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i := by
  rw [← cancel_epi (α_ f g (h ≫ i)).inv, ← cancel_mono ((α_ f g h).inv ▷ i)]
  simp

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv =
      (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
      (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom := by
  simp [← cancel_epi ((α_ f g h).hom ▷ i)]

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i =
      f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv :=
  eq_of_inv_eq_inv (by simp)

theorem triangle_assoc_comp_left (f : a ⟶ b) (g : b ⟶ c) :
    (α_ f (𝟙 b) g).hom ≫ f ◁ (λ_ g).hom = (ρ_ f).hom ▷ g :=
  triangle f g

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right (f : a ⟶ b) (g : b ⟶ c) :
    (α_ f (𝟙 b) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (λ_ g).hom := by rw [← triangle, inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right_inv (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ f).inv ▷ g ≫ (α_ f (𝟙 b) g).hom = f ◁ (λ_ g).inv := by
  simp [← cancel_mono (f ◁ (λ_ g).hom)]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_left_inv (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g := by
  simp [← cancel_mono ((ρ_ f).hom ▷ g)]

@[reassoc]
theorem associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h) := by simp

@[reassoc]
theorem associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) ≫ (α_ f' g h).inv = (α_ f g h).inv ≫ η ▷ g ▷ h := by simp

@[reassoc]
theorem whiskerRight_comp_symm {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h = (α_ f g h).hom ≫ η ▷ (g ≫ h) ≫ (α_ f' g h).inv := by simp

@[reassoc]
theorem associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ h := by simp

@[reassoc]
theorem associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    f ◁ η ▷ h ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ (f ◁ η) ▷ h := by simp

@[reassoc]
theorem whisker_assoc_symm (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    f ◁ η ▷ h = (α_ f g h).inv ≫ (f ◁ η) ▷ h ≫ (α_ f g' h).hom := by simp

@[reassoc]
theorem associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ g ◁ η := by simp

@[reassoc]
theorem associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η ≫ (α_ f g h').inv = (α_ f g h).inv ≫ (f ≫ g) ◁ η := by simp

@[reassoc]
theorem comp_whiskerLeft_symm (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η = (α_ f g h).inv ≫ (f ≫ g) ◁ η ≫ (α_ f g h').hom := by simp

@[reassoc]
theorem leftUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η ≫ (λ_ g).hom = (λ_ f).hom ≫ η := by
  simp

@[reassoc]
theorem leftUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (λ_ g).inv = (λ_ f).inv ≫ 𝟙 a ◁ η := by simp

theorem id_whiskerLeft_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (λ_ f).inv ≫ 𝟙 a ◁ η ≫ (λ_ g).hom := by
  simp

@[reassoc]
theorem rightUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η := by simp

@[reassoc]
theorem rightUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (ρ_ g).inv = (ρ_ f).inv ≫ η ▷ 𝟙 b := by simp

theorem whiskerRight_id_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (ρ_ f).inv ≫ η ▷ 𝟙 b ≫ (ρ_ g).hom := by
  simp

theorem whiskerLeft_iff {f g : a ⟶ b} (η θ : f ⟶ g) : 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ := by simp

theorem whiskerRight_iff {f g : a ⟶ b} (η θ : f ⟶ g) : η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ := by simp

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight f g : 𝟙 f ▷ g = 𝟙 (f ≫ g)`.
-/
@[reassoc, simp]
theorem leftUnitor_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (λ_ (f ≫ g)).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, ← cancel_epi (α_ _ _ _).hom, ←
      cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_whiskerRight_assoc, triangle, associator_naturality_left]

@[reassoc, simp]
theorem leftUnitor_inv_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ f).inv ▷ g = (λ_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
theorem whiskerLeft_rightUnitor (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv, ←
      cancel_epi (f ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, triangle_assoc_comp_right,
      associator_inv_naturality_right]

@[reassoc, simp]
theorem whiskerLeft_rightUnitor_inv (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g (𝟙 c)).hom :=
  eq_of_inv_eq_inv (by simp)

/-
It is not so obvious whether `leftUnitor_whiskerRight` or `leftUnitor_comp` should be a simp
lemma. Our choice is the former. One reason is that the latter yields the following loop:
[id_whiskerLeft]   : 𝟙 a ◁ (ρ_ f).hom ==> (λ_ (f ≫ 𝟙 b)).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv
[leftUnitor_comp]  : (λ_ (f ≫ 𝟙 b)).hom ==> (α_ (𝟙 a) f (𝟙 b)).inv ≫ (λ_ f).hom ▷ 𝟙 b
[whiskerRight_id]  : (λ_ f).hom ▷ 𝟙 b ==> (ρ_ (𝟙 a ≫ f)).hom ≫ (λ_ f).hom ≫ (ρ_ f).inv
[rightUnitor_comp] : (ρ_ (𝟙 a ≫ f)).hom ==> (α_ (𝟙 a) f (𝟙 b)).hom ≫ 𝟙 a ◁ (ρ_ f).hom
-/
@[reassoc]
theorem leftUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ (f ≫ g)).hom = (α_ (𝟙 a) f g).inv ≫ (λ_ f).hom ▷ g := by simp

@[reassoc]
theorem leftUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ (f ≫ g)).inv = (λ_ f).inv ▷ g ≫ (α_ (𝟙 a) f g).hom := by simp

@[reassoc]
theorem rightUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c)).hom ≫ f ◁ (ρ_ g).hom := by simp

@[reassoc]
theorem rightUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ (f ≫ g)).inv = f ◁ (ρ_ g).inv ≫ (α_ f g (𝟙 c)).inv := by simp

@[simp]
theorem unitors_equal : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  rw [← whiskerLeft_iff, ← cancel_epi (α_ _ _ _).hom, ← cancel_mono (ρ_ _).hom, triangle, ←
      rightUnitor_comp, rightUnitor_naturality]

@[simp]
theorem unitors_inv_equal : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by simp [Iso.inv_eq_inv]

section

attribute [local simp] whisker_exchange

/-- Precomposition of a 1-morphism as a functor. -/
@[simps]
def precomp (c : B) (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj := (f ≫ ·)
  map := (f ◁ ·)

/-- Precomposition of a 1-morphism as a functor from the category of 1-morphisms `a ⟶ b` into the
category of functors `(b ⟶ c) ⥤ (a ⟶ c)`. -/
@[simps]
def precomposing (a b c : B) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) where
  obj f := precomp c f
  map η := { app := (η ▷ ·) }

/-- Postcomposition of a 1-morphism as a functor. -/
@[simps]
def postcomp (a : B) (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj := (· ≫ f)
  map := (· ▷ f)

/-- Postcomposition of a 1-morphism as a functor from the category of 1-morphisms `b ⟶ c` into the
category of functors `(a ⟶ b) ⥤ (a ⟶ c)`. -/
@[simps]
def postcomposing (a b c : B) : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := postcomp a f
  map η := { app := (· ◁ η) }

/-- Left component of the associator as a natural isomorphism. -/
@[simps!]
def associatorNatIsoLeft (a : B) (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposing a ..).obj g ⋙ (postcomposing ..).obj h ≅ (postcomposing ..).obj (g ≫ h) :=
  NatIso.ofComponents (α_ · g h)

/-- Middle component of the associator as a natural isomorphism. -/
@[simps!]
def associatorNatIsoMiddle (f : a ⟶ b) (h : c ⟶ d) :
    (precomposing ..).obj f ⋙ (postcomposing ..).obj h ≅
      (postcomposing ..).obj h ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f · h)

/-- Right component of the associator as a natural isomorphism. -/
@[simps!]
def associatorNatIsoRight (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposing _ _ d).obj (f ≫ g) ≅ (precomposing ..).obj g ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f g ·)

/-- Left unitor as a natural isomorphism. -/
@[simps!]
def leftUnitorNatIso (a b : B) : (precomposing _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (λ_ ·)

/-- Right unitor as a natural isomorphism. -/
@[simps!]
def rightUnitorNatIso (a b : B) : (postcomposing a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (ρ_ ·)

end

end Bicategory

end CategoryTheory

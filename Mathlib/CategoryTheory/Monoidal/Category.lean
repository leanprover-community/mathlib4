/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.monoidal.category
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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

Some consequences of the definition are proved in other files,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `CategoryTheory.Monoidal.UnitorsEqual`.

## Implementation
Dealing with unitors and associators is painful, and at this stage we do not have a useful
implementation of coherence for monoidal categories.

In an effort to lessen the pain, we put some effort into choosing the right `simp` lemmas.
Generally, the rule is that the component index of a natural transformation "weighs more"
in considering the complexity of an expression than does a structural isomorphism (associator, etc).

As an example when we prove Proposition 2.2.4 of
<http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
we state it as a `@[simp]` lemma as
```
(λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ⊗ (𝟙 Y)
```

This is far from completely effective, but seems to prove a useful principle.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/


open CategoryTheory

universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See <https://stacks.math.columbia.edu/tag/0FFK>.
-/
-- Porting note: The Mathport did not translate the temporary notation
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C → C → C
  /-- curried tensor product of morphisms -/
  tensorHom : ∀ {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂)
  /-- Tensor product of identiy maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  tensor_id : ∀ X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by aesop_cat
  /--
  Composition of tensor products is tensor product of compositions:
  `(f₁ ⊗ g₁) ∘ (f₂ ⊗ g₂) = (f₁ ∘ f₂) ⊗ (g₁ ⊗ g₂)`
  -/
  tensor_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
    aesop_cat
  -- Porting note: Adding a prime here, so I can later define `tensorUnit` unprimed with explicit
  --               argument `C`
  /-- The tensor unity in the monoidal structure `𝟙_C` -/
  tensorUnit' : C
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ f₂) ⊗ f₃ ≃ f₁ ⊗ (f₂ ⊗ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
        (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
    aesop_cat
  /-- The left unitor: `𝟙_C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit' X ≅ X
  /--
  Naturality of the left unitor, commutativity of `𝟙_C ⊗ X ⟶ 𝟙_C ⊗ Y ⟶ Y` and `𝟙_C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      tensorHom (𝟙 tensorUnit') f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
    aesop_cat
  /-- The right unitor: `X ⊗ 𝟙_C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit' ≅ X
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_C ⟶ Y ⊗ 𝟙_C ⟶ Y` and `X ⊗ 𝟙_C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      tensorHom f (𝟙 tensorUnit') ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
    aesop_cat
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      tensorHom (associator W X Y).hom (𝟙 Z) ≫
          (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
        (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
    aesop_cat
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_C ⊗ Y)`, `(X ⊗ 𝟙_C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C,
      (associator X tensorUnit' Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
        tensorHom (rightUnitor X).hom (𝟙 Y) := by
    aesop_cat
#align category_theory.monoidal_category CategoryTheory.MonoidalCategory

-- Porting Note: `restate_axiom` doesn't seem to be necessary in Lean 4
-- restate_axiom MonoidalCategory.tensor_id'

attribute [simp] MonoidalCategory.tensor_id

-- Porting Note: same as above
-- restate_axiom MonoidalCategory.tensor_comp'

attribute [reassoc] MonoidalCategory.tensor_comp

-- This would be redundant in the simp set.
attribute [simp] MonoidalCategory.tensor_comp

-- Porting Note: same as above
-- restate_axiom MonoidalCategory.associator_naturality'

attribute [reassoc] MonoidalCategory.associator_naturality

-- Porting Note: same as above
-- restate_axiom MonoidalCategory.leftUnitor_naturality'

attribute [reassoc] MonoidalCategory.leftUnitor_naturality

-- Porting Note: same as above
-- restate_axiom MonoidalCategory.rightUnitor_naturality'

attribute [reassoc] MonoidalCategory.rightUnitor_naturality

-- Porting Note: same as above
-- restate_axiom MonoidalCategory.pentagon'

-- Porting Note: same as above
-- restate_axiom MonoidalCategory.triangle'

attribute [reassoc] MonoidalCategory.pentagon

attribute [reassoc (attr := simp)] MonoidalCategory.triangle

-- Porting Note: This is here to make `tensorUnit` explicitly depend on `C`, which was done in
--               Lean 3 using the `[]` notation in the `tensorUnit'` field.
open CategoryTheory.MonoidalCategory in
/-- The tensor unity in the monoidal structure `𝟙_C` -/
abbrev MonoidalCategory.tensorUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] : C :=
  tensorUnit' (C := C)

open MonoidalCategory

-- mathport name: tensor_obj
/-- Notation for `tensorObj`, the tensor product of objects in a monoidal category -/
infixr:70 " ⊗ " => tensorObj

-- mathport name: tensor_hom
/-- Notation for `tensorHom`, the tensor product of morphisms in a monoidal category -/
infixr:70 " ⊗ " => tensorHom

-- mathport name: «expr𝟙_»
/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
notation "𝟙_" => tensorUnit

-- mathport name: exprα_
/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z) ≃ X ⊗ (Y ⊗ Z)` -/
notation "α_" => associator

-- mathport name: «exprλ_»
/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
notation "λ_" => leftUnitor

-- mathport name: exprρ_
/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
notation "ρ_" => rightUnitor

variable (C : Type u) [𝒞 : Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {C : Type u} {X Y X' Y' : C} [Category.{v} C] [MonoidalCategory.{v} C] (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⊗ g.inv
  hom_inv_id := by rw [← tensor_comp, Iso.hom_inv_id, Iso.hom_inv_id, ← tensor_id]
  inv_hom_id := by rw [← tensor_comp, Iso.inv_hom_id, Iso.inv_hom_id, ← tensor_id]
#align category_theory.tensor_iso CategoryTheory.tensorIso

-- mathport name: tensor_iso
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
  -- Porting note: Replaced `ext` with `aesop_cat_nonterminal`
  aesop_cat_nonterminal
  simp [← tensor_comp]
#align category_theory.monoidal_category.inv_tensor CategoryTheory.MonoidalCategory.inv_tensor

variable {U V W X Y Z : C}

theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ if h : P then g h else g' h) = if h : P then f ⊗ g h else f ⊗ g' h :=
  by split_ifs <;> rfl
#align category_theory.monoidal_category.tensor_dite CategoryTheory.MonoidalCategory.tensor_dite

theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ f = if h : P then g h ⊗ f else g' h ⊗ f :=
  by split_ifs <;> rfl
#align category_theory.monoidal_category.dite_tensor CategoryTheory.MonoidalCategory.dite_tensor

@[reassoc, simp]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.comp_tensor_id CategoryTheory.MonoidalCategory.comp_tensor_id

@[reassoc, simp]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.id_tensor_comp CategoryTheory.MonoidalCategory.id_tensor_comp

@[reassoc (attr := simp)]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.id_tensor_comp_tensor_id CategoryTheory.MonoidalCategory.id_tensor_comp_tensor_id

@[reassoc (attr := simp)]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.tensor_id_comp_id_tensor CategoryTheory.MonoidalCategory.tensor_id_comp_id_tensor

@[simp]
theorem rightUnitor_conjugation {X Y : C} (f : X ⟶ Y) :
    f ⊗ 𝟙 (𝟙_ C) = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

#align category_theory.monoidal_category.right_unitor_conjugation CategoryTheory.MonoidalCategory.rightUnitor_conjugation

@[simp]
theorem leftUnitor_conjugation {X Y : C} (f : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = (λ_ X).hom ≫ f ≫ (λ_ Y).inv
  := by rw [← leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

#align category_theory.monoidal_category.left_unitor_conjugation CategoryTheory.MonoidalCategory.leftUnitor_conjugation

@[reassoc]
theorem leftUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) := by simp
#align category_theory.monoidal_category.left_unitor_inv_naturality CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality

@[reassoc]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) := by simp
#align category_theory.monoidal_category.right_unitor_inv_naturality CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality

theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by simp
#align category_theory.monoidal_category.tensor_left_iff CategoryTheory.MonoidalCategory.tensor_left_iff

theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by simp
#align category_theory.monoidal_category.tensor_right_iff CategoryTheory.MonoidalCategory.tensor_right_iff

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/


section

@[reassoc]
theorem pentagon_inv (W X Y Z : C) :
    (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  CategoryTheory.eq_of_inv_eq_inv (by simp [pentagon])
#align category_theory.monoidal_category.pentagon_inv CategoryTheory.MonoidalCategory.pentagon_inv

@[reassoc, simp]
theorem rightUnitor_tensor (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ (𝟙 X ⊗ (ρ_ Y).hom) := by
  rw [← tensor_right_iff, comp_tensor_id, ← cancel_mono (α_ X Y (𝟙_ C)).hom, assoc,
    associator_naturality, ← triangle_assoc, ← triangle, id_tensor_comp, pentagon_assoc, ←
    associator_naturality, tensor_id]
#align category_theory.monoidal_category.right_unitor_tensor CategoryTheory.MonoidalCategory.rightUnitor_tensor

@[reassoc, simp]
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = (𝟙 X ⊗ (ρ_ Y).inv) ≫ (α_ X Y (𝟙_ C)).inv :=
  eq_of_inv_eq_inv (by simp)
#align category_theory.monoidal_category.right_unitor_tensor_inv CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ⊗ 𝟙 Y) = 𝟙 X ⊗ (λ_ Y).hom := by
  rw [← triangle, Iso.inv_hom_id_assoc]
#align category_theory.monoidal_category.triangle_assoc_comp_right CategoryTheory.MonoidalCategory.triangle_assoc_comp_right

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y :=
  by
  apply (cancel_mono ((ρ_ X).hom ⊗ 𝟙 Y)).1
  simp only [triangle_assoc_comp_right, assoc]
  rw [← id_tensor_comp, Iso.inv_hom_id, ← comp_tensor_id, Iso.inv_hom_id]
#align category_theory.monoidal_category.triangle_assoc_comp_left_inv CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv

end

@[reassoc]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
  by
  rw [comp_inv_eq, assoc, associator_naturality]
  simp
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

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ h) := by
  rw [← tensor_id, associator_naturality]
#align category_theory.monoidal_category.id_tensor_associator_naturality CategoryTheory.MonoidalCategory.id_tensor_associator_naturality

@[reassoc]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) := by
  rw [← tensor_id, associator_inv_naturality]
#align category_theory.monoidal_category.id_tensor_associator_inv_naturality CategoryTheory.MonoidalCategory.id_tensor_associator_inv_naturality

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⊗ g) ≫ (f.inv ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, f.hom_inv_id, id_tensor_comp]
#align category_theory.monoidal_category.hom_inv_id_tensor CategoryTheory.MonoidalCategory.hom_inv_id_tensor

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.hom ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, f.inv_hom_id, id_tensor_comp]
#align category_theory.monoidal_category.inv_hom_id_tensor CategoryTheory.MonoidalCategory.inv_hom_id_tensor

@[reassoc (attr := simp)]
theorem tensorHom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.hom) ≫ (h ⊗ f.inv) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, f.hom_inv_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_hom_inv_id CategoryTheory.MonoidalCategory.tensorHom_inv_id

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.hom) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, f.inv_hom_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_inv_hom_id CategoryTheory.MonoidalCategory.tensor_inv_hom_id

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ g) ≫ (inv f ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, IsIso.hom_inv_id, id_tensor_comp]
#align category_theory.monoidal_category.hom_inv_id_tensor' CategoryTheory.MonoidalCategory.hom_inv_id_tensor'

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ g) ≫ (f ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, IsIso.inv_hom_id, id_tensor_comp]
#align category_theory.monoidal_category.inv_hom_id_tensor' CategoryTheory.MonoidalCategory.inv_hom_id_tensor'

@[reassoc (attr := simp)]
theorem tensorHom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f) ≫ (h ⊗ inv f) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, IsIso.hom_inv_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_hom_inv_id' CategoryTheory.MonoidalCategory.tensorHom_inv_id'

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ inv f) ≫ (h ⊗ f) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, IsIso.inv_hom_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_inv_hom_id' CategoryTheory.MonoidalCategory.tensor_inv_hom_id'

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

/-- The tensor product expressed as a functor. -/
@[simps]
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ f.2
#align category_theory.monoidal_category.tensor CategoryTheory.MonoidalCategory.tensor

/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C
    where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ f.2.1) ⊗ f.2.2
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
#align category_theory.monoidal_category.right_assoc_tensor CategoryTheory.MonoidalCategory.rightAssocTensor

@[simp]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl
#align category_theory.monoidal_category.right_assoc_tensor_obj CategoryTheory.MonoidalCategory.rightAssocTensor_obj

@[simp]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl
#align category_theory.monoidal_category.right_assoc_tensor_map CategoryTheory.MonoidalCategory.rightAssocTensor_map

/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensorUnitLeft : C ⥤ C where
  obj X := 𝟙_ C ⊗ X
  map {X Y : C} (f : X ⟶ Y) := 𝟙 (𝟙_ C) ⊗ f
#align category_theory.monoidal_category.tensor_unit_left CategoryTheory.MonoidalCategory.tensorUnitLeft

/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensorUnitRight : C ⥤ C where
  obj X := X ⊗ 𝟙_ C
  map {X Y : C} (f : X ⟶ Y) := f ⊗ 𝟙 (𝟙_ C)
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
  map {Y} {Y'} f := 𝟙 X ⊗ f
#align category_theory.monoidal_category.tensor_left CategoryTheory.MonoidalCategory.tensorLeft

/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f =>
    by
    dsimp
    rw [← tensor_id]
    apply associator_naturality
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
  map {Y} {Y'} f := f ⊗ 𝟙 X
#align category_theory.monoidal_category.tensor_right CategoryTheory.MonoidalCategory.tensorRight

-- Porting Note: This used to be `variable (C)` but it seems like Lean 4 parses that differently
variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is a op-monoidal functor.
-/
@[simps]
def tensoringLeft : C ⥤ C ⥤ C where
  obj := tensorLeft
  map {X} {Y} f := { app := fun Z => f ⊗ 𝟙 Z }
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
  map {X} {Y} f := { app := fun Z => 𝟙 Z ⊗ f }
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
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f =>
    by
    dsimp
    rw [← tensor_id]
    apply associator_inv_naturality
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

@[simps! tensorObj tensorHom tensorUnit' associator]
instance prodMonoidal : MonoidalCategory (C₁ × C₂) where
  tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom f g := (f.1 ⊗ g.1, f.2 ⊗ g.2)
  tensorUnit' := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)
#align category_theory.monoidal_category.prod_monoidal CategoryTheory.MonoidalCategory.prodMonoidal

@[simp]
theorem prodMonoidal_leftUnitor_hom_fst (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).1 = (λ_ X.1).hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_hom_fst CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_fst

@[simp]
theorem prodMonoidal_leftUnitor_hom_snd (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).2 = (λ_ X.2).hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_hom_snd CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_snd

@[simp]
theorem prodMonoidal_leftUnitor_inv_fst (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).1 = (λ_ X.1).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_inv_fst CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_fst

@[simp]
theorem prodMonoidal_leftUnitor_inv_snd (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).2 = (λ_ X.2).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_inv_snd CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_snd

@[simp]
theorem prodMonoidal_rightUnitor_hom_fst (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).1 = (ρ_ X.1).hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_hom_fst CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_fst

@[simp]
theorem prodMonoidal_rightUnitor_hom_snd (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).2 = (ρ_ X.2).hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_hom_snd CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_snd

@[simp]
theorem prodMonoidal_rightUnitor_inv_fst (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).1 = (ρ_ X.1).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_inv_fst CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_fst

@[simp]
theorem prodMonoidal_rightUnitor_inv_snd (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).2 = (ρ_ X.2).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_inv_snd CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_snd

end

end MonoidalCategory

end CategoryTheory

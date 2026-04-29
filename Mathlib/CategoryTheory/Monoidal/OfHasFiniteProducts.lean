/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way
is sometimes called a (co-)Cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## TODO

Once we have cocartesian-monoidal categories, replace `monoidalOfHasFiniteCoproducts` and
`symmetricOfHasFiniteCoproducts` with `CocartesianMonoidalCategory.ofHasFiniteCoproducts`.
-/

@[expose] public section


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
@[instance_reducible,
  deprecated CartesianMonoidalCategory.ofHasFiniteProducts (since := "2025-10-19")]
def monoidalOfHasFiniteProducts [HasTerminal C] [HasBinaryProducts C] : MonoidalCategory C :=
  have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  let +nondep : CartesianMonoidalCategory C := .ofHasFiniteProducts
  inferInstance

end

namespace monoidalOfHasFiniteProducts

variable [HasTerminal C] [HasBinaryProducts C]

attribute [local instance] monoidalOfHasFiniteProducts

open scoped MonoidalCategory

@[deprecated CartesianMonoidalCategory.toUnit_unique (since := "2025-10-19")]
theorem unit_ext {X : C} (f g : X ⟶ 𝟙_ C) : f = g := terminal.hom_ext f g

@[deprecated CartesianMonoidalCategory.hom_ext (since := "2025-10-19")]
theorem tensor_ext {X Y Z : C} (f g : X ⟶ Y ⊗ Z)
    (w₁ : f ≫ prod.fst = g ≫ prod.fst) (w₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  Limits.prod.hom_ext w₁ w₂

@[deprecated "This is an implementation detail." (since := "2025-10-19"), simp]
theorem tensorUnit : 𝟙_ C = ⊤_ C := rfl

@[deprecated "This is an implementation detail." (since := "2025-10-19"), simp]
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨯ Y) :=
  rfl

@[deprecated CartesianMonoidalCategory.leftUnitor_hom (since := "2025-10-19"), simp]
theorem leftUnitor_hom (X : C) : (λ_ X).hom = Limits.prod.snd :=
  rfl

@[deprecated CartesianMonoidalCategory.rightUnitor_hom (since := "2025-10-19"), simp]
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = Limits.prod.fst :=
  rfl

@[deprecated "Use the `CartesianMonoidalCategory.associator_hom_...` lemmas"
  (since := "2025-10-19"), simp]
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      prod.lift (Limits.prod.fst ≫ Limits.prod.fst)
        (prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd) :=
  rfl

@[deprecated "Use the `CartesianMonoidalCategory.associator_inv_...` lemmas"
  (since := "2025-10-19")]
theorem associator_inv (X Y Z : C) :
    (α_ X Y Z).inv =
      prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated CartesianMonoidalCategory.associator_hom_fst (since := "2025-10-19")]
theorem associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ prod.fst = prod.fst ≫ prod.fst := by simp [associator_hom]

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated CartesianMonoidalCategory.associator_hom_snd_fst (since := "2025-10-19")]
theorem associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ prod.snd ≫ prod.fst = prod.fst ≫ prod.snd := by simp [associator_hom]

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated CartesianMonoidalCategory.associator_hom_snd_snd (since := "2025-10-19")]
theorem associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ prod.snd ≫ prod.snd = prod.snd := by simp [associator_hom]

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated CartesianMonoidalCategory.associator_inv_fst_fst (since := "2025-10-19")]
theorem associator_inv_fst_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ prod.fst ≫ prod.fst = prod.fst := by simp [associator_inv]

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated CartesianMonoidalCategory.associator_inv_fst_snd (since := "2025-10-19")]
theorem associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ prod.fst ≫ prod.snd = prod.snd ≫ prod.fst := by simp [associator_inv]

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated CartesianMonoidalCategory.associator_inv_snd (since := "2025-10-19")]
theorem associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ prod.snd = prod.snd ≫ prod.snd := by simp [associator_inv]

end monoidalOfHasFiniteProducts

section

attribute [local instance] monoidalOfHasFiniteProducts

open MonoidalCategory

set_option linter.deprecated false in
/-- The monoidal structure coming from finite products is symmetric.
-/
@[deprecated CartesianMonoidalCategory.toSymmetricCategory (since := "2025-10-19"), simps!,
  implicit_reducible]
def symmetricOfHasFiniteProducts [HasTerminal C] [HasBinaryProducts C] : SymmetricCategory C :=
  have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  let : CartesianMonoidalCategory C := .ofHasFiniteProducts
  let +nondep : BraidedCategory C := .ofCartesianMonoidalCategory
  inferInstance

end

section

#adaptation_note /-- prior to nightly-2026-02-05
these four fields were provided by the auto_param -/
/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
@[instance_reducible]
def monoidalOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : MonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y ↦ X ⨿ Y
    whiskerLeft := fun _ _ _ g ↦ Limits.coprod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ ↦ Limits.coprod.map f (𝟙 _)
    tensorHom := fun f g ↦ Limits.coprod.map f g
    tensorUnit := ⊥_ C
    associator := coprod.associator
    leftUnitor := coprod.leftUnitor
    rightUnitor := coprod.rightUnitor
  }
  .ofTensorHom
    (pentagon := coprod.pentagon)
    (triangle := coprod.triangle)
    (associator_naturality := @coprod.associator_naturality _ _ _)
    (id_tensorHom_id := fun _ _ => coprod.map_id_id)
    (tensorHom_comp_tensorHom := coprod.map_map)
    (leftUnitor_naturality := coprod.leftUnitor_naturality)
    (rightUnitor_naturality := coprod.rightUnitor_naturality)

end

namespace monoidalOfHasFiniteCoproducts

variable [HasInitial C] [HasBinaryCoproducts C]

attribute [local instance] monoidalOfHasFiniteCoproducts

open scoped MonoidalCategory

@[simp]
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨿ Y) :=
  rfl

@[simp]
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ₘ g = Limits.coprod.map f g :=
  rfl

@[simp]
theorem whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f = Limits.coprod.map (𝟙 X) f :=
  rfl

@[simp]
theorem whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = Limits.coprod.map f (𝟙 Z) :=
  rfl

@[simp]
theorem leftUnitor_hom (X : C) : (λ_ X).hom = coprod.desc (initial.to X) (𝟙 _) :=
  rfl

@[simp]
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) :=
  rfl

@[simp]
theorem leftUnitor_inv (X : C) : (λ_ X).inv = Limits.coprod.inr :=
  rfl

@[simp]
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = Limits.coprod.inl :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right-hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr) :=
  rfl

theorem associator_inv (X Y Z : C) :
    (α_ X Y Z).inv =
      coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) :=
  rfl

end monoidalOfHasFiniteCoproducts

section

attribute [local instance] monoidalOfHasFiniteCoproducts

open MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps, implicit_reducible]
def symmetricOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] :
    SymmetricCategory C where
  braiding := Limits.coprod.braiding
  braiding_naturality_left f g := by simp
  braiding_naturality_right f g := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_inv]; simp
  symmetry X Y := by simp

end

namespace monoidalOfHasFiniteProducts

variable {C}
variable {D : Type*} [Category* D] (F : C ⥤ D)
  [HasTerminal C] [HasBinaryProducts C]
  [HasTerminal D] [HasBinaryProducts D]

set_option linter.deprecated false in
attribute [local simp] associator_hom_fst
@[deprecated Functor.OplaxMonoidal.ofChosenFiniteProducts (since := "2025-10-19")]
instance :
    have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
    have : HasFiniteProducts D := hasFiniteProducts_of_has_binary_and_terminal
    let : CartesianMonoidalCategory C := .ofHasFiniteProducts
    let : CartesianMonoidalCategory D := .ofHasFiniteProducts
    F.OplaxMonoidal := by extract_lets; exact .ofChosenFiniteProducts F

open Functor.OplaxMonoidal

@[deprecated "No replacement" (since := "2025-10-19")]
lemma η_eq :
    have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
    have : HasFiniteProducts D := hasFiniteProducts_of_has_binary_and_terminal
    let : CartesianMonoidalCategory C := .ofHasFiniteProducts
    let : CartesianMonoidalCategory D := .ofHasFiniteProducts
    η F = terminalComparison F := rfl

@[deprecated "No replacement" (since := "2025-10-19")]
lemma δ_eq (X Y : C) :
    have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
    have : HasFiniteProducts D := hasFiniteProducts_of_has_binary_and_terminal
    let : CartesianMonoidalCategory C := .ofHasFiniteProducts
    let : CartesianMonoidalCategory D := .ofHasFiniteProducts
    δ F X Y = prodComparison F X Y := rfl

variable [PreservesLimit (Functor.empty.{0} C) F]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]

set_option backward.defeqAttrib.useBackward true in
set_option linter.deprecated false in
@[deprecated inferInstance (since := "2025-10-19")]
instance :
    have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
    have : HasFiniteProducts D := hasFiniteProducts_of_has_binary_and_terminal
    let : CartesianMonoidalCategory C := .ofHasFiniteProducts
    let : CartesianMonoidalCategory D := .ofHasFiniteProducts
    IsIso (η F) := by dsimp [η_eq]; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option linter.deprecated false in
@[deprecated inferInstance (since := "2025-10-19")]
instance (X Y : C) :
    have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
    have : HasFiniteProducts D := hasFiniteProducts_of_has_binary_and_terminal
    let : CartesianMonoidalCategory C := .ofHasFiniteProducts
    let : CartesianMonoidalCategory D := .ofHasFiniteProducts
    IsIso (δ F X Y) := by dsimp [δ_eq]; infer_instance

/-- Promote a functor that preserves finite products to a monoidal functor between
categories equipped with the monoidal category structure given by finite products. -/
@[deprecated Functor.Monoidal.ofChosenFiniteProducts (since := "2025-10-19")]
instance :
    have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
    have : HasFiniteProducts D := hasFiniteProducts_of_has_binary_and_terminal
    let : CartesianMonoidalCategory C := .ofHasFiniteProducts
    let : CartesianMonoidalCategory D := .ofHasFiniteProducts
    F.Monoidal := by extract_lets; exact .ofOplaxMonoidal F

end monoidalOfHasFiniteProducts

end CategoryTheory

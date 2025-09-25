/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.Tactic.ApplyFun

/-!
# Rigid (autonomous) monoidal categories

This file defines rigid (autonomous) monoidal categories and the necessary theory about
exact pairings and duals.

## Main definitions

* `ExactPairing` of two objects of a monoidal category
* Type classes `HasLeftDual` and `HasRightDual` that capture that a pairing exists
* The `rightAdjointMate f` as a morphism `fᘁ : Yᘁ ⟶ Xᘁ` for a morphism `f : X ⟶ Y`
* The classes of `RightRigidCategory`, `LeftRigidCategory` and `RigidCategory`

## Main statements

* `comp_rightAdjointMate`: The adjoint mates of the composition is the composition of
  adjoint mates.

## Notation

* `η_` and `ε_` denote the coevaluation and evaluation morphism of an exact pairing.
* `Xᘁ` and `ᘁX` denote the right and left dual of an object, as well as the adjoint
  mate of a morphism.

## Future work

* Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.
* Show that the left adjoint mate of the right adjoint mate of a morphism is the morphism itself.
* Simplify constructions in the case where a symmetry or braiding is present.
* Show that `ᘁ` gives an equivalence of categories `C ≅ (Cᵒᵖ)ᴹᵒᵖ`.
* Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).

## Notes

Although we construct the adjunction `tensorLeft Y ⊣ tensorLeft X` from `ExactPairing X Y`,
this is not a bijective correspondence.
I think the correct statement is that `tensorLeft Y` and `tensorLeft X` are
module endofunctors of `C` as a right `C` module category,
and `ExactPairing X Y` is in bijection with adjunctions compatible with this right `C` action.

## References

* <https://ncatlab.org/nlab/show/rigid+monoidal+category>

## Tags

rigid category, monoidal category

-/


open CategoryTheory MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class ExactPairing (X Y : C) where
  /-- Coevaluation of an exact pairing.

  Do not use directly. Use `ExactPairing.coevaluation` instead. -/
  coevaluation' : 𝟙_ C ⟶ X ⊗ Y
  /-- Evaluation of an exact pairing.

  Do not use directly. Use `ExactPairing.evaluation` instead. -/
  evaluation' : Y ⊗ X ⟶ 𝟙_ C
  coevaluation_evaluation' :
    Y ◁ coevaluation' ≫ (α_ _ _ _).inv ≫ evaluation' ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv := by
    cat_disch
  evaluation_coevaluation' :
    coevaluation' ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ evaluation' = (λ_ X).hom ≫ (ρ_ X).inv := by
    cat_disch

namespace ExactPairing

-- Porting note: as there is no mechanism equivalent to `[]` in Lean 3 to make
-- arguments for class fields explicit,
-- we now repeat all the fields without primes.
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Making.20variable.20in.20class.20field.20explicit
variable (X Y : C)
variable [ExactPairing X Y]

/-- Coevaluation of an exact pairing. -/
def coevaluation : 𝟙_ C ⟶ X ⊗ Y := @coevaluation' _ _ _ X Y _

/-- Evaluation of an exact pairing. -/
def evaluation : Y ⊗ X ⟶ 𝟙_ C := @evaluation' _ _ _ X Y _

@[inherit_doc] notation "η_" => ExactPairing.coevaluation
@[inherit_doc] notation "ε_" => ExactPairing.evaluation

lemma coevaluation_evaluation :
    Y ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ ε_ X _ ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv :=
  coevaluation_evaluation'

lemma evaluation_coevaluation :
    η_ _ _ ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε_ _ Y = (λ_ X).hom ≫ (ρ_ X).inv :=
  evaluation_coevaluation'

lemma coevaluation_evaluation'' :
    Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y = ⊗𝟙.hom := by
  convert coevaluation_evaluation X Y <;> simp [monoidalComp]

lemma evaluation_coevaluation'' :
    η_ X Y ▷ X ⊗≫ X ◁ ε_ X Y = ⊗𝟙.hom := by
  convert evaluation_coevaluation X Y <;> simp [monoidalComp]

end ExactPairing

attribute [reassoc (attr := simp)] ExactPairing.coevaluation_evaluation
attribute [reassoc (attr := simp)] ExactPairing.evaluation_coevaluation

instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation' := (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by monoidal_coherence
  evaluation_coevaluation' := by monoidal_coherence

/-- A class of objects which have a right dual. -/
class HasRightDual (X : C) where
  /-- The right dual of the object `X`. -/
  rightDual : C
  [exact : ExactPairing X rightDual]

/-- A class of objects which have a left dual. -/
class HasLeftDual (Y : C) where
  /-- The left dual of the object `X`. -/
  leftDual : C
  [exact : ExactPairing leftDual Y]

attribute [instance] HasRightDual.exact
attribute [instance] HasLeftDual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

#adaptation_note /-- https://github.com/leanprover/lean4/pull/4596
The overlapping notation for `leftDual` and `leftAdjointMate` become more problematic in
after https://github.com/leanprover/lean4/pull/4596, and we sometimes have to disambiguate with
e.g. `(ᘁX : C)` where previously just `ᘁX` was enough. -/

@[inherit_doc] prefix:1024 "ᘁ" => leftDual
@[inherit_doc] postfix:1024 "ᘁ" => rightDual

instance hasRightDualUnit : HasRightDual (𝟙_ C) where
  rightDual := 𝟙_ C

instance hasLeftDualUnit : HasLeftDual (𝟙_ C) where
  leftDual := 𝟙_ C

instance hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where
  rightDual := X

instance hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where
  leftDual := X

@[simp]
theorem leftDual_rightDual {X : C} [HasRightDual X] : ᘁXᘁ = X :=
  rfl

@[simp]
theorem rightDual_leftDual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X :=
  rfl

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (λ_ _).hom

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (λ_ _).inv ≫ η_ (ᘁX) X ▷ _ ≫ (_ ◁ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f
@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

@[simp]
theorem rightAdjointMate_id {X : C} [HasRightDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ) := by
  simp [rightAdjointMate]

@[simp]
theorem leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX) := by
  simp [leftAdjointMate]

theorem rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
    {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g =
      (ρ_ (Yᘁ)).inv ≫
        _ ◁ η_ X (Xᘁ) ≫ _ ◁ (f ⊗ₘ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ ε_ Y (Yᘁ) ▷ _ ≫ (λ_ Z).hom :=
  calc
    _ = 𝟙 _ ⊗≫ (Yᘁ : C) ◁ η_ X Xᘁ ≫ Yᘁ ◁ f ▷ Xᘁ ⊗≫ (ε_ Y Yᘁ ▷ Xᘁ ≫ 𝟙_ C ◁ g) ⊗≫ 𝟙 _ := by
      dsimp only [rightAdjointMate]; monoidal
    _ = _ := by
      rw [← whisker_exchange, tensorHom_def]; monoidal

theorem leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
    {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g =
      (λ_ _).inv ≫
        η_ (ᘁX : C) X ▷ _ ≫ (g ⊗ₘ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom :=
  calc
    _ = 𝟙 _ ⊗≫ η_ (ᘁX : C) X ▷ (ᘁY) ⊗≫ (ᘁX) ◁ f ▷ (ᘁY) ⊗≫ ((ᘁX) ◁ ε_ (ᘁY) Y ≫ g ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
      dsimp only [leftAdjointMate]; monoidal
    _ = _ := by
      rw [whisker_exchange, tensorHom_def']; monoidal

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_rightAdjointMate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ := by
  rw [rightAdjointMate_comp]
  simp only [rightAdjointMate, comp_whiskerRight]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]; congr 2
  symm
  calc
    _ = 𝟙 _ ⊗≫ (η_ Y Yᘁ ▷ 𝟙_ C ≫ (Y ⊗ Yᘁ) ◁ η_ X Xᘁ) ⊗≫ Y ◁ Yᘁ ◁ f ▷ Xᘁ ⊗≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [tensorHom_def']; monoidal
    _ = η_ X Xᘁ ⊗≫ (η_ Y Yᘁ ▷ (X ⊗ Xᘁ) ≫ (Y ⊗ Yᘁ) ◁ f ▷ Xᘁ) ⊗≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ X Xᘁ ⊗≫ f ▷ Xᘁ ⊗≫ (η_ Y Yᘁ ▷ Y ⊗≫ Y ◁ ε_ Y Yᘁ) ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ g ▷ Xᘁ := by
      rw [evaluation_coevaluation'']; monoidal

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_leftAdjointMate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf := by
  rw [leftAdjointMate_comp]
  simp only [leftAdjointMate, MonoidalCategory.whiskerLeft_comp]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← comp_whiskerRight]; congr 2
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((𝟙_ C) ◁ η_ (ᘁY) Y ≫ η_ (ᘁX) X ▷ ((ᘁY) ⊗ Y)) ⊗≫ (ᘁX) ◁ f ▷ (ᘁY) ▷ Y ⊗≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y ⊗≫ (ᘁX) ◁ g := by
      rw [tensorHom_def]; monoidal
    _ = η_ (ᘁX) X ⊗≫ (((ᘁX) ⊗ X) ◁ η_ (ᘁY) Y ≫ ((ᘁX) ◁ f) ▷ ((ᘁY) ⊗ Y)) ⊗≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y ⊗≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; monoidal
    _ = η_ (ᘁX) X ⊗≫ ((ᘁX) ◁ f) ⊗≫ (ᘁX) ◁ (Y ◁ η_ (ᘁY) Y ⊗≫ ε_ (ᘁY) Y ▷ Y) ⊗≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; monoidal
    _ = η_ (ᘁX) X ≫ (ᘁX) ◁ f ≫ (ᘁX) ◁ g := by
      rw [coevaluation_evaluation'']; monoidal

/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
by "pulling the string on the left" up or down.

This gives the adjunction `tensorLeftAdjunction Y Y' : tensorLeft Y' ⊣ tensorLeft Y`.

This adjunction is often referred to as "Frobenius reciprocity" in the
fusion categories / planar algebras / subfactors literature.
-/
def tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z) where
  toFun f := (λ_ _).inv ≫ η_ _ _ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ f
  invFun f := Y' ◁ f ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (λ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ Y' ◁ η_ Y Y' ▷ X ⊗≫ ((Y' ⊗ Y) ◁ f ≫ ε_ Y Y' ▷ Z) ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ▷ X ⊗≫ f := by
        rw [whisker_exchange]; monoidal
      _ = f := by
        rw [coevaluation_evaluation'']; monoidal
  right_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ (η_ Y Y' ▷ X ≫ (Y ⊗ Y') ◁ f) ⊗≫ Y ◁ ε_ Y Y' ▷ Z ⊗≫ 𝟙 _ := by
        monoidal
      _ = f ⊗≫ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ▷ Z ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = f := by
        rw [evaluation_coevaluation'']; monoidal

/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')`
by "pulling the string on the right" up or down.
-/
def tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y') where
  toFun f := (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _
  invFun f := f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ X ◁ η_ Y Y' ▷ Y ⊗≫ (f ▷ (Y' ⊗ Y) ≫ Z ◁ ε_ Y Y') ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ X ◁ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ f := by
        rw [← whisker_exchange]; monoidal
      _ = f := by
        rw [evaluation_coevaluation'']; monoidal
  right_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ (X ◁ η_ Y Y' ≫ f ▷ (Y ⊗ Y')) ⊗≫ Z ◁ ε_ Y Y' ▷ Y' ⊗≫ 𝟙 _ := by
        monoidal
      _ = f ⊗≫ Z ◁ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = f := by
        rw [coevaluation_evaluation'']; monoidal

theorem tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g := by
  simp [tensorLeftHomEquiv]

theorem tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      _ ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g := by
  simp [tensorLeftHomEquiv]

theorem tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y' := by
  simp [tensorRightHomEquiv]

theorem tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g := by
  simp [tensorRightHomEquiv]

/-- If `Y Y'` have an exact pairing,
then the functor `tensorLeft Y'` is left adjoint to `tensorLeft Y`.
-/
def tensorLeftAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorLeft Y' ⊣ tensorLeft Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorLeftHomEquiv_naturality f g }

/-- If `Y Y'` have an exact pairing,
then the functor `tensor_right Y` is left adjoint to `tensor_right Y'`.
-/
def tensorRightAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorRight Y ⊣ tensorRight Y' :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorRightHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorRightHomEquiv_naturality f g }

/--
If `Y` has a left dual `ᘁY`, then it is a closed object, with the internal hom functor `Y ⟶[C] -`
given by left tensoring by `ᘁY`.
This has to be a definition rather than an instance to avoid diamonds, for example between
`category_theory.monoidal_closed.functor_closed` and
`CategoryTheory.Monoidal.functorHasLeftDual`. Moreover, in concrete applications there is often
a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the closed
structure shouldn't come from `has_left_dual` (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic).
-/
def closedOfHasLeftDual (Y : C) [HasLeftDual Y] : Closed Y where
  rightAdj := tensorLeft (ᘁY)
  adj := tensorLeftAdjunction (ᘁY) Y

/-- `tensorLeftHomEquiv` commutes with tensoring on the right -/
theorem tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y ⊗ Z)
    (g : X' ⟶ Z') :
    (tensorLeftHomEquiv (X ⊗ X') Y Y' (Z ⊗ Z')).symm ((f ⊗ₘ g) ≫ (α_ _ _ _).hom) =
      (α_ _ _ _).inv ≫ ((tensorLeftHomEquiv X Y Y' Z).symm f ⊗ₘ g) := by
  simp [tensorLeftHomEquiv, tensorHom_def']

/-- `tensorRightHomEquiv` commutes with tensoring on the left -/
theorem tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z ⊗ Y')
    (g : X' ⟶ Z') :
    (tensorRightHomEquiv (X' ⊗ X) Y Y' (Z' ⊗ Z)).symm ((g ⊗ₘ f) ≫ (α_ _ _ _).inv) =
      (α_ _ _ _).hom ≫ (g ⊗ₘ (tensorRightHomEquiv X Y Y' Z).symm f) := by
  simp [tensorRightHomEquiv, tensorHom_def]

@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ Y ◁ f) = (ρ_ _).hom ≫ f := by
  calc
    _ = Y' ◁ η_ Y Y' ⊗≫ ((Y' ⊗ Y) ◁ f ≫ ε_ Y Y' ▷ Z) ⊗≫ 𝟙 _ := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ⊗≫ f := by
      rw [whisker_exchange]; monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight {X Y : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) :
    (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ f ▷ (Xᘁ)) = (ρ_ _).hom ≫ fᘁ := by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  simp

@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft {X Y : C} [HasLeftDual X]
    [HasLeftDual Y] (f : X ⟶ Y) :
    (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (ᘁX : C) X ≫ (ᘁX : C) ◁ f) = (λ_ _).hom ≫ ᘁf := by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  simp

@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ f ▷ Y') = (λ_ _).hom ≫ f :=
  calc
    _ = η_ Y Y' ▷ Y ⊗≫ (f ▷ (Y' ⊗ Y) ≫ Z ◁ ε_ Y Y') ⊗≫ 𝟙 _ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ f := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

@[simp]
theorem tensorLeftHomEquiv_whiskerLeft_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) :
    (tensorLeftHomEquiv _ _ _ _) (Z ◁ f ≫ ε_ _ _) = f ≫ (ρ_ _).inv :=
  calc
    _ = 𝟙 _ ⊗≫ (η_ (ᘁZ : C) Z ▷ Y ≫ ((ᘁZ) ⊗ Z) ◁ f) ⊗≫ (ᘁZ) ◁ ε_ (ᘁZ) Z := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = f ⊗≫ (η_ (ᘁZ) Z ▷ (ᘁZ) ⊗≫ (ᘁZ) ◁ ε_ (ᘁZ) Z) := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

@[simp]
theorem tensorLeftHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) (f ▷ _ ≫ ε_ _ _) = (ᘁf) ≫ (ρ_ _).inv := by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  simp

@[simp]
theorem tensorRightHomEquiv_whiskerLeft_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((Yᘁ : C) ◁ f ≫ ε_ _ _) = fᘁ ≫ (λ_ _).inv := by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  simp

@[simp]
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ) :
    (tensorRightHomEquiv _ _ _ _) (f ▷ X ≫ ε_ X (Xᘁ)) = f ≫ (λ_ _).inv :=
  calc
    _ = 𝟙 _ ⊗≫ (Y ◁ η_ X Xᘁ ≫ f ▷ (X ⊗ Xᘁ)) ⊗≫ ε_ X Xᘁ ▷ Xᘁ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = f ⊗≫ (Xᘁ ◁ η_ X Xᘁ ⊗≫ ε_ X Xᘁ ▷ Xᘁ) := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [coevaluation_evaluation'']; monoidal

-- Next four lemmas passing `fᘁ` or `ᘁf` through (co)evaluations.
@[reassoc]
theorem coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ _ ◁ (fᘁ) = η_ _ _ ≫ f ▷ _ := by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp

@[reassoc]
theorem leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    X ◁ (ᘁf) ≫ ε_ _ _ = f ▷ _ ≫ ε_ _ _ := by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp

@[reassoc]
theorem coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ (ᘁf) ▷ Y = η_ (ᘁX) X ≫ (ᘁX) ◁ f := by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp

@[reassoc]
theorem rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ▷ X) ≫ ε_ X (Xᘁ) = ((Yᘁ) ◁ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp

/-- Transport an exact pairing across an isomorphism in the first argument. -/
def exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : ExactPairing X Y where
  evaluation' := Y ◁ i.hom ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ i.inv ▷ Y
  evaluation_coevaluation' :=
    calc
      _ = η_ X' Y ▷ X ⊗≫ (i.inv ▷ (Y ⊗ X) ≫ X ◁ (Y ◁ i.hom)) ⊗≫ X ◁ ε_ X' Y := by
        monoidal
      _ = 𝟙 _ ⊗≫ (η_ X' Y ▷ X ≫ (X' ⊗ Y) ◁ i.hom) ⊗≫
          (i.inv ▷ (Y ⊗ X') ≫ X ◁ ε_ X' Y) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ i.hom ⊗≫ (η_ X' Y ▷ X' ⊗≫ X' ◁ ε_ X' Y) ⊗≫ i.inv ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, ← whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ (i.hom ≫ i.inv) ⊗≫ 𝟙 _ := by
        rw [evaluation_coevaluation'']; monoidal
      _ = (λ_ X).hom ≫ (ρ_ X).inv := by
        rw [Iso.hom_inv_id]
        monoidal
  coevaluation_evaluation' := by
    calc
      _ = Y ◁ η_ X' Y ≫ Y ◁ (i.inv ≫ i.hom) ▷ Y ⊗≫ ε_ X' Y ▷ Y := by
        monoidal
      _ = Y ◁ η_ X' Y ⊗≫ ε_ X' Y ▷ Y := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
        rw [coevaluation_evaluation'']
        simp

/-- Transport an exact pairing across an isomorphism in the second argument. -/
def exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : ExactPairing X Y where
  evaluation' := i.hom ▷ X ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ X ◁ i.inv
  evaluation_coevaluation' := by
    calc
      _ = η_ X Y' ▷ X ⊗≫ X ◁ (i.inv ≫ i.hom) ▷ X ≫ X ◁ ε_ X Y' := by
        monoidal
      _ = η_ X Y' ▷ X ⊗≫ X ◁ ε_ X Y' := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
        rw [evaluation_coevaluation'']
        simp
  coevaluation_evaluation' :=
    calc
      _ = Y ◁ η_ X Y' ⊗≫ (Y ◁ (X ◁ i.inv) ≫ i.hom ▷ (X ⊗ Y)) ⊗≫ ε_ X Y' ▷ Y := by
        monoidal
      _ = 𝟙 _ ⊗≫ (Y ◁ η_ X Y' ≫ i.hom ▷ (X ⊗ Y')) ⊗≫
          ((Y' ⊗ X) ◁ i.inv ≫ ε_ X Y' ▷ Y) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ i.hom ⊗≫ (Y' ◁ η_ X Y' ⊗≫ ε_ X Y' ▷ Y') ⊗≫ i.inv ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ (i.hom ≫ i.inv) ⊗≫ 𝟙 _ := by
        rw [coevaluation_evaluation'']; monoidal
      _ = (ρ_ Y).hom ≫ (λ_ Y).inv := by
        rw [Iso.hom_inv_id]
        monoidal

/-- Transport an exact pairing across isomorphisms. -/
def exactPairingCongr {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y') :
    ExactPairing X Y :=
  haveI : ExactPairing X' Y := exactPairingCongrRight j
  exactPairingCongrLeft i

/-- Right duals are isomorphic. -/
def rightDualIso {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) : Y₁ ≅ Y₂ where
  hom := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_rightAdjointMate, Category.comp_id, @rightAdjointMate_id]
    rfl
  inv_hom_id := by
    rw [← @comp_rightAdjointMate, Category.comp_id, @rightAdjointMate_id]
    rfl

/-- Left duals are isomorphic. -/
def leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ where
  hom := @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_leftAdjointMate C, Category.comp_id, @leftAdjointMate_id]
    rfl
  inv_hom_id := by
    rw [← @comp_leftAdjointMate C, Category.comp_id, @leftAdjointMate_id]
    rfl

@[simp]
theorem rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by
  ext
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id]

@[simp]
theorem leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by
  ext
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id]

/-- A right rigid monoidal category is one in which every object has a right dual. -/
class RightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [rightDual : ∀ X : C, HasRightDual X]

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : ∀ X : C, HasLeftDual X]

attribute [instance 100] RightRigidCategory.rightDual
attribute [instance 100] LeftRigidCategory.leftDual

/-- Any left rigid category is monoidal closed, with the internal hom `X ⟶[C] Y = ᘁX ⊗ Y`.
This has to be a definition rather than an instance to avoid diamonds, for example between
`category_theory.monoidal_closed.functor_category` and
`CategoryTheory.Monoidal.leftRigidFunctorCategory`. Moreover, in concrete applications there is
often a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the monoidal
closed structure shouldn't come the rigid structure (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic). -/
def monoidalClosedOfLeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [LeftRigidCategory C] : MonoidalClosed C where
  closed X := closedOfHasLeftDual X

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class RigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    RightRigidCategory C, LeftRigidCategory C

end CategoryTheory

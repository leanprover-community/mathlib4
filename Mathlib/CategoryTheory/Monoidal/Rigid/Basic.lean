/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.Tactic.ApplyFun

#align_import category_theory.monoidal.rigid.basic from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

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

## Notations

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
    aesop_cat
  evaluation_coevaluation' :
    coevaluation' ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ evaluation' = (λ_ X).hom ≫ (ρ_ X).inv := by
    aesop_cat
#align category_theory.exact_pairing CategoryTheory.ExactPairing

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
    Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y = ⊗𝟙 := by
  convert coevaluation_evaluation X Y <;> simp [monoidalComp]

lemma evaluation_coevaluation'' :
    η_ X Y ▷ X ⊗≫ X ◁ ε_ X Y = ⊗𝟙 := by
  convert evaluation_coevaluation X Y <;> simp [monoidalComp]

end ExactPairing

attribute [reassoc (attr := simp)] ExactPairing.coevaluation_evaluation
attribute [reassoc (attr := simp)] ExactPairing.evaluation_coevaluation

instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation' := (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by rw [← id_tensorHom, ← tensorHom_id]; coherence
  evaluation_coevaluation' := by rw [← id_tensorHom, ← tensorHom_id]; coherence
#align category_theory.exact_pairing_unit CategoryTheory.exactPairingUnit

/-- A class of objects which have a right dual. -/
class HasRightDual (X : C) where
  /-- The right dual of the object `X`. -/
  rightDual : C
  [exact : ExactPairing X rightDual]
#align category_theory.has_right_dual CategoryTheory.HasRightDual

/-- A class of objects which have a left dual. -/
class HasLeftDual (Y : C) where
  /-- The left dual of the object `X`. -/
  leftDual : C
  [exact : ExactPairing leftDual Y]
#align category_theory.has_left_dual CategoryTheory.HasLeftDual

attribute [instance] HasRightDual.exact
attribute [instance] HasLeftDual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

@[inherit_doc] prefix:1024 "ᘁ" => leftDual
@[inherit_doc] postfix:1024 "ᘁ" => rightDual

instance hasRightDualUnit : HasRightDual (𝟙_ C) where
  rightDual := 𝟙_ C
#align category_theory.has_right_dual_unit CategoryTheory.hasRightDualUnit

instance hasLeftDualUnit : HasLeftDual (𝟙_ C) where
  leftDual := 𝟙_ C
#align category_theory.has_left_dual_unit CategoryTheory.hasLeftDualUnit

instance hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where
  rightDual := X
#align category_theory.has_right_dual_left_dual CategoryTheory.hasRightDualLeftDual

instance hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where
  leftDual := X
#align category_theory.has_left_dual_right_dual CategoryTheory.hasLeftDualRightDual

@[simp]
theorem leftDual_rightDual {X : C} [HasRightDual X] : ᘁXᘁ = X :=
  rfl
#align category_theory.left_dual_right_dual CategoryTheory.leftDual_rightDual

@[simp]
theorem rightDual_leftDual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X :=
  rfl
#align category_theory.right_dual_left_dual CategoryTheory.rightDual_leftDual

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (λ_ _).hom
#align category_theory.right_adjoint_mate CategoryTheory.rightAdjointMate

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (λ_ _).inv ≫ η_ (ᘁX) X ▷ _ ≫ (_ ◁ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
#align category_theory.left_adjoint_mate CategoryTheory.leftAdjointMate

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f
@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

@[simp]
theorem rightAdjointMate_id {X : C} [HasRightDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ) := by
  simp [rightAdjointMate]
#align category_theory.right_adjoint_mate_id CategoryTheory.rightAdjointMate_id

@[simp]
theorem leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX) := by
  simp [leftAdjointMate]
#align category_theory.left_adjoint_mate_id CategoryTheory.leftAdjointMate_id

theorem rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
    {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g =
      (ρ_ (Yᘁ)).inv ≫
        _ ◁ η_ X (Xᘁ) ≫ _ ◁ (f ⊗ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ ε_ Y (Yᘁ) ▷ _ ≫ (λ_ Z).hom :=
  calc
    _ = 𝟙 _ ⊗≫ Yᘁ ◁ η_ X Xᘁ ≫ Yᘁ ◁ f ▷ Xᘁ ⊗≫ (ε_ Y Yᘁ ▷ Xᘁ ≫ 𝟙_ C ◁ g) ⊗≫ 𝟙 _ := by
      dsimp only [rightAdjointMate]; coherence
    _ = _ := by
      rw [← whisker_exchange, tensorHom_def]; coherence
#align category_theory.right_adjoint_mate_comp CategoryTheory.rightAdjointMate_comp

theorem leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
    {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g =
      (λ_ _).inv ≫
        η_ (ᘁX) X ▷ _ ≫ (g ⊗ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom :=
  calc
    _ = 𝟙 _ ⊗≫ η_ (ᘁX) X ▷ (ᘁY) ⊗≫ (ᘁX) ◁ f ▷ (ᘁY) ⊗≫ ((ᘁX) ◁ ε_ (ᘁY) Y ≫ g ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
      dsimp only [leftAdjointMate]; coherence
    _ = _ := by
      rw [whisker_exchange, tensorHom_def']; coherence
#align category_theory.left_adjoint_mate_comp CategoryTheory.leftAdjointMate_comp

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
      rw [tensorHom_def']; coherence
    _ = η_ X Xᘁ ⊗≫ (η_ Y Yᘁ ▷ (X ⊗ Xᘁ) ≫ (Y ⊗ Yᘁ) ◁ f ▷ Xᘁ) ⊗≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; coherence
    _ = η_ X Xᘁ ⊗≫ f ▷ Xᘁ ⊗≫ (η_ Y Yᘁ ▷ Y ⊗≫ Y ◁ ε_ Y Yᘁ) ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; coherence
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ g ▷ Xᘁ := by
      rw [evaluation_coevaluation'']; coherence
#align category_theory.comp_right_adjoint_mate CategoryTheory.comp_rightAdjointMate

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
      rw [tensorHom_def]; coherence
    _ = η_ (ᘁX) X ⊗≫ (((ᘁX) ⊗ X) ◁ η_ (ᘁY) Y ≫ ((ᘁX) ◁ f) ▷ ((ᘁY) ⊗ Y)) ⊗≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y ⊗≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; coherence
    _ = η_ (ᘁX) X ⊗≫ ((ᘁX) ◁ f) ⊗≫ (ᘁX) ◁ (Y ◁ η_ (ᘁY) Y ⊗≫ ε_ (ᘁY) Y ▷ Y) ⊗≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; coherence
    _ = η_ (ᘁX) X ≫ (ᘁX) ◁ f ≫ (ᘁX) ◁ g := by
      rw [coevaluation_evaluation'']; coherence
#align category_theory.comp_left_adjoint_mate CategoryTheory.comp_leftAdjointMate

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
        coherence
      _ = 𝟙 _ ⊗≫ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ▷ X ⊗≫ f := by
        rw [whisker_exchange]; coherence
      _ = f := by
        rw [coevaluation_evaluation'']; coherence
  right_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ (η_ Y Y' ▷ X ≫ (Y ⊗ Y') ◁ f) ⊗≫ Y ◁ ε_ Y Y' ▷ Z ⊗≫ 𝟙 _ := by
        coherence
      _ = f ⊗≫ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ▷ Z ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; coherence
      _ = f := by
        rw [evaluation_coevaluation'']; coherence
#align category_theory.tensor_left_hom_equiv CategoryTheory.tensorLeftHomEquiv

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
        coherence
      _ = 𝟙 _ ⊗≫ X ◁ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ f := by
        rw [← whisker_exchange]; coherence
      _ = f := by
        rw [evaluation_coevaluation'']; coherence
  right_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ (X ◁ η_ Y Y' ≫ f ▷ (Y ⊗ Y')) ⊗≫ Z ◁ ε_ Y Y' ▷ Y' ⊗≫ 𝟙 _ := by
        coherence
      _ = f ⊗≫ Z ◁ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; coherence
      _ = f := by
        rw [coevaluation_evaluation'']; coherence
#align category_theory.tensor_right_hom_equiv CategoryTheory.tensorRightHomEquiv

theorem tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g := by
  simp [tensorLeftHomEquiv]
#align category_theory.tensor_left_hom_equiv_naturality CategoryTheory.tensorLeftHomEquiv_naturality

theorem tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      _ ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g := by
  simp [tensorLeftHomEquiv]
#align category_theory.tensor_left_hom_equiv_symm_naturality CategoryTheory.tensorLeftHomEquiv_symm_naturality

theorem tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y' := by
  simp [tensorRightHomEquiv]
#align category_theory.tensor_right_hom_equiv_naturality CategoryTheory.tensorRightHomEquiv_naturality

theorem tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g := by
  simp [tensorRightHomEquiv]
#align category_theory.tensor_right_hom_equiv_symm_naturality CategoryTheory.tensorRightHomEquiv_symm_naturality

/-- If `Y Y'` have an exact pairing,
then the functor `tensorLeft Y'` is left adjoint to `tensorLeft Y`.
-/
def tensorLeftAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorLeft Y' ⊣ tensorLeft Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorLeftHomEquiv_naturality f g }
#align category_theory.tensor_left_adjunction CategoryTheory.tensorLeftAdjunction

/-- If `Y Y'` have an exact pairing,
then the functor `tensor_right Y` is left adjoint to `tensor_right Y'`.
-/
def tensorRightAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorRight Y ⊣ tensorRight Y' :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorRightHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorRightHomEquiv_naturality f g }
#align category_theory.tensor_right_adjunction CategoryTheory.tensorRightAdjunction

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
  adj := tensorLeftAdjunction (ᘁY) Y
#align category_theory.closed_of_has_left_dual CategoryTheory.closedOfHasLeftDual

/-- `tensorLeftHomEquiv` commutes with tensoring on the right -/
theorem tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y ⊗ Z)
    (g : X' ⟶ Z') :
    (tensorLeftHomEquiv (X ⊗ X') Y Y' (Z ⊗ Z')).symm ((f ⊗ g) ≫ (α_ _ _ _).hom) =
      (α_ _ _ _).inv ≫ ((tensorLeftHomEquiv X Y Y' Z).symm f ⊗ g) := by
  simp [tensorLeftHomEquiv, tensorHom_def']
#align category_theory.tensor_left_hom_equiv_tensor CategoryTheory.tensorLeftHomEquiv_tensor

/-- `tensorRightHomEquiv` commutes with tensoring on the left -/
theorem tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z ⊗ Y')
    (g : X' ⟶ Z') :
    (tensorRightHomEquiv (X' ⊗ X) Y Y' (Z' ⊗ Z)).symm ((g ⊗ f) ≫ (α_ _ _ _).inv) =
      (α_ _ _ _).hom ≫ (g ⊗ (tensorRightHomEquiv X Y Y' Z).symm f) := by
  simp [tensorRightHomEquiv, tensorHom_def]
#align category_theory.tensor_right_hom_equiv_tensor CategoryTheory.tensorRightHomEquiv_tensor

@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ Y ◁ f) = (ρ_ _).hom ≫ f := by
  calc
    _ = Y' ◁ η_ Y Y' ⊗≫ ((Y' ⊗ Y) ◁ f ≫ ε_ Y Y' ▷ Z) ⊗≫ 𝟙 _ := by
      dsimp [tensorLeftHomEquiv]; coherence
    _ = (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ⊗≫ f := by
      rw [whisker_exchange]; coherence
    _ = _ := by rw [coevaluation_evaluation'']; coherence
#align category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_id_tensor CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft

@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight {X Y : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) :
    (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ f ▷ (Xᘁ)) = (ρ_ _).hom ≫ fᘁ := by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  simp
#align category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_tensor_id CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight

@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft {X Y : C} [HasLeftDual X]
    [HasLeftDual Y] (f : X ⟶ Y) :
    (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (ᘁX) X ≫ (ᘁX) ◁ f) = (λ_ _).hom ≫ ᘁf := by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  simp
#align category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_id_tensor CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft

@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ f ▷ Y') = (λ_ _).hom ≫ f :=
  calc
    _ = η_ Y Y' ▷ Y ⊗≫ (f ▷ (Y' ⊗ Y) ≫ Z ◁ ε_ Y Y') ⊗≫ 𝟙 _ := by
      dsimp [tensorRightHomEquiv]; coherence
    _ = (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ f := by
      rw [← whisker_exchange]; coherence
    _ = _ := by
      rw [evaluation_coevaluation'']; coherence
#align category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_tensor_id CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight

@[simp]
theorem tensorLeftHomEquiv_whiskerLeft_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) :
    (tensorLeftHomEquiv _ _ _ _) (Z ◁ f ≫ ε_ _ _) = f ≫ (ρ_ _).inv :=
  calc
    _ = 𝟙 _ ⊗≫ (η_ (ᘁZ) Z ▷ Y ≫ ((ᘁZ) ⊗ Z) ◁ f) ⊗≫ (ᘁZ) ◁ ε_ (ᘁZ) Z := by
      dsimp [tensorLeftHomEquiv]; coherence
    _ = f ⊗≫ (η_ (ᘁZ) Z ▷ (ᘁZ) ⊗≫ (ᘁZ) ◁ ε_ (ᘁZ) Z) := by
      rw [← whisker_exchange]; coherence
    _ = _ := by
      rw [evaluation_coevaluation'']; coherence
#align category_theory.tensor_left_hom_equiv_id_tensor_comp_evaluation CategoryTheory.tensorLeftHomEquiv_whiskerLeft_comp_evaluation

@[simp]
theorem tensorLeftHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) (f ▷ _ ≫ ε_ _ _) = (ᘁf) ≫ (ρ_ _).inv := by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  simp
#align category_theory.tensor_left_hom_equiv_tensor_id_comp_evaluation CategoryTheory.tensorLeftHomEquiv_whiskerRight_comp_evaluation

@[simp]
theorem tensorRightHomEquiv_whiskerLeft_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((Yᘁ) ◁ f ≫ ε_ _ _) = fᘁ ≫ (λ_ _).inv := by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  simp
#align category_theory.tensor_right_hom_equiv_id_tensor_comp_evaluation CategoryTheory.tensorRightHomEquiv_whiskerLeft_comp_evaluation

@[simp]
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ) :
    (tensorRightHomEquiv _ _ _ _) (f ▷ X ≫ ε_ X (Xᘁ)) = f ≫ (λ_ _).inv :=
  calc
    _ = 𝟙 _ ⊗≫ (Y ◁ η_ X Xᘁ ≫ f ▷ (X ⊗ Xᘁ)) ⊗≫ ε_ X Xᘁ ▷ Xᘁ := by
      dsimp [tensorRightHomEquiv]; coherence
    _ = f ⊗≫ (Xᘁ ◁ η_ X Xᘁ ⊗≫ ε_ X Xᘁ ▷ Xᘁ) := by
      rw [whisker_exchange]; coherence
    _ = _ := by
      rw [coevaluation_evaluation'']; coherence
#align category_theory.tensor_right_hom_equiv_tensor_id_comp_evaluation CategoryTheory.tensorRightHomEquiv_whiskerRight_comp_evaluation

-- Next four lemmas passing `fᘁ` or `ᘁf` through (co)evaluations.
@[reassoc]
theorem coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ _ ◁ (fᘁ) = η_ _ _ ≫ f ▷ _ := by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp
#align category_theory.coevaluation_comp_right_adjoint_mate CategoryTheory.coevaluation_comp_rightAdjointMate

@[reassoc]
theorem leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    X ◁ (ᘁf) ≫ ε_ _ _ = f ▷ _ ≫ ε_ _ _ := by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp
#align category_theory.left_adjoint_mate_comp_evaluation CategoryTheory.leftAdjointMate_comp_evaluation

@[reassoc]
theorem coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ (ᘁf) ▷ Y = η_ (ᘁX) X ≫ (ᘁX) ◁ f := by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp
#align category_theory.coevaluation_comp_left_adjoint_mate CategoryTheory.coevaluation_comp_leftAdjointMate

@[reassoc]
theorem rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ▷ X) ≫ ε_ X (Xᘁ) = ((Yᘁ) ◁ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp
#align category_theory.right_adjoint_mate_comp_evaluation CategoryTheory.rightAdjointMate_comp_evaluation

/-- Transport an exact pairing across an isomorphism in the first argument. -/
def exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : ExactPairing X Y where
  evaluation' := Y ◁ i.hom ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ i.inv ▷ Y
  evaluation_coevaluation' :=
    calc
      _ = η_ X' Y ▷ X ⊗≫ (i.inv ▷ (Y ⊗ X) ≫ X ◁ (Y ◁ i.hom)) ⊗≫ X ◁ ε_ X' Y := by
        coherence
      _ = 𝟙 _ ⊗≫ (η_ X' Y ▷ X ≫ (X' ⊗ Y) ◁ i.hom) ⊗≫
          (i.inv ▷ (Y ⊗ X') ≫ X ◁ ε_ X' Y) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; coherence
      _ = 𝟙 _ ⊗≫ i.hom ⊗≫ (η_ X' Y ▷ X' ⊗≫ X' ◁ ε_ X' Y) ⊗≫ i.inv ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, ← whisker_exchange]; coherence
      _ = 𝟙 _ ⊗≫ (i.hom ≫ i.inv) ⊗≫ 𝟙 _ := by
        rw [evaluation_coevaluation'']; coherence
      _ = (λ_ X).hom ≫ (ρ_ X).inv := by
        rw [Iso.hom_inv_id]
        -- coherence failed
        simp [monoidalComp]
  coevaluation_evaluation' := by
    calc
      _ = Y ◁ η_ X' Y ≫ Y ◁ (i.inv ≫ i.hom) ▷ Y ⊗≫ ε_ X' Y ▷ Y := by
        coherence
      _ = Y ◁ η_ X' Y ⊗≫ ε_ X' Y ▷ Y := by
        rw [Iso.inv_hom_id]; coherence
      _ = _ := by
        rw [coevaluation_evaluation'']
        -- coherence failed
        simp [monoidalComp]
#align category_theory.exact_pairing_congr_left CategoryTheory.exactPairingCongrLeft

/-- Transport an exact pairing across an isomorphism in the second argument. -/
def exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : ExactPairing X Y where
  evaluation' := i.hom ▷ X ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ X ◁ i.inv
  evaluation_coevaluation' := by
    calc
      _ = η_ X Y' ▷ X ⊗≫ X ◁ (i.inv ≫ i.hom) ▷ X ≫ X ◁ ε_ X Y' := by
        coherence
      _ = η_ X Y' ▷ X ⊗≫ X ◁ ε_ X Y' := by
        rw [Iso.inv_hom_id]; coherence
      _ = _ := by
        rw [evaluation_coevaluation'']
        -- coherence failed
        simp [monoidalComp]
  coevaluation_evaluation' :=
    calc
      _ = Y ◁ η_ X Y' ⊗≫ (Y ◁ (X ◁ i.inv) ≫ i.hom ▷ (X ⊗ Y)) ⊗≫ ε_ X Y' ▷ Y := by
        coherence
      _ = 𝟙 _ ⊗≫ (Y ◁ η_ X Y' ≫ i.hom ▷ (X ⊗ Y')) ⊗≫
          ((Y' ⊗ X) ◁ i.inv ≫ ε_ X Y' ▷ Y) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; coherence
      _ = 𝟙 _ ⊗≫ i.hom ⊗≫ (Y' ◁ η_ X Y' ⊗≫ ε_ X Y' ▷ Y') ⊗≫ i.inv ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, whisker_exchange]; coherence
      _ = 𝟙 _ ⊗≫ (i.hom ≫ i.inv) ⊗≫ 𝟙 _ := by
        rw [coevaluation_evaluation'']; coherence
      _ = (ρ_ Y).hom ≫ (λ_ Y).inv := by
        rw [Iso.hom_inv_id]
        -- coherence failed
        simp [monoidalComp]
#align category_theory.exact_pairing_congr_right CategoryTheory.exactPairingCongrRight

/-- Transport an exact pairing across isomorphisms. -/
def exactPairingCongr {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y') :
    ExactPairing X Y :=
  haveI : ExactPairing X' Y := exactPairingCongrRight j
  exactPairingCongrLeft i
#align category_theory.exact_pairing_congr CategoryTheory.exactPairingCongr

/-- Right duals are isomorphic. -/
def rightDualIso {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) : Y₁ ≅ Y₂ where
  hom := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  -- Porting note: no implicit arguments were required below:
  hom_inv_id := by
    rw [← @comp_rightAdjointMate C _ _ X X X ⟨Y₁⟩ ⟨Y₂⟩ ⟨Y₁⟩, Category.comp_id,
      @rightAdjointMate_id _ _ _ _ ⟨Y₁⟩]
    rfl
  inv_hom_id := by
    rw [← @comp_rightAdjointMate C _ _ X X X ⟨Y₂⟩ ⟨Y₁⟩ ⟨Y₂⟩, Category.comp_id,
      @rightAdjointMate_id _ _ _ _ ⟨Y₂⟩]
    rfl
#align category_theory.right_dual_iso CategoryTheory.rightDualIso

/-- Left duals are isomorphic. -/
def leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ where
  hom := @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  -- Porting note: no implicit arguments were required below:
  hom_inv_id := by
    rw [← @comp_leftAdjointMate C _ _ Y Y Y ⟨X₁⟩ ⟨X₂⟩ ⟨X₁⟩, Category.comp_id,
      @leftAdjointMate_id _ _ _ _ ⟨X₁⟩]
    rfl
  inv_hom_id := by
    rw [← @comp_leftAdjointMate C _ _ Y Y Y ⟨X₂⟩ ⟨X₁⟩ ⟨X₂⟩, Category.comp_id,
      @leftAdjointMate_id _ _ _ _ ⟨X₂⟩]
    rfl
#align category_theory.left_dual_iso CategoryTheory.leftDualIso

@[simp]
theorem rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by
  ext
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id _ _ _ _ ⟨Y⟩]
#align category_theory.right_dual_iso_id CategoryTheory.rightDualIso_id

@[simp]
theorem leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by
  ext
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id _ _ _ _ ⟨X⟩]
#align category_theory.left_dual_iso_id CategoryTheory.leftDualIso_id

/-- A right rigid monoidal category is one in which every object has a right dual. -/
class RightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [rightDual : ∀ X : C, HasRightDual X]
#align category_theory.right_rigid_category CategoryTheory.RightRigidCategory

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : ∀ X : C, HasLeftDual X]
#align category_theory.left_rigid_category CategoryTheory.LeftRigidCategory

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
#align category_theory.monoidal_closed_of_left_rigid_category CategoryTheory.monoidalClosedOfLeftRigidCategory

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class RigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    RightRigidCategory C, LeftRigidCategory C
#align category_theory.rigid_category CategoryTheory.RigidCategory

end CategoryTheory

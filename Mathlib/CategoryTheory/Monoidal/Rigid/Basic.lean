/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.monoidal.rigid.basic
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.Tactic.ApplyFun

/-!
# Rigid (autonomous) monoidal categories

This file defines rigid (autonomous) monoidal categories and the necessary theory about
exact pairings and duals.

## Main definitions

* `exact_pairing` of two objects of a monoidal category
* Type classes `has_left_dual` and `has_right_dual` that capture that a pairing exists
* The `right_adjoint_mate f` as a morphism `fᘁ : Yᘁ ⟶ Xᘁ` for a morphism `f : X ⟶ Y`
* The classes of `right_rigid_category`, `left_rigid_category` and `rigid_category`

## Main statements

* `comp_right_adjoint_mate`: The adjoint mates of the composition is the composition of
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

Although we construct the adjunction `tensor_left Y ⊣ tensor_left X` from `exact_pairing X Y`,
this is not a bijective correspondence.
I think the correct statement is that `tensor_left Y` and `tensor_left X` are
module endofunctors of `C` as a right `C` module category,
and `exact_pairing X Y` is in bijection with adjunctions compatible with this right `C` action.

## References

* <https://ncatlab.org/nlab/show/rigid+monoidal+category>

## Tags

rigid category, monoidal category

-/


open CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`coevaluation] [] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`evaluation] [] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`coevaluation_evaluation'] [] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`evaluation_coevaluation'] [] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class ExactPairing (X Y : C) where
  coevaluation : 𝟙_ C ⟶ X ⊗ Y
  evaluation : Y ⊗ X ⟶ 𝟙_ C
  coevaluation_evaluation' :
    (𝟙 Y ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 Y) = (ρ_ Y).Hom ≫ (λ_ Y).inv := by
    obviously
  evaluation_coevaluation' :
    (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).Hom ≫ (𝟙 X ⊗ evaluation) = (λ_ X).Hom ≫ (ρ_ X).inv := by
    obviously
#align category_theory.exact_pairing CategoryTheory.ExactPairing

open ExactPairing

-- mathport name: exprη_
notation "η_" => ExactPairing.coevaluation

-- mathport name: exprε_
notation "ε_" => ExactPairing.evaluation

restate_axiom coevaluation_evaluation'

attribute [simp, reassoc] exact_pairing.coevaluation_evaluation

restate_axiom evaluation_coevaluation'

attribute [simp, reassoc] exact_pairing.evaluation_coevaluation

instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation := (ρ_ _).inv
  evaluation := (ρ_ _).Hom
  coevaluation_evaluation' := by coherence
  evaluation_coevaluation' := by coherence
#align category_theory.exact_pairing_unit CategoryTheory.exactPairingUnit

/-- A class of objects which have a right dual. -/
class HasRightDual (X : C) where
  rightDual : C
  [exact : ExactPairing X right_dual]
#align category_theory.has_right_dual CategoryTheory.HasRightDual

/-- A class of objects with have a left dual. -/
class HasLeftDual (Y : C) where
  leftDual : C
  [exact : ExactPairing left_dual Y]
#align category_theory.has_left_dual CategoryTheory.HasLeftDual

attribute [instance] has_right_dual.exact

attribute [instance] has_left_dual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

-- mathport name: left_dual
prefix:1024 "ᘁ" => leftDual

-- mathport name: right_dual
postfix:1024 "ᘁ" => rightDual

instance hasRightDualUnit : HasRightDual (𝟙_ C) where rightDual := 𝟙_ C
#align category_theory.has_right_dual_unit CategoryTheory.hasRightDualUnit

instance hasLeftDualUnit : HasLeftDual (𝟙_ C) where leftDual := 𝟙_ C
#align category_theory.has_left_dual_unit CategoryTheory.hasLeftDualUnit

instance hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where rightDual := X
#align category_theory.has_right_dual_left_dual CategoryTheory.hasRightDualLeftDual

instance hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where leftDual := X
#align category_theory.has_left_dual_right_dual CategoryTheory.hasLeftDualRightDual

@[simp]
theorem leftDual_rightDual {X : C} [HasRightDual X] : ᘁXᘁ = X :=
  rfl
#align category_theory.left_dual_right_dual CategoryTheory.leftDual_rightDual

@[simp]
theorem rightDual_leftDual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X :=
  rfl
#align category_theory.right_dual_left_dual CategoryTheory.rightDual_leftDual

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (𝟙 _ ⊗ f ⊗ 𝟙 _) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).Hom
#align category_theory.right_adjoint_mate CategoryTheory.rightAdjointMate

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom
#align category_theory.left_adjoint_mate CategoryTheory.leftAdjointMate

-- mathport name: right_adjoint_mate
notation f "ᘁ" => rightAdjointMate f

-- mathport name: left_adjoint_mate
notation "ᘁ" f => leftAdjointMate f

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightAdjointMate_id {X : C} [HasRightDual X] : 𝟙 Xᘁ = 𝟙 (Xᘁ) := by
  simp only [right_adjoint_mate, monoidal_category.tensor_id, category.id_comp,
    coevaluation_evaluation_assoc, category.comp_id, iso.inv_hom_id]
#align category_theory.right_adjoint_mate_id CategoryTheory.rightAdjointMate_id

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ𝟙 X) = 𝟙 (ᘁX) := by
  simp only [left_adjoint_mate, monoidal_category.tensor_id, category.id_comp,
    evaluation_coevaluation_assoc, category.comp_id, iso.inv_hom_id]
#align category_theory.left_adjoint_mate_id CategoryTheory.leftAdjointMate_id

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
    {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g =
      (ρ_ (Yᘁ)).inv ≫
        (𝟙 _ ⊗ η_ X (Xᘁ)) ≫ (𝟙 _ ⊗ f ⊗ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ (ε_ Y (Yᘁ) ⊗ 𝟙 _) ≫ (λ_ Z).Hom := by
  dsimp only [right_adjoint_mate]
  rw [category.assoc, category.assoc, associator_inv_naturality_assoc,
    associator_inv_naturality_assoc, ← tensor_id_comp_id_tensor g, category.assoc, category.assoc,
    category.assoc, category.assoc, id_tensor_comp_tensor_id_assoc, ← left_unitor_naturality,
    tensor_id_comp_id_tensor_assoc]
#align category_theory.right_adjoint_mate_comp CategoryTheory.rightAdjointMate_comp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
    {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g =
      (λ_ _).inv ≫
        (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((g ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom := by
  dsimp only [left_adjoint_mate]
  rw [category.assoc, category.assoc, associator_naturality_assoc, associator_naturality_assoc, ←
    id_tensor_comp_tensor_id _ g, category.assoc, category.assoc, category.assoc, category.assoc,
    tensor_id_comp_id_tensor_assoc, ← right_unitor_naturality, id_tensor_comp_tensor_id_assoc]
#align category_theory.left_adjoint_mate_comp CategoryTheory.leftAdjointMate_comp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_rightAdjointMate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ := by
  rw [right_adjoint_mate_comp]
  simp only [right_adjoint_mate, comp_tensor_id, iso.cancel_iso_inv_left, id_tensor_comp,
    category.assoc]
  symm; iterate 5 trans; rw [← category.id_comp g, tensor_comp]
  rw [← category.assoc]
  symm; iterate 2 trans; rw [← category.assoc]; apply eq_whisker
  repeat' rw [← id_tensor_comp]; congr 1
  rw [← id_tensor_comp_tensor_id (λ_ (Xᘁ)).Hom g, id_tensor_right_unitor_inv, category.assoc,
    category.assoc, right_unitor_inv_naturality_assoc, ← associator_naturality_assoc, tensor_id,
    tensor_id_comp_id_tensor_assoc, ← associator_naturality_assoc]
  slice_rhs 2 3 =>
    rw [← tensor_comp, tensor_id, category.comp_id, ← category.id_comp (η_ Y (Yᘁ)), tensor_comp]
  rw [← id_tensor_comp_tensor_id _ (η_ Y (Yᘁ)), ← tensor_id]
  repeat' rw [category.assoc]
  rw [pentagon_hom_inv_assoc, ← associator_naturality_assoc, associator_inv_naturality_assoc]
  slice_rhs 5 7 => rw [← comp_tensor_id, ← comp_tensor_id, evaluation_coevaluation, comp_tensor_id]
  rw [associator_inv_naturality_assoc]
  slice_rhs 4 5 => rw [← tensor_comp, left_unitor_naturality, tensor_comp]
  repeat' rw [category.assoc]
  rw [triangle_assoc_comp_right_inv_assoc, ← left_unitor_tensor_assoc, left_unitor_naturality_assoc,
    unitors_equal, ← category.assoc, ← category.assoc]
  simp
#align category_theory.comp_right_adjoint_mate CategoryTheory.comp_rightAdjointMate

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_leftAdjointMate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf := by
  rw [left_adjoint_mate_comp]
  simp only [left_adjoint_mate, id_tensor_comp, iso.cancel_iso_inv_left, comp_tensor_id,
    category.assoc]
  symm; iterate 5 trans; rw [← category.id_comp g, tensor_comp]
  rw [← category.assoc]
  symm; iterate 2 trans; rw [← category.assoc]; apply eq_whisker
  repeat' rw [← comp_tensor_id]; congr 1
  rw [← tensor_id_comp_id_tensor g (ρ_ (ᘁX)).Hom, left_unitor_inv_tensor_id, category.assoc,
    category.assoc, left_unitor_inv_naturality_assoc, ← associator_inv_naturality_assoc, tensor_id,
    id_tensor_comp_tensor_id_assoc, ← associator_inv_naturality_assoc]
  slice_rhs 2 3 =>
    rw [← tensor_comp, tensor_id, category.comp_id, ← category.id_comp (η_ (ᘁY) Y), tensor_comp]
  rw [← tensor_id_comp_id_tensor (η_ (ᘁY) Y), ← tensor_id]
  repeat' rw [category.assoc]
  rw [pentagon_inv_hom_assoc, ← associator_inv_naturality_assoc, associator_naturality_assoc]
  slice_rhs 5 7 => rw [← id_tensor_comp, ← id_tensor_comp, coevaluation_evaluation, id_tensor_comp]
  rw [associator_naturality_assoc]
  slice_rhs 4 5 => rw [← tensor_comp, right_unitor_naturality, tensor_comp]
  repeat' rw [category.assoc]
  rw [triangle_assoc_comp_left_inv_assoc, ← right_unitor_tensor_assoc,
    right_unitor_naturality_assoc, ← unitors_equal, ← category.assoc, ← category.assoc]
  simp
#align category_theory.comp_left_adjoint_mate CategoryTheory.comp_leftAdjointMate

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
by "pulling the string on the left" up or down.

This gives the adjunction `tensor_left_adjunction Y Y' : tensor_left Y' ⊣ tensor_left Y`.

This adjunction is often referred to as "Frobenius reciprocity" in the
fusion categories / planar algebras / subfactors literature.
-/
def tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z) where
  toFun f := (λ_ _).inv ≫ (η_ _ _ ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ f)
  invFun f := (𝟙 Y' ⊗ f) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).Hom
  left_inv f := by
    dsimp
    simp only [id_tensor_comp]
    slice_lhs 4 5 => rw [associator_inv_naturality]
    slice_lhs 5 6 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_lhs 2 5 => simp only [← tensor_id, associator_inv_conjugation]
    have c :
      (α_ Y' (Y ⊗ Y') X).Hom ≫
          (𝟙 Y' ⊗ (α_ Y Y' X).Hom) ≫ (α_ Y' Y (Y' ⊗ X)).inv ≫ (α_ (Y' ⊗ Y) Y' X).inv =
        (α_ _ _ _).inv ⊗ 𝟙 _
    pure_coherence
    slice_lhs 4 7 => rw [c]
    slice_lhs 3 5 => rw [← comp_tensor_id, ← comp_tensor_id, coevaluation_evaluation]
    simp only [left_unitor_conjugation]
    coherence
  right_inv f := by
    dsimp
    simp only [id_tensor_comp]
    slice_lhs 3 4 => rw [← associator_naturality]
    slice_lhs 2 3 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    slice_lhs 3 6 => simp only [← tensor_id, associator_inv_conjugation]
    have c :
      (α_ (Y ⊗ Y') Y Z).Hom ≫
          (α_ Y Y' (Y ⊗ Z)).Hom ≫ (𝟙 Y ⊗ (α_ Y' Y Z).inv) ≫ (α_ Y (Y' ⊗ Y) Z).inv =
        (α_ _ _ _).Hom ⊗ 𝟙 Z
    pure_coherence
    slice_lhs 5 8 => rw [c]
    slice_lhs 4 6 => rw [← comp_tensor_id, ← comp_tensor_id, evaluation_coevaluation]
    simp only [left_unitor_conjugation]
    coherence
#align category_theory.tensor_left_hom_equiv CategoryTheory.tensorLeftHomEquiv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')`
by "pulling the string on the right" up or down.
-/
def tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y') where
  toFun f := (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (α_ _ _ _).inv ≫ (f ⊗ 𝟙 _)
  invFun f := (f ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom
  left_inv f := by
    dsimp
    simp only [comp_tensor_id]
    slice_lhs 4 5 => rw [associator_naturality]
    slice_lhs 5 6 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    slice_lhs 2 5 => simp only [← tensor_id, associator_conjugation]
    have c :
      (α_ X (Y ⊗ Y') Y).inv ≫
          ((α_ X Y Y').inv ⊗ 𝟙 Y) ≫ (α_ (X ⊗ Y) Y' Y).Hom ≫ (α_ X Y (Y' ⊗ Y)).Hom =
        𝟙 _ ⊗ (α_ _ _ _).Hom
    pure_coherence
    slice_lhs 4 7 => rw [c]
    slice_lhs 3 5 => rw [← id_tensor_comp, ← id_tensor_comp, evaluation_coevaluation]
    simp only [right_unitor_conjugation]
    coherence
  right_inv f := by
    dsimp
    simp only [comp_tensor_id]
    slice_lhs 3 4 => rw [← associator_inv_naturality]
    slice_lhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_lhs 3 6 => simp only [← tensor_id, associator_conjugation]
    have c :
      (α_ Z Y' (Y ⊗ Y')).inv ≫
          (α_ (Z ⊗ Y') Y Y').inv ≫ ((α_ Z Y' Y).Hom ⊗ 𝟙 Y') ≫ (α_ Z (Y' ⊗ Y) Y').Hom =
        𝟙 _ ⊗ (α_ _ _ _).inv
    pure_coherence
    slice_lhs 5 8 => rw [c]
    slice_lhs 4 6 => rw [← id_tensor_comp, ← id_tensor_comp, coevaluation_evaluation]
    simp only [right_unitor_conjugation]
    coherence
#align category_theory.tensor_right_hom_equiv CategoryTheory.tensorRightHomEquiv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorLeftHomEquiv X Y Y' Z) f ≫ (𝟙 Y ⊗ g) := by
  dsimp [tensor_left_hom_equiv]
  simp only [id_tensor_comp, category.assoc]
#align category_theory.tensor_left_hom_equiv_naturality CategoryTheory.tensorLeftHomEquiv_naturality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      (𝟙 _ ⊗ f) ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g := by
  dsimp [tensor_left_hom_equiv]
  simp only [id_tensor_comp, category.assoc]
#align category_theory.tensor_left_hom_equiv_symm_naturality CategoryTheory.tensorLeftHomEquiv_symm_naturality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensorRightHomEquiv X Y Y' Z) f ≫ (g ⊗ 𝟙 Y') := by
  dsimp [tensor_right_hom_equiv]
  simp only [comp_tensor_id, category.assoc]
#align category_theory.tensor_right_hom_equiv_naturality CategoryTheory.tensorRightHomEquiv_naturality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      (f ⊗ 𝟙 Y) ≫ (tensorRightHomEquiv X' Y Y' Z).symm g := by
  dsimp [tensor_right_hom_equiv]
  simp only [comp_tensor_id, category.assoc]
#align category_theory.tensor_right_hom_equiv_symm_naturality CategoryTheory.tensorRightHomEquiv_symm_naturality

/-- If `Y Y'` have an exact pairing,
then the functor `tensor_left Y'` is left adjoint to `tensor_left Y`.
-/
def tensorLeftAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorLeft Y' ⊣ tensorLeft Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun X X' Z f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun X Z Z' f g => tensorLeftHomEquiv_naturality f g }
#align category_theory.tensor_left_adjunction CategoryTheory.tensorLeftAdjunction

/-- If `Y Y'` have an exact pairing,
then the functor `tensor_right Y` is left adjoint to `tensor_right Y'`.
-/
def tensorRightAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorRight Y ⊣ tensorRight Y' :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorRightHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun X X' Z f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun X Z Z' f g => tensorRightHomEquiv_naturality f g }
#align category_theory.tensor_right_adjunction CategoryTheory.tensorRightAdjunction

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/--
If `Y` has a left dual `ᘁY`, then it is a closed object, with the internal hom functor `Y ⟶[C] -`
given by left tensoring by `ᘁY`.
This has to be a definition rather than an instance to avoid diamonds, for example between
`category_theory.monoidal_closed.functor_closed` and
`category_theory.monoidal.functor_has_left_dual`. Moreover, in concrete applications there is often
a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the closed
structure shouldn't come from `has_left_dual` (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic).
-/
def closedOfHasLeftDual (Y : C) [HasLeftDual Y] : Closed Y
    where isAdj := ⟨_, tensorLeftAdjunction (ᘁY) Y⟩
#align category_theory.closed_of_has_left_dual CategoryTheory.closedOfHasLeftDual

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- `tensor_left_hom_equiv` commutes with tensoring on the right -/
theorem tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y ⊗ Z)
    (g : X' ⟶ Z') :
    (tensorLeftHomEquiv (X ⊗ X') Y Y' (Z ⊗ Z')).symm ((f ⊗ g) ≫ (α_ _ _ _).Hom) =
      (α_ _ _ _).inv ≫ ((tensorLeftHomEquiv X Y Y' Z).symm f ⊗ g) := by
  dsimp [tensor_left_hom_equiv]
  simp only [id_tensor_comp]
  simp only [associator_inv_conjugation]
  slice_lhs 2 2 => rw [← id_tensor_comp_tensor_id]
  conv_rhs => rw [← id_tensor_comp_tensor_id, comp_tensor_id, comp_tensor_id]
  simp; coherence
#align category_theory.tensor_left_hom_equiv_tensor CategoryTheory.tensorLeftHomEquiv_tensor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- `tensor_right_hom_equiv` commutes with tensoring on the left -/
theorem tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z ⊗ Y')
    (g : X' ⟶ Z') :
    (tensorRightHomEquiv (X' ⊗ X) Y Y' (Z' ⊗ Z)).symm ((g ⊗ f) ≫ (α_ _ _ _).inv) =
      (α_ _ _ _).Hom ≫ (g ⊗ (tensorRightHomEquiv X Y Y' Z).symm f) := by
  dsimp [tensor_right_hom_equiv]
  simp only [comp_tensor_id]
  simp only [associator_conjugation]
  slice_lhs 2 2 => rw [← tensor_id_comp_id_tensor]
  conv_rhs => rw [← tensor_id_comp_id_tensor, id_tensor_comp, id_tensor_comp]
  simp only [← tensor_id, associator_conjugation]
  simp; coherence
#align category_theory.tensor_right_hom_equiv_tensor CategoryTheory.tensorRightHomEquiv_tensor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_id_tensor {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ (𝟙 Y ⊗ f)) = (ρ_ _).Hom ≫ f := by
  dsimp [tensor_left_hom_equiv]
  rw [id_tensor_comp]
  slice_lhs 2 3 => rw [associator_inv_naturality]
  slice_lhs 3 4 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_lhs 1 3 => rw [coevaluation_evaluation]
  simp
#align category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_id_tensor CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_id_tensor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_tensor_id {X Y : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) :
    (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ (f ⊗ 𝟙 (Xᘁ))) = (ρ_ _).Hom ≫ fᘁ := by
  dsimp [tensor_left_hom_equiv, right_adjoint_mate]
  simp
#align category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_tensor_id CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_tensor_id

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_id_tensor {X Y : C} [HasLeftDual X]
    [HasLeftDual Y] (f : X ⟶ Y) :
    (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (ᘁX) X ≫ (𝟙 (ᘁX) ⊗ f)) = (λ_ _).Hom ≫ ᘁf := by
  dsimp [tensor_right_hom_equiv, left_adjoint_mate]
  simp
#align category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_id_tensor CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_id_tensor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_tensor_id {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ (f ⊗ 𝟙 Y')) = (λ_ _).Hom ≫ f := by
  dsimp [tensor_right_hom_equiv]
  rw [comp_tensor_id]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_lhs 3 4 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 1 3 => rw [evaluation_coevaluation]
  simp
#align category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_tensor_id CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_tensor_id

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorLeftHomEquiv_id_tensor_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) :
    (tensorLeftHomEquiv _ _ _ _) ((𝟙 Z ⊗ f) ≫ ε_ _ _) = f ≫ (ρ_ _).inv := by
  dsimp [tensor_left_hom_equiv]
  rw [id_tensor_comp]
  slice_lhs 3 4 => rw [← associator_naturality]
  slice_lhs 2 3 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 3 5 => rw [evaluation_coevaluation]
  simp
#align category_theory.tensor_left_hom_equiv_id_tensor_comp_evaluation CategoryTheory.tensorLeftHomEquiv_id_tensor_comp_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorLeftHomEquiv_tensor_id_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) ((f ⊗ 𝟙 _) ≫ ε_ _ _) = (ᘁf) ≫ (ρ_ _).inv := by
  dsimp [tensor_left_hom_equiv, left_adjoint_mate]
  simp
#align category_theory.tensor_left_hom_equiv_tensor_id_comp_evaluation CategoryTheory.tensorLeftHomEquiv_tensor_id_comp_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorRightHomEquiv_id_tensor_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((𝟙 (Yᘁ) ⊗ f) ≫ ε_ _ _) = fᘁ ≫ (λ_ _).inv := by
  dsimp [tensor_right_hom_equiv, right_adjoint_mate]
  simp
#align category_theory.tensor_right_hom_equiv_id_tensor_comp_evaluation CategoryTheory.tensorRightHomEquiv_id_tensor_comp_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorRightHomEquiv_tensor_id_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ) :
    (tensorRightHomEquiv _ _ _ _) ((f ⊗ 𝟙 X) ≫ ε_ X (Xᘁ)) = f ≫ (λ_ _).inv := by
  dsimp [tensor_right_hom_equiv]
  rw [comp_tensor_id]
  slice_lhs 3 4 => rw [← associator_inv_naturality]
  slice_lhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_lhs 3 5 => rw [coevaluation_evaluation]
  simp
#align category_theory.tensor_right_hom_equiv_tensor_id_comp_evaluation CategoryTheory.tensorRightHomEquiv_tensor_id_comp_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- Next four lemmas passing `fᘁ` or `ᘁf` through (co)evaluations.
theorem coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ (𝟙 _ ⊗ fᘁ) = η_ _ _ ≫ (f ⊗ 𝟙 _) := by
  apply_fun (tensor_left_hom_equiv _ Y (Yᘁ) _).symm
  simp
#align category_theory.coevaluation_comp_right_adjoint_mate CategoryTheory.coevaluation_comp_rightAdjointMate

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    (𝟙 X ⊗ ᘁf) ≫ ε_ _ _ = (f ⊗ 𝟙 _) ≫ ε_ _ _ := by
  apply_fun tensor_left_hom_equiv _ (ᘁX) X _
  simp
#align category_theory.left_adjoint_mate_comp_evaluation CategoryTheory.leftAdjointMate_comp_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ ((ᘁf) ⊗ 𝟙 Y) = η_ (ᘁX) X ≫ (𝟙 (ᘁX) ⊗ f) := by
  apply_fun (tensor_right_hom_equiv _ (ᘁY) Y _).symm
  simp
#align category_theory.coevaluation_comp_left_adjoint_mate CategoryTheory.coevaluation_comp_leftAdjointMate

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ⊗ 𝟙 X) ≫ ε_ X (Xᘁ) = (𝟙 (Yᘁ) ⊗ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensor_right_hom_equiv _ X (Xᘁ) _
  simp
#align category_theory.right_adjoint_mate_comp_evaluation CategoryTheory.rightAdjointMate_comp_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Transport an exact pairing across an isomorphism in the first argument. -/
def exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : ExactPairing X Y where
  evaluation := (𝟙 Y ⊗ i.Hom) ≫ ε_ _ _
  coevaluation := η_ _ _ ≫ (i.inv ⊗ 𝟙 Y)
  evaluation_coevaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    slice_lhs 2 3 => rw [associator_naturality]
    slice_lhs 3 4 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    slice_lhs 4 5 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    slice_lhs 2 3 => rw [← associator_naturality]
    slice_lhs 1 2 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    slice_lhs 2 4 => rw [evaluation_coevaluation]
    slice_lhs 1 2 => rw [left_unitor_naturality]
    slice_lhs 3 4 => rw [← right_unitor_inv_naturality]
    simp
  coevaluation_evaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    simp only [iso.inv_hom_id_assoc, associator_conjugation, category.assoc]
    slice_lhs 2 3 =>
      rw [← tensor_comp]
      simp
    simp
#align category_theory.exact_pairing_congr_left CategoryTheory.exactPairingCongrLeft

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Transport an exact pairing across an isomorphism in the second argument. -/
def exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : ExactPairing X Y where
  evaluation := (i.Hom ⊗ 𝟙 X) ≫ ε_ _ _
  coevaluation := η_ _ _ ≫ (𝟙 X ⊗ i.inv)
  evaluation_coevaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    simp only [iso.inv_hom_id_assoc, associator_conjugation, category.assoc]
    slice_lhs 3 4 =>
      rw [← tensor_comp]
      simp
    simp
  coevaluation_evaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    slice_lhs 3 4 => rw [← associator_inv_naturality]
    slice_lhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_lhs 3 4 => rw [associator_inv_naturality]
    slice_lhs 4 5 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_lhs 2 4 => rw [coevaluation_evaluation]
    slice_lhs 1 2 => rw [right_unitor_naturality]
    slice_lhs 3 4 => rw [← left_unitor_inv_naturality]
    simp
#align category_theory.exact_pairing_congr_right CategoryTheory.exactPairingCongrRight

/-- Transport an exact pairing across isomorphisms. -/
def exactPairingCongr {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y') :
    ExactPairing X Y :=
  haveI : exact_pairing X' Y := exact_pairing_congr_right j
  exact_pairing_congr_left i
#align category_theory.exact_pairing_congr CategoryTheory.exactPairingCongr

/-- Right duals are isomorphic. -/
def rightDualIso {X Y₁ Y₂ : C} (_ : ExactPairing X Y₁) (_ : ExactPairing X Y₂) : Y₁ ≅ Y₂ where
  Hom := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id' := by rw [← comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id]
  inv_hom_id' := by rw [← comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id]
#align category_theory.right_dual_iso CategoryTheory.rightDualIso

/-- Left duals are isomorphic. -/
def leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ where
  Hom := @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id' := by rw [← comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id]
  inv_hom_id' := by rw [← comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id]
#align category_theory.left_dual_iso CategoryTheory.leftDualIso

@[simp]
theorem rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by ext;
  simp only [right_dual_iso, iso.refl_hom, right_adjoint_mate_id]
#align category_theory.right_dual_iso_id CategoryTheory.rightDualIso_id

@[simp]
theorem leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by ext;
  simp only [left_dual_iso, iso.refl_hom, left_adjoint_mate_id]
#align category_theory.left_dual_iso_id CategoryTheory.leftDualIso_id

/-- A right rigid monoidal category is one in which every object has a right dual. -/
class RightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [rightDual : ∀ X : C, HasRightDual X]
#align category_theory.right_rigid_category CategoryTheory.RightRigidCategory

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : ∀ X : C, HasLeftDual X]
#align category_theory.left_rigid_category CategoryTheory.LeftRigidCategory

attribute [instance 100] right_rigid_category.right_dual

attribute [instance 100] left_rigid_category.left_dual

/-- Any left rigid category is monoidal closed, with the internal hom `X ⟶[C] Y = ᘁX ⊗ Y`.
This has to be a definition rather than an instance to avoid diamonds, for example between
`category_theory.monoidal_closed.functor_category` and
`category_theory.monoidal.left_rigid_functor_category`. Moreover, in concrete applications there is
often a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the monoidal
closed structure shouldn't come the rigid structure (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic). -/
def monoidalClosedOfLeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [LeftRigidCategory C] : MonoidalClosed C where closed' X := closedOfHasLeftDual X
#align category_theory.monoidal_closed_of_left_rigid_category CategoryTheory.monoidalClosedOfLeftRigidCategory

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class RigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    RightRigidCategory C, LeftRigidCategory C
#align category_theory.rigid_category CategoryTheory.RigidCategory

end CategoryTheory


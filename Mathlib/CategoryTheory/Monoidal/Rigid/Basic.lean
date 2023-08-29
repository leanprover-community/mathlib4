/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
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
  coevaluation' : 𝟙_ C ⟶ X ⊗ Y
  evaluation' : Y ⊗ X ⟶ 𝟙_ C
  coevaluation_evaluation' :
    (𝟙 Y ⊗ coevaluation') ≫ (α_ _ _ _).inv ≫ (evaluation' ⊗ 𝟙 Y) = (ρ_ Y).hom ≫ (λ_ Y).inv := by
    aesop_cat
  evaluation_coevaluation' :
    (coevaluation' ⊗ 𝟙 X) ≫ (α_ _ _ _).hom ≫ (𝟙 X ⊗ evaluation') = (λ_ X).hom ≫ (ρ_ X).inv := by
    aesop_cat
#align category_theory.exact_pairing CategoryTheory.ExactPairing

namespace ExactPairing

-- Porting note: as there is no mechanism equivalent to `[]` in Lean 3 to make
-- arguments for class fields explicit,
-- we now repeat all the fields without primes.
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Making.20variable.20in.20class.20field.20explicit

variable (X Y : C)
variable [ExactPairing X Y]

def coevaluation : 𝟙_ C ⟶ X ⊗ Y := @coevaluation' _ _ _ X Y _
def evaluation : Y ⊗ X ⟶ 𝟙_ C := @evaluation' _ _ _ X Y _

notation "η_" => ExactPairing.coevaluation
notation "ε_" => ExactPairing.evaluation

lemma coevaluation_evaluation :
    (𝟙 Y ⊗ η_ _ _) ≫ (α_ _ _ _).inv ≫ (ε_ X _ ⊗ 𝟙 Y) = (ρ_ Y).hom ≫ (λ_ Y).inv :=
  coevaluation_evaluation'

lemma evaluation_coevaluation :
    (η_ _ _ ⊗ 𝟙 X) ≫ (α_ _ _ _).hom ≫ (𝟙 X ⊗ ε_ _ Y) = (λ_ X).hom ≫ (ρ_ X).inv :=
  evaluation_coevaluation'

end ExactPairing

attribute [reassoc (attr := simp)] ExactPairing.coevaluation_evaluation
attribute [reassoc (attr := simp)] ExactPairing.evaluation_coevaluation

instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation' := (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by coherence
                                 -- 🎉 no goals
  evaluation_coevaluation' := by coherence
                                 -- 🎉 no goals
#align category_theory.exact_pairing_unit CategoryTheory.exactPairingUnit

/-- A class of objects which have a right dual. -/
class HasRightDual (X : C) where
  rightDual : C
  [exact : ExactPairing X rightDual]
#align category_theory.has_right_dual CategoryTheory.HasRightDual

/-- A class of objects which have a left dual. -/
class HasLeftDual (Y : C) where
  leftDual : C
  [exact : ExactPairing leftDual Y]
#align category_theory.has_left_dual CategoryTheory.HasLeftDual

attribute [instance] HasRightDual.exact
attribute [instance] HasLeftDual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

prefix:1024 "ᘁ" => leftDual
postfix:1024 "ᘁ" => rightDual

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
  (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (𝟙 _ ⊗ f ⊗ 𝟙 _) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).hom
#align category_theory.right_adjoint_mate CategoryTheory.rightAdjointMate

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).hom
#align category_theory.left_adjoint_mate CategoryTheory.leftAdjointMate

notation f "ᘁ" => rightAdjointMate f
notation "ᘁ" f => leftAdjointMate f

@[simp]
theorem rightAdjointMate_id {X : C} [HasRightDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ) := by
  simp only [rightAdjointMate, MonoidalCategory.tensor_id, Category.id_comp,
    coevaluation_evaluation_assoc, Category.comp_id, Iso.inv_hom_id]
#align category_theory.right_adjoint_mate_id CategoryTheory.rightAdjointMate_id

@[simp]
theorem leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX) := by
  simp only [leftAdjointMate, MonoidalCategory.tensor_id, Category.id_comp,
    evaluation_coevaluation_assoc, Category.comp_id, Iso.inv_hom_id]
#align category_theory.left_adjoint_mate_id CategoryTheory.leftAdjointMate_id

theorem rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
    {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g =
      (ρ_ (Yᘁ)).inv ≫
        (𝟙 _ ⊗ η_ X (Xᘁ)) ≫ (𝟙 _ ⊗ f ⊗ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ (ε_ Y (Yᘁ) ⊗ 𝟙 _) ≫ (λ_ Z).hom := by
  dsimp only [rightAdjointMate]
  -- ⊢ ((ρ_ Yᘁ).inv ≫ (𝟙 Yᘁ ⊗ η_ X Xᘁ) ≫ (𝟙 Yᘁ ⊗ f ⊗ 𝟙 Xᘁ) ≫ (α_ Yᘁ Y Xᘁ).inv ≫ (ε_ …
  rw [Category.assoc, Category.assoc, associator_inv_naturality_assoc,
    associator_inv_naturality_assoc, ← tensor_id_comp_id_tensor g, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc, id_tensor_comp_tensor_id_assoc, ← leftUnitor_naturality,
    tensor_id_comp_id_tensor_assoc]
#align category_theory.right_adjoint_mate_comp CategoryTheory.rightAdjointMate_comp

theorem leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
    {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g =
      (λ_ _).inv ≫
        (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((g ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).hom := by
  dsimp only [leftAdjointMate]
  -- ⊢ ((λ_ ᘁY).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 ᘁY) ≫ ((𝟙 ᘁX ⊗ f) ⊗ 𝟙 ᘁY) ≫ (α_ (ᘁX) Y ᘁY).hom …
  rw [Category.assoc, Category.assoc, associator_naturality_assoc, associator_naturality_assoc, ←
    id_tensor_comp_tensor_id _ g, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    tensor_id_comp_id_tensor_assoc, ← rightUnitor_naturality, id_tensor_comp_tensor_id_assoc]
#align category_theory.left_adjoint_mate_comp CategoryTheory.leftAdjointMate_comp

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_rightAdjointMate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ := by
  rw [rightAdjointMate_comp]
  -- ⊢ (f ≫ g)ᘁ = (ρ_ Zᘁ).inv ≫ (𝟙 Zᘁ ⊗ η_ Y Yᘁ) ≫ (𝟙 Zᘁ ⊗ g ⊗ fᘁ) ≫ (α_ Zᘁ Z Xᘁ).i …
  simp only [rightAdjointMate, comp_tensor_id, Iso.cancel_iso_inv_left, id_tensor_comp,
    Category.assoc]
  symm
  -- ⊢ (𝟙 Zᘁ ⊗ η_ Y Yᘁ) ≫ (𝟙 Zᘁ ⊗ g ⊗ (ρ_ Yᘁ).inv ≫ (𝟙 Yᘁ ⊗ η_ X Xᘁ) ≫ (𝟙 Yᘁ ⊗ f ⊗  …
  iterate 5
    trans
    rw [← Category.id_comp g, tensor_comp]
  rw [← Category.assoc]
  -- ⊢ ((𝟙 Zᘁ ⊗ η_ Y Yᘁ) ≫ (𝟙 Zᘁ ⊗ (𝟙 Y ⊗ (ρ_ Yᘁ).inv) ≫ (𝟙 Y ⊗ 𝟙 Yᘁ ⊗ η_ X Xᘁ) ≫ ( …
  symm
  -- ⊢ (𝟙 Zᘁ ⊗ η_ X Xᘁ) ≫ (𝟙 Zᘁ ⊗ f ⊗ 𝟙 Xᘁ) ≫ (𝟙 Zᘁ ⊗ g ⊗ 𝟙 Xᘁ) ≫ (α_ Zᘁ Z Xᘁ).inv  …
  iterate 2
    trans
    rw [← Category.assoc]
  apply eq_whisker
  -- ⊢ ((𝟙 Zᘁ ⊗ η_ X Xᘁ) ≫ (𝟙 Zᘁ ⊗ f ⊗ 𝟙 Xᘁ)) ≫ (𝟙 Zᘁ ⊗ g ⊗ 𝟙 Xᘁ) = (𝟙 Zᘁ ⊗ η_ Y Yᘁ …
  repeat'
    -- Porting note: why do we need to fill in the implicit `C` here, and below?
    rw [← @id_tensor_comp C]
  congr 1
  -- ⊢ (η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ)) ≫ (g ⊗ 𝟙 Xᘁ) = η_ Y Yᘁ ≫ (𝟙 Y ⊗ (ρ_ Yᘁ).inv) ≫ (𝟙 Y ⊗ …
  rw [← id_tensor_comp_tensor_id (λ_ (Xᘁ)).hom g, id_tensor_rightUnitor_inv, Category.assoc,
    Category.assoc, rightUnitor_inv_naturality_assoc, ← associator_naturality_assoc, tensor_id,
    tensor_id_comp_id_tensor_assoc, ← associator_naturality_assoc]
  slice_rhs 2 3 =>
    rw [← tensor_comp, tensor_id, Category.comp_id, ← Category.id_comp (η_ Y (Yᘁ)), tensor_comp]
  rw [← id_tensor_comp_tensor_id _ (η_ Y (Yᘁ)), ← tensor_id]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ ((((((𝟙 (𝟙_ C) ⊗  …
  repeat' rw [@Category.assoc C]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ (𝟙 (𝟙_ C) ⊗ η_ X  …
  rw [pentagon_hom_inv_assoc, ← associator_naturality_assoc, associator_inv_naturality_assoc]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ (𝟙 (𝟙_ C) ⊗ η_ X  …
  slice_rhs 5 7 => rw [← comp_tensor_id, ← comp_tensor_id, evaluation_coevaluation, comp_tensor_id]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ (𝟙 (𝟙_ C) ⊗ η_ X  …
  rw [associator_inv_naturality_assoc]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ (𝟙 (𝟙_ C) ⊗ η_ X  …
  slice_rhs 4 5 => rw [← tensor_comp, leftUnitor_naturality, tensor_comp]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ (𝟙 (𝟙_ C) ⊗ η_ X  …
  repeat' rw [@Category.assoc C]
  -- ⊢ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ) ≫ (g ⊗ 𝟙 Xᘁ) = (ρ_ tensorUnit').inv ≫ (𝟙 (𝟙_ C) ⊗ η_ X  …
  rw [triangle_assoc_comp_right_inv_assoc, ← leftUnitor_tensor_assoc, leftUnitor_naturality_assoc,
    unitors_equal, ← Category.assoc, ← Category.assoc]
  simp
  -- 🎉 no goals
#align category_theory.comp_right_adjoint_mate CategoryTheory.comp_rightAdjointMate

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_leftAdjointMate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf := by
  rw [leftAdjointMate_comp]
  -- ⊢ (ᘁf ≫ g) = (λ_ ᘁZ).inv ≫ (η_ (ᘁY) Y ⊗ 𝟙 ᘁZ) ≫ (((ᘁf) ⊗ g) ⊗ 𝟙 ᘁZ) ≫ (α_ (ᘁX) …
  simp only [leftAdjointMate, id_tensor_comp, Iso.cancel_iso_inv_left, comp_tensor_id,
    Category.assoc]
  symm
  -- ⊢ (η_ (ᘁY) Y ⊗ 𝟙 ᘁZ) ≫ (((λ_ ᘁY).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 ᘁY) ≫ ((𝟙 ᘁX ⊗ f) ⊗ 𝟙 ᘁY …
  iterate 5
    trans
    rw [← Category.id_comp g, tensor_comp]
  rw [← Category.assoc]
  -- ⊢ ((η_ (ᘁY) Y ⊗ 𝟙 ᘁZ) ≫ (((λ_ ᘁY).inv ⊗ 𝟙 Y) ≫ ((η_ (ᘁX) X ⊗ 𝟙 ᘁY) ⊗ 𝟙 Y) ≫ (( …
  symm
  -- ⊢ (η_ (ᘁX) X ⊗ 𝟙 ᘁZ) ≫ ((𝟙 ᘁX ⊗ f) ⊗ 𝟙 ᘁZ) ≫ ((𝟙 ᘁX ⊗ g) ⊗ 𝟙 ᘁZ) ≫ (α_ (ᘁX) Z  …
  iterate 2
    trans
    rw [← Category.assoc]
  apply eq_whisker
  -- ⊢ ((η_ (ᘁX) X ⊗ 𝟙 ᘁZ) ≫ ((𝟙 ᘁX ⊗ f) ⊗ 𝟙 ᘁZ)) ≫ ((𝟙 ᘁX ⊗ g) ⊗ 𝟙 ᘁZ) = (η_ (ᘁY)  …
  repeat'
    -- Porting note: why do we need to fill in the implicit `C` here, and below?
    rw [← @comp_tensor_id C]
  congr 1
  -- ⊢ (η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f)) ≫ (𝟙 ᘁX ⊗ g) = η_ (ᘁY) Y ≫ ((λ_ ᘁY).inv ⊗ 𝟙 Y) ≫ (( …
  rw [← tensor_id_comp_id_tensor g (ρ_ (ᘁX)).hom, leftUnitor_inv_tensor_id, Category.assoc,
    Category.assoc, leftUnitor_inv_naturality_assoc, ← associator_inv_naturality_assoc, tensor_id,
    id_tensor_comp_tensor_id_assoc, ← associator_inv_naturality_assoc]
  slice_rhs 2 3 =>
    rw [← tensor_comp, tensor_id, Category.comp_id, ← Category.id_comp (η_ (ᘁY) Y), tensor_comp]
  rw [← tensor_id_comp_id_tensor (η_ (ᘁY) Y), ← tensor_id]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ ((((((η_ (ᘁX) X …
  repeat' rw [@Category.assoc C]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ (η_ (ᘁX) X ⊗ 𝟙  …
  rw [pentagon_inv_hom_assoc, ← associator_inv_naturality_assoc, associator_naturality_assoc]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ (η_ (ᘁX) X ⊗ 𝟙  …
  slice_rhs 5 7 => rw [← id_tensor_comp, ← id_tensor_comp, coevaluation_evaluation, id_tensor_comp]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ (η_ (ᘁX) X ⊗ 𝟙  …
  rw [associator_naturality_assoc]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ (η_ (ᘁX) X ⊗ 𝟙  …
  slice_rhs 4 5 => rw [← tensor_comp, rightUnitor_naturality, tensor_comp]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ (η_ (ᘁX) X ⊗ 𝟙  …
  repeat' rw [@Category.assoc C]
  -- ⊢ η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ≫ (𝟙 ᘁX ⊗ g) = (λ_ tensorUnit').inv ≫ (η_ (ᘁX) X ⊗ 𝟙  …
  rw [triangle_assoc_comp_left_inv_assoc, ← rightUnitor_tensor_assoc,
    rightUnitor_naturality_assoc, ← unitors_equal, ← Category.assoc, ← Category.assoc]
  simp
  -- 🎉 no goals
#align category_theory.comp_left_adjoint_mate CategoryTheory.comp_leftAdjointMate

/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
by "pulling the string on the left" up or down.

This gives the adjunction `tensorLeftAdjunction Y Y' : tensorLeft Y' ⊣ tensorLeft Y`.

This adjunction is often referred to as "Frobenius reciprocity" in the
fusion categories / planar algebras / subfactors literature.
-/
def tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z) where
  toFun f := (λ_ _).inv ≫ (η_ _ _ ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ f)
  invFun f := (𝟙 Y' ⊗ f) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).hom
  left_inv f := by
    dsimp
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv ≫ (η_ Y Y' ⊗ 𝟙 X) ≫ (α_ Y Y' X).hom ≫ (𝟙 Y ⊗ f)) ≫ (α_ Y' …
    simp only [id_tensor_comp]
    -- ⊢ ((𝟙 Y' ⊗ (λ_ X).inv) ≫ (𝟙 Y' ⊗ η_ Y Y' ⊗ 𝟙 X) ≫ (𝟙 Y' ⊗ (α_ Y Y' X).hom) ≫ ( …
    slice_lhs 4 5 => rw [associator_inv_naturality]
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ (𝟙 Y' ⊗ η_ Y Y' ⊗ 𝟙 X) ≫ (𝟙 Y' ⊗ (α_ Y Y' X).hom) ≫ (( …
    slice_lhs 5 6 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ (𝟙 Y' ⊗ η_ Y Y' ⊗ 𝟙 X) ≫ (𝟙 Y' ⊗ (α_ Y Y' X).hom) ≫ (α …
    slice_lhs 2 5 => simp only [← tensor_id, associator_inv_conjugation]
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ ((((α_ Y' tensorUnit' X).inv ≫ ((𝟙 Y' ⊗ η_ Y Y') ⊗ 𝟙 X …
    have c :
      (α_ Y' (Y ⊗ Y') X).hom ≫
          (𝟙 Y' ⊗ (α_ Y Y' X).hom) ≫ (α_ Y' Y (Y' ⊗ X)).inv ≫ (α_ (Y' ⊗ Y) Y' X).inv =
        (α_ _ _ _).inv ⊗ 𝟙 _
    pure_coherence
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ ((((α_ Y' tensorUnit' X).inv ≫ ((𝟙 Y' ⊗ η_ Y Y') ⊗ 𝟙 X …
    slice_lhs 4 7 => rw [c]
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ (α_ Y' tensorUnit' X).inv ≫ ((𝟙 Y' ⊗ η_ Y Y') ⊗ 𝟙 X) ≫ …
    slice_lhs 3 5 => rw [← comp_tensor_id, ← comp_tensor_id, coevaluation_evaluation]
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ (α_ Y' tensorUnit' X).inv ≫ ((((ρ_ Y').hom ≫ (λ_ Y').i …
    simp only [leftUnitor_conjugation]
    -- ⊢ (𝟙 Y' ⊗ (λ_ X).inv) ≫ (α_ Y' tensorUnit' X).inv ≫ ((((ρ_ Y').hom ≫ (λ_ Y').i …
    coherence
    -- 🎉 no goals
  right_inv f := by
    dsimp
    -- ⊢ (λ_ X).inv ≫ (η_ Y Y' ⊗ 𝟙 X) ≫ (α_ Y Y' X).hom ≫ (𝟙 Y ⊗ (𝟙 Y' ⊗ f) ≫ (α_ Y'  …
    simp only [id_tensor_comp]
    -- ⊢ (λ_ X).inv ≫ (η_ Y Y' ⊗ 𝟙 X) ≫ (α_ Y Y' X).hom ≫ (𝟙 Y ⊗ 𝟙 Y' ⊗ f) ≫ (𝟙 Y ⊗ ( …
    slice_lhs 3 4 => rw [← associator_naturality]
    -- ⊢ (λ_ X).inv ≫ (η_ Y Y' ⊗ 𝟙 X) ≫ (((((𝟙 Y ⊗ 𝟙 Y') ⊗ f) ≫ (α_ Y Y' (Y ⊗ Z)).hom …
    slice_lhs 2 3 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    -- ⊢ (λ_ X).inv ≫ (((((𝟙 tensorUnit' ⊗ f) ≫ (η_ Y Y' ⊗ 𝟙 (Y ⊗ Z))) ≫ (α_ Y Y' (Y  …
    slice_lhs 3 6 => simp only [← tensor_id, associator_inv_conjugation]
    -- ⊢ (λ_ X).inv ≫ (𝟙 tensorUnit' ⊗ f) ≫ (((α_ tensorUnit' Y Z).inv ≫ ((η_ Y Y' ⊗  …
    have c :
      (α_ (Y ⊗ Y') Y Z).hom ≫
          (α_ Y Y' (Y ⊗ Z)).hom ≫ (𝟙 Y ⊗ (α_ Y' Y Z).inv) ≫ (α_ Y (Y' ⊗ Y) Z).inv =
        (α_ _ _ _).hom ⊗ 𝟙 Z
    pure_coherence
    -- ⊢ (λ_ X).inv ≫ (𝟙 tensorUnit' ⊗ f) ≫ (((α_ tensorUnit' Y Z).inv ≫ ((η_ Y Y' ⊗  …
    slice_lhs 5 8 => rw [c]
    -- ⊢ (λ_ X).inv ≫ (𝟙 tensorUnit' ⊗ f) ≫ (α_ tensorUnit' Y Z).inv ≫ ((η_ Y Y' ⊗ 𝟙  …
    slice_lhs 4 6 => rw [← comp_tensor_id, ← comp_tensor_id, evaluation_coevaluation]
    -- ⊢ (λ_ X).inv ≫ (𝟙 tensorUnit' ⊗ f) ≫ (α_ tensorUnit' Y Z).inv ≫ (((λ_ Y).hom ≫ …
    simp only [leftUnitor_conjugation]
    -- ⊢ (λ_ X).inv ≫ ((λ_ X).hom ≫ f ≫ (λ_ (Y ⊗ Z)).inv) ≫ (α_ tensorUnit' Y Z).inv  …
    coherence
    -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv CategoryTheory.tensorLeftHomEquiv

/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')`
by "pulling the string on the right" up or down.
-/
def tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y') where
  toFun f := (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (α_ _ _ _).inv ≫ (f ⊗ 𝟙 _)
  invFun f := (f ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).hom
  left_inv f := by
    dsimp
    -- ⊢ ((ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Y') ≫ (α_ X Y Y').inv ≫ (f ⊗ 𝟙 Y') ⊗ 𝟙 Y) ≫ (α_ Z  …
    simp only [comp_tensor_id]
    -- ⊢ (((ρ_ X).inv ⊗ 𝟙 Y) ≫ ((𝟙 X ⊗ η_ Y Y') ⊗ 𝟙 Y) ≫ ((α_ X Y Y').inv ⊗ 𝟙 Y) ≫ (( …
    slice_lhs 4 5 => rw [associator_naturality]
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ ((𝟙 X ⊗ η_ Y Y') ⊗ 𝟙 Y) ≫ ((α_ X Y Y').inv ⊗ 𝟙 Y) ≫ ((( …
    slice_lhs 5 6 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ ((𝟙 X ⊗ η_ Y Y') ⊗ 𝟙 Y) ≫ ((α_ X Y Y').inv ⊗ 𝟙 Y) ≫ (α_ …
    slice_lhs 2 5 => simp only [← tensor_id, associator_conjugation]
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ ((((α_ X tensorUnit' Y).hom ≫ (𝟙 X ⊗ η_ Y Y' ⊗ 𝟙 Y) ≫ ( …
    have c :
      (α_ X (Y ⊗ Y') Y).inv ≫
          ((α_ X Y Y').inv ⊗ 𝟙 Y) ≫ (α_ (X ⊗ Y) Y' Y).hom ≫ (α_ X Y (Y' ⊗ Y)).hom =
        𝟙 _ ⊗ (α_ _ _ _).hom
    pure_coherence
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ ((((α_ X tensorUnit' Y).hom ≫ (𝟙 X ⊗ η_ Y Y' ⊗ 𝟙 Y) ≫ ( …
    slice_lhs 4 7 => rw [c]
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X tensorUnit' Y).hom ≫ (𝟙 X ⊗ η_ Y Y' ⊗ 𝟙 Y) ≫ (((( …
    slice_lhs 3 5 => rw [← id_tensor_comp, ← id_tensor_comp, evaluation_coevaluation]
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X tensorUnit' Y).hom ≫ (((𝟙 X ⊗ (λ_ Y).hom ≫ (ρ_ Y) …
    simp only [rightUnitor_conjugation]
    -- ⊢ ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X tensorUnit' Y).hom ≫ (((𝟙 X ⊗ (λ_ Y).hom ≫ (ρ_ Y) …
    coherence
    -- 🎉 no goals
  right_inv f := by
    dsimp
    -- ⊢ (ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Y') ≫ (α_ X Y Y').inv ≫ ((f ⊗ 𝟙 Y) ≫ (α_ Z Y' Y).ho …
    simp only [comp_tensor_id]
    -- ⊢ (ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Y') ≫ (α_ X Y Y').inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Y') ≫ ((α_ Z …
    slice_lhs 3 4 => rw [← associator_inv_naturality]
    -- ⊢ (ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Y') ≫ ((((f ⊗ 𝟙 Y ⊗ 𝟙 Y') ≫ (α_ (Z ⊗ Y') Y Y').inv) …
    slice_lhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    -- ⊢ (ρ_ X).inv ≫ (((((f ⊗ 𝟙 tensorUnit') ≫ (𝟙 (Z ⊗ Y') ⊗ η_ Y Y')) ≫ (α_ (Z ⊗ Y' …
    slice_lhs 3 6 => simp only [← tensor_id, associator_conjugation]
    -- ⊢ (ρ_ X).inv ≫ (f ⊗ 𝟙 tensorUnit') ≫ (((α_ Z Y' tensorUnit').hom ≫ (𝟙 Z ⊗ 𝟙 Y' …
    have c :
      (α_ Z Y' (Y ⊗ Y')).inv ≫
          (α_ (Z ⊗ Y') Y Y').inv ≫ ((α_ Z Y' Y).hom ⊗ 𝟙 Y') ≫ (α_ Z (Y' ⊗ Y) Y').hom =
        𝟙 _ ⊗ (α_ _ _ _).inv
    pure_coherence
    -- ⊢ (ρ_ X).inv ≫ (f ⊗ 𝟙 tensorUnit') ≫ (((α_ Z Y' tensorUnit').hom ≫ (𝟙 Z ⊗ 𝟙 Y' …
    slice_lhs 5 8 => rw [c]
    -- ⊢ (ρ_ X).inv ≫ (f ⊗ 𝟙 tensorUnit') ≫ (α_ Z Y' tensorUnit').hom ≫ (𝟙 Z ⊗ 𝟙 Y' ⊗ …
    slice_lhs 4 6 => rw [← id_tensor_comp, ← id_tensor_comp, coevaluation_evaluation]
    -- ⊢ (ρ_ X).inv ≫ (f ⊗ 𝟙 tensorUnit') ≫ (α_ Z Y' tensorUnit').hom ≫ ((𝟙 Z ⊗ (ρ_ Y …
    simp only [rightUnitor_conjugation]
    -- ⊢ (ρ_ X).inv ≫ ((ρ_ X).hom ≫ f ≫ (ρ_ (Z ⊗ Y')).inv) ≫ (α_ Z Y' tensorUnit').ho …
    coherence
    -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv CategoryTheory.tensorRightHomEquiv

theorem tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorLeftHomEquiv X Y Y' Z) f ≫ (𝟙 Y ⊗ g) := by
  dsimp [tensorLeftHomEquiv]
  -- ⊢ (λ_ X).inv ≫ (η_ Y Y' ⊗ 𝟙 X) ≫ (α_ Y Y' X).hom ≫ (𝟙 Y ⊗ f ≫ g) = ((λ_ X).inv …
  simp only [id_tensor_comp, Category.assoc]
  -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_naturality CategoryTheory.tensorLeftHomEquiv_naturality

theorem tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      (𝟙 _ ⊗ f) ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g := by
  dsimp [tensorLeftHomEquiv]
  -- ⊢ (𝟙 Y' ⊗ f ≫ g) ≫ (α_ Y' Y Z).inv ≫ (ε_ Y Y' ⊗ 𝟙 Z) ≫ (λ_ Z).hom = (𝟙 Y' ⊗ f) …
  simp only [id_tensor_comp, Category.assoc]
  -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_symm_naturality CategoryTheory.tensorLeftHomEquiv_symm_naturality

theorem tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensorRightHomEquiv X Y Y' Z) f ≫ (g ⊗ 𝟙 Y') := by
  dsimp [tensorRightHomEquiv]
  -- ⊢ (ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Y') ≫ (α_ X Y Y').inv ≫ (f ≫ g ⊗ 𝟙 Y') = ((ρ_ X).in …
  simp only [comp_tensor_id, Category.assoc]
  -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv_naturality CategoryTheory.tensorRightHomEquiv_naturality

theorem tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      (f ⊗ 𝟙 Y) ≫ (tensorRightHomEquiv X' Y Y' Z).symm g := by
  dsimp [tensorRightHomEquiv]
  -- ⊢ (f ≫ g ⊗ 𝟙 Y) ≫ (α_ Z Y' Y).hom ≫ (𝟙 Z ⊗ ε_ Y Y') ≫ (ρ_ Z).hom = (f ⊗ 𝟙 Y) ≫ …
  simp only [comp_tensor_id, Category.assoc]
  -- 🎉 no goals
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
`category_theory.monoidal.functor_has_left_dual`. Moreover, in concrete applications there is often
a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the closed
structure shouldn't come from `has_left_dual` (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic).
-/
def closedOfHasLeftDual (Y : C) [HasLeftDual Y] : Closed Y
    where isAdj := ⟨_, tensorLeftAdjunction (ᘁY) Y⟩
#align category_theory.closed_of_has_left_dual CategoryTheory.closedOfHasLeftDual

/-- `tensorLeftHomEquiv` commutes with tensoring on the right -/
theorem tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y ⊗ Z)
    (g : X' ⟶ Z') :
    (tensorLeftHomEquiv (X ⊗ X') Y Y' (Z ⊗ Z')).symm ((f ⊗ g) ≫ (α_ _ _ _).hom) =
      (α_ _ _ _).inv ≫ ((tensorLeftHomEquiv X Y Y' Z).symm f ⊗ g) := by
  dsimp [tensorLeftHomEquiv]
  -- ⊢ (𝟙 Y' ⊗ (f ⊗ g) ≫ (α_ Y Z Z').hom) ≫ (α_ Y' Y (Z ⊗ Z')).inv ≫ (ε_ Y Y' ⊗ 𝟙 ( …
  simp only [id_tensor_comp]
  -- ⊢ ((𝟙 Y' ⊗ f ⊗ g) ≫ (𝟙 Y' ⊗ (α_ Y Z Z').hom)) ≫ (α_ Y' Y (Z ⊗ Z')).inv ≫ (ε_ Y …
  simp only [associator_inv_conjugation]
  -- ⊢ (((α_ Y' X X').inv ≫ ((𝟙 Y' ⊗ f) ⊗ g) ≫ (α_ Y' (Y ⊗ Z) Z').hom) ≫ (𝟙 Y' ⊗ (α …
  slice_lhs 2 2 => rw [← id_tensor_comp_tensor_id]
  -- ⊢ (α_ Y' X X').inv ≫ ((((((𝟙 (Y' ⊗ X) ⊗ g) ≫ ((𝟙 Y' ⊗ f) ⊗ 𝟙 Z')) ≫ (α_ Y' (Y  …
  conv_rhs => rw [← id_tensor_comp_tensor_id, comp_tensor_id, comp_tensor_id]
  -- ⊢ (α_ Y' X X').inv ≫ ((((((𝟙 (Y' ⊗ X) ⊗ g) ≫ ((𝟙 Y' ⊗ f) ⊗ 𝟙 Z')) ≫ (α_ Y' (Y  …
  simp; coherence
  -- ⊢ (𝟙 (Y' ⊗ X) ⊗ g) ≫ (α_ Y' X Z').hom ≫ (𝟙 Y' ⊗ f ⊗ 𝟙 Z') ≫ (𝟙 Y' ⊗ (α_ Y Z Z' …
        -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_tensor CategoryTheory.tensorLeftHomEquiv_tensor

/-- `tensorRightHomEquiv` commutes with tensoring on the left -/
theorem tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z ⊗ Y')
    (g : X' ⟶ Z') :
    (tensorRightHomEquiv (X' ⊗ X) Y Y' (Z' ⊗ Z)).symm ((g ⊗ f) ≫ (α_ _ _ _).inv) =
      (α_ _ _ _).hom ≫ (g ⊗ (tensorRightHomEquiv X Y Y' Z).symm f) := by
  dsimp [tensorRightHomEquiv]
  -- ⊢ ((g ⊗ f) ≫ (α_ Z' Z Y').inv ⊗ 𝟙 Y) ≫ (α_ (Z' ⊗ Z) Y' Y).hom ≫ (𝟙 (Z' ⊗ Z) ⊗  …
  simp only [comp_tensor_id]
  -- ⊢ (((g ⊗ f) ⊗ 𝟙 Y) ≫ ((α_ Z' Z Y').inv ⊗ 𝟙 Y)) ≫ (α_ (Z' ⊗ Z) Y' Y).hom ≫ (𝟙 ( …
  simp only [associator_conjugation]
  -- ⊢ (((α_ X' X Y).hom ≫ (g ⊗ f ⊗ 𝟙 Y) ≫ (α_ Z' (Z ⊗ Y') Y).inv) ≫ ((α_ Z' Z Y'). …
  slice_lhs 2 2 => rw [← tensor_id_comp_id_tensor]
  -- ⊢ (α_ X' X Y).hom ≫ ((((((g ⊗ 𝟙 (X ⊗ Y)) ≫ (𝟙 Z' ⊗ f ⊗ 𝟙 Y)) ≫ (α_ Z' (Z ⊗ Y') …
  conv_rhs => rw [← tensor_id_comp_id_tensor, id_tensor_comp, id_tensor_comp]
  -- ⊢ (α_ X' X Y).hom ≫ ((((((g ⊗ 𝟙 (X ⊗ Y)) ≫ (𝟙 Z' ⊗ f ⊗ 𝟙 Y)) ≫ (α_ Z' (Z ⊗ Y') …
  simp only [← tensor_id, associator_conjugation]
  -- ⊢ (α_ X' X Y).hom ≫ ((((((g ⊗ 𝟙 X ⊗ 𝟙 Y) ≫ (𝟙 Z' ⊗ f ⊗ 𝟙 Y)) ≫ (α_ Z' (Z ⊗ Y') …
  simp; coherence
  -- ⊢ (g ⊗ f ⊗ 𝟙 Y) ≫ (α_ Z' (Z ⊗ Y') Y).inv ≫ ((α_ Z' Z Y').inv ⊗ 𝟙 Y) ≫ (α_ (Z'  …
        -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv_tensor CategoryTheory.tensorRightHomEquiv_tensor

@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_id_tensor {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ (𝟙 Y ⊗ f)) = (ρ_ _).hom ≫ f := by
  dsimp [tensorLeftHomEquiv]
  -- ⊢ (𝟙 Y' ⊗ η_ Y Y' ≫ (𝟙 Y ⊗ f)) ≫ (α_ Y' Y Z).inv ≫ (ε_ Y Y' ⊗ 𝟙 Z) ≫ (λ_ Z).ho …
  rw [id_tensor_comp]
  -- ⊢ ((𝟙 Y' ⊗ η_ Y Y') ≫ (𝟙 Y' ⊗ 𝟙 Y ⊗ f)) ≫ (α_ Y' Y Z).inv ≫ (ε_ Y Y' ⊗ 𝟙 Z) ≫  …
  slice_lhs 2 3 => rw [associator_inv_naturality]
  -- ⊢ (𝟙 Y' ⊗ η_ Y Y') ≫ (((α_ Y' Y Y').inv ≫ ((𝟙 Y' ⊗ 𝟙 Y) ⊗ f)) ≫ (ε_ Y Y' ⊗ 𝟙 Z …
  slice_lhs 3 4 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- ⊢ (𝟙 Y' ⊗ η_ Y Y') ≫ (α_ Y' Y Y').inv ≫ ((ε_ Y Y' ⊗ 𝟙 Y') ≫ (𝟙 (𝟙_ C) ⊗ f)) ≫  …
  slice_lhs 1 3 => rw [coevaluation_evaluation]
  -- ⊢ (((ρ_ Y').hom ≫ (λ_ Y').inv) ≫ (𝟙 (𝟙_ C) ⊗ f)) ≫ (λ_ Z).hom = (ρ_ Y').hom ≫ f
  simp
  -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_id_tensor CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_id_tensor

@[simp]
theorem tensorLeftHomEquiv_symm_coevaluation_comp_tensor_id {X Y : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) :
    (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ (f ⊗ 𝟙 (Xᘁ))) = (ρ_ _).hom ≫ fᘁ := by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  -- ⊢ (𝟙 Yᘁ ⊗ η_ X Xᘁ ≫ (f ⊗ 𝟙 Xᘁ)) ≫ (α_ Yᘁ Y Xᘁ).inv ≫ (ε_ Y Yᘁ ⊗ 𝟙 Xᘁ) ≫ (λ_ Xᘁ …
  simp
  -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_tensor_id CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_tensor_id

@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_id_tensor {X Y : C} [HasLeftDual X]
    [HasLeftDual Y] (f : X ⟶ Y) :
    (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (ᘁX) X ≫ (𝟙 (ᘁX) ⊗ f)) = (λ_ _).hom ≫ ᘁf := by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  -- ⊢ (η_ (ᘁX) X ≫ (𝟙 ᘁX ⊗ f) ⊗ 𝟙 ᘁY) ≫ (α_ (ᘁX) Y ᘁY).hom ≫ (𝟙 ᘁX ⊗ ε_ (ᘁY) Y) ≫  …
  simp
  -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_id_tensor CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_id_tensor

@[simp]
theorem tensorRightHomEquiv_symm_coevaluation_comp_tensor_id {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ (f ⊗ 𝟙 Y')) = (λ_ _).hom ≫ f := by
  dsimp [tensorRightHomEquiv]
  -- ⊢ (η_ Y Y' ≫ (f ⊗ 𝟙 Y') ⊗ 𝟙 Y) ≫ (α_ Z Y' Y).hom ≫ (𝟙 Z ⊗ ε_ Y Y') ≫ (ρ_ Z).ho …
  rw [comp_tensor_id]
  -- ⊢ ((η_ Y Y' ⊗ 𝟙 Y) ≫ ((f ⊗ 𝟙 Y') ⊗ 𝟙 Y)) ≫ (α_ Z Y' Y).hom ≫ (𝟙 Z ⊗ ε_ Y Y') ≫ …
  slice_lhs 2 3 => rw [associator_naturality]
  -- ⊢ (η_ Y Y' ⊗ 𝟙 Y) ≫ (((α_ Y Y' Y).hom ≫ (f ⊗ 𝟙 Y' ⊗ 𝟙 Y)) ≫ (𝟙 Z ⊗ ε_ Y Y')) ≫ …
  slice_lhs 3 4 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- ⊢ (η_ Y Y' ⊗ 𝟙 Y) ≫ (α_ Y Y' Y).hom ≫ ((𝟙 Y ⊗ ε_ Y Y') ≫ (f ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ …
  slice_lhs 1 3 => rw [evaluation_coevaluation]
  -- ⊢ (((λ_ Y).hom ≫ (ρ_ Y).inv) ≫ (f ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ Z).hom = (λ_ Y).hom ≫ f
  simp
  -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_tensor_id CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_tensor_id

@[simp]
theorem tensorLeftHomEquiv_id_tensor_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) :
    (tensorLeftHomEquiv _ _ _ _) ((𝟙 Z ⊗ f) ≫ ε_ _ _) = f ≫ (ρ_ _).inv := by
  dsimp [tensorLeftHomEquiv]
  -- ⊢ (λ_ Y).inv ≫ (η_ (ᘁZ) Z ⊗ 𝟙 Y) ≫ (α_ (ᘁZ) Z Y).hom ≫ (𝟙 ᘁZ ⊗ (𝟙 Z ⊗ f) ≫ ε_  …
  rw [id_tensor_comp]
  -- ⊢ (λ_ Y).inv ≫ (η_ (ᘁZ) Z ⊗ 𝟙 Y) ≫ (α_ (ᘁZ) Z Y).hom ≫ (𝟙 ᘁZ ⊗ 𝟙 Z ⊗ f) ≫ (𝟙 ᘁ …
  slice_lhs 3 4 => rw [← associator_naturality]
  -- ⊢ (λ_ Y).inv ≫ (η_ (ᘁZ) Z ⊗ 𝟙 Y) ≫ (((𝟙 ᘁZ ⊗ 𝟙 Z) ⊗ f) ≫ (α_ (ᘁZ) Z ᘁZ).hom) ≫ …
  slice_lhs 2 3 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- ⊢ (λ_ Y).inv ≫ (((𝟙 tensorUnit' ⊗ f) ≫ (η_ (ᘁZ) Z ⊗ 𝟙 ᘁZ)) ≫ (α_ (ᘁZ) Z ᘁZ).ho …
  slice_lhs 3 5 => rw [evaluation_coevaluation]
  -- ⊢ (λ_ Y).inv ≫ (𝟙 tensorUnit' ⊗ f) ≫ (λ_ ᘁZ).hom ≫ (ρ_ ᘁZ).inv = f ≫ (ρ_ ᘁZ).inv
  simp
  -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_id_tensor_comp_evaluation CategoryTheory.tensorLeftHomEquiv_id_tensor_comp_evaluation

@[simp]
theorem tensorLeftHomEquiv_tensor_id_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) ((f ⊗ 𝟙 _) ≫ ε_ _ _) = (ᘁf) ≫ (ρ_ _).inv := by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  -- ⊢ (λ_ ᘁY).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 ᘁY) ≫ (α_ (ᘁX) X ᘁY).hom ≫ (𝟙 ᘁX ⊗ (f ⊗ 𝟙 ᘁY) ≫ …
  simp
  -- 🎉 no goals
#align category_theory.tensor_left_hom_equiv_tensor_id_comp_evaluation CategoryTheory.tensorLeftHomEquiv_tensor_id_comp_evaluation

@[simp]
theorem tensorRightHomEquiv_id_tensor_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((𝟙 (Yᘁ) ⊗ f) ≫ ε_ _ _) = fᘁ ≫ (λ_ _).inv := by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  -- ⊢ (ρ_ Yᘁ).inv ≫ (𝟙 Yᘁ ⊗ η_ X Xᘁ) ≫ (α_ Yᘁ X Xᘁ).inv ≫ ((𝟙 Yᘁ ⊗ f) ≫ ε_ Y Yᘁ ⊗  …
  simp
  -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv_id_tensor_comp_evaluation CategoryTheory.tensorRightHomEquiv_id_tensor_comp_evaluation

@[simp]
theorem tensorRightHomEquiv_tensor_id_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ) :
    (tensorRightHomEquiv _ _ _ _) ((f ⊗ 𝟙 X) ≫ ε_ X (Xᘁ)) = f ≫ (λ_ _).inv := by
  dsimp [tensorRightHomEquiv]
  -- ⊢ (ρ_ Y).inv ≫ (𝟙 Y ⊗ η_ X Xᘁ) ≫ (α_ Y X Xᘁ).inv ≫ ((f ⊗ 𝟙 X) ≫ ε_ X Xᘁ ⊗ 𝟙 Xᘁ …
  rw [comp_tensor_id]
  -- ⊢ (ρ_ Y).inv ≫ (𝟙 Y ⊗ η_ X Xᘁ) ≫ (α_ Y X Xᘁ).inv ≫ ((f ⊗ 𝟙 X) ⊗ 𝟙 Xᘁ) ≫ (ε_ X  …
  slice_lhs 3 4 => rw [← associator_inv_naturality]
  -- ⊢ (ρ_ Y).inv ≫ (𝟙 Y ⊗ η_ X Xᘁ) ≫ ((f ⊗ 𝟙 X ⊗ 𝟙 Xᘁ) ≫ (α_ Xᘁ X Xᘁ).inv) ≫ (ε_ X …
  slice_lhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- ⊢ (ρ_ Y).inv ≫ (((f ⊗ 𝟙 tensorUnit') ≫ (𝟙 Xᘁ ⊗ η_ X Xᘁ)) ≫ (α_ Xᘁ X Xᘁ).inv) ≫ …
  slice_lhs 3 5 => rw [coevaluation_evaluation]
  -- ⊢ (ρ_ Y).inv ≫ (f ⊗ 𝟙 tensorUnit') ≫ (ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv = f ≫ (λ_ Xᘁ).inv
  simp
  -- 🎉 no goals
#align category_theory.tensor_right_hom_equiv_tensor_id_comp_evaluation CategoryTheory.tensorRightHomEquiv_tensor_id_comp_evaluation

-- Next four lemmas passing `fᘁ` or `ᘁf` through (co)evaluations.
theorem coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ (𝟙 _ ⊗ fᘁ) = η_ _ _ ≫ (f ⊗ 𝟙 _) := by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  -- ⊢ ↑(tensorLeftHomEquiv (𝟙_ C) Y Yᘁ Xᘁ).symm (η_ Y Yᘁ ≫ (𝟙 Y ⊗ fᘁ)) = ↑(tensorL …
  simp
  -- 🎉 no goals
#align category_theory.coevaluation_comp_right_adjoint_mate CategoryTheory.coevaluation_comp_rightAdjointMate

theorem leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    (𝟙 X ⊗ ᘁf) ≫ ε_ _ _ = (f ⊗ 𝟙 _) ≫ ε_ _ _ := by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  -- ⊢ ↑(tensorLeftHomEquiv (ᘁY) (ᘁX) X (𝟙_ C)) ((𝟙 X ⊗ ᘁf) ≫ ε_ (ᘁX) X) = ↑(tensor …
  simp
  -- 🎉 no goals
#align category_theory.left_adjoint_mate_comp_evaluation CategoryTheory.leftAdjointMate_comp_evaluation

theorem coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ ((ᘁf) ⊗ 𝟙 Y) = η_ (ᘁX) X ≫ (𝟙 (ᘁX) ⊗ f) := by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  -- ⊢ ↑(tensorRightHomEquiv (𝟙_ C) (ᘁY) Y ᘁX).symm (η_ (ᘁY) Y ≫ ((ᘁf) ⊗ 𝟙 Y)) = ↑( …
  simp
  -- 🎉 no goals
#align category_theory.coevaluation_comp_left_adjoint_mate CategoryTheory.coevaluation_comp_leftAdjointMate

theorem rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ⊗ 𝟙 X) ≫ ε_ X (Xᘁ) = (𝟙 (Yᘁ) ⊗ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  -- ⊢ ↑(tensorRightHomEquiv Yᘁ X Xᘁ (𝟙_ C)) ((fᘁ ⊗ 𝟙 X) ≫ ε_ X Xᘁ) = ↑(tensorRight …
  simp
  -- 🎉 no goals
#align category_theory.right_adjoint_mate_comp_evaluation CategoryTheory.rightAdjointMate_comp_evaluation

/-- Transport an exact pairing across an isomorphism in the first argument. -/
def exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : ExactPairing X Y where
  evaluation' := (𝟙 Y ⊗ i.hom) ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ (i.inv ⊗ 𝟙 Y)
  evaluation_coevaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    -- ⊢ ((η_ X' Y ⊗ 𝟙 X) ≫ ((i.inv ⊗ 𝟙 Y) ⊗ 𝟙 X)) ≫ (α_ X Y X).hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ i. …
    slice_lhs 2 3 => rw [associator_naturality]
    -- ⊢ (η_ X' Y ⊗ 𝟙 X) ≫ (((α_ X' Y X).hom ≫ (i.inv ⊗ 𝟙 Y ⊗ 𝟙 X)) ≫ (𝟙 X ⊗ 𝟙 Y ⊗ i. …
    slice_lhs 3 4 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    -- ⊢ (η_ X' Y ⊗ 𝟙 X) ≫ (α_ X' Y X).hom ≫ ((𝟙 X' ⊗ 𝟙 Y ⊗ i.hom) ≫ (i.inv ⊗ 𝟙 (Y ⊗  …
    slice_lhs 4 5 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    -- ⊢ (η_ X' Y ⊗ 𝟙 X) ≫ (α_ X' Y X).hom ≫ (𝟙 X' ⊗ 𝟙 Y ⊗ i.hom) ≫ (𝟙 X' ⊗ ε_ X' Y)  …
    slice_lhs 2 3 => rw [← associator_naturality]
    -- ⊢ (η_ X' Y ⊗ 𝟙 X) ≫ ((((𝟙 X' ⊗ 𝟙 Y) ⊗ i.hom) ≫ (α_ X' Y X').hom) ≫ (𝟙 X' ⊗ ε_  …
    slice_lhs 1 2 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
    -- ⊢ ((((𝟙 (𝟙_ C) ⊗ i.hom) ≫ (η_ X' Y ⊗ 𝟙 X')) ≫ (α_ X' Y X').hom) ≫ (𝟙 X' ⊗ ε_ X …
    -- ⊢ ((𝟙 Y ⊗ η_ X' Y) ≫ (𝟙 Y ⊗ i.inv ⊗ 𝟙 Y)) ≫ (α_ Y X Y).inv ≫ ((𝟙 Y ⊗ i.hom) ⊗  …
    slice_lhs 2 4 => rw [evaluation_coevaluation]
    -- ⊢ (𝟙 Y ⊗ η_ X' Y) ≫ (𝟙 Y ⊗ i.inv ⊗ 𝟙 Y) ≫ (𝟙 Y ⊗ i.hom ⊗ 𝟙 Y) ≫ (α_ Y X' Y).in …
    -- ⊢ (𝟙 (𝟙_ C) ⊗ i.hom) ≫ ((λ_ X').hom ≫ (ρ_ X').inv) ≫ (i.inv ⊗ 𝟙 (𝟙_ C)) = (λ_  …
    slice_lhs 1 2 => rw [leftUnitor_naturality]
    -- ⊢ (((λ_ X).hom ≫ i.hom) ≫ (ρ_ X').inv) ≫ (i.inv ⊗ 𝟙 (𝟙_ C)) = (λ_ X).hom ≫ (ρ_ …
    slice_lhs 3 4 => rw [← rightUnitor_inv_naturality]
    -- 🎉 no goals
    -- ⊢ (λ_ X).hom ≫ i.hom ≫ i.inv ≫ (ρ_ X).inv = (λ_ X).hom ≫ (ρ_ X).inv
    simp
    -- 🎉 no goals
  coevaluation_evaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    simp only [Iso.inv_hom_id_assoc, associator_conjugation, Category.assoc]
    slice_lhs 2 3 =>
      rw [← tensor_comp]
      simp
    simp
#align category_theory.exact_pairing_congr_left CategoryTheory.exactPairingCongrLeft

/-- Transport an exact pairing across an isomorphism in the second argument. -/
def exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : ExactPairing X Y where
  evaluation' := (i.hom ⊗ 𝟙 X) ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ (𝟙 X ⊗ i.inv)
  evaluation_coevaluation' := by
    rw [id_tensor_comp, comp_tensor_id]
    -- ⊢ ((η_ X Y' ⊗ 𝟙 X) ≫ ((𝟙 X ⊗ i.inv) ⊗ 𝟙 X)) ≫ (α_ X Y X).hom ≫ (𝟙 X ⊗ i.hom ⊗  …
    simp only [Iso.inv_hom_id_assoc, associator_conjugation, Category.assoc]
    -- ⊢ (η_ X Y' ⊗ 𝟙 X) ≫ (α_ X Y' X).hom ≫ (𝟙 X ⊗ i.inv ⊗ 𝟙 X) ≫ (𝟙 X ⊗ i.hom ⊗ 𝟙 X …
    slice_lhs 3 4 =>
      rw [← tensor_comp]
      simp
    simp
    -- ⊢ ((𝟙 Y ⊗ η_ X Y') ≫ (𝟙 Y ⊗ 𝟙 X ⊗ i.inv)) ≫ (α_ Y X Y).inv ≫ ((i.hom ⊗ 𝟙 X) ⊗  …
    -- 🎉 no goals
    -- ⊢ (𝟙 Y ⊗ η_ X Y') ≫ (𝟙 Y ⊗ 𝟙 X ⊗ i.inv) ≫ ((i.hom ⊗ 𝟙 X ⊗ 𝟙 Y) ≫ (α_ Y' X Y).i …
  coevaluation_evaluation' := by
    -- ⊢ (𝟙 Y ⊗ η_ X Y') ≫ (((i.hom ⊗ 𝟙 (X ⊗ Y')) ≫ (𝟙 Y' ⊗ 𝟙 X ⊗ i.inv)) ≫ (α_ Y' X  …
    rw [id_tensor_comp, comp_tensor_id]
    -- ⊢ ((((i.hom ⊗ 𝟙 (𝟙_ C)) ≫ (𝟙 Y' ⊗ η_ X Y')) ≫ (𝟙 Y' ⊗ 𝟙 X ⊗ i.inv)) ≫ (α_ Y' X …
    slice_lhs 3 4 => rw [← associator_inv_naturality]
    -- ⊢ (i.hom ⊗ 𝟙 (𝟙_ C)) ≫ (𝟙 Y' ⊗ η_ X Y') ≫ ((α_ Y' X Y').inv ≫ ((𝟙 Y' ⊗ 𝟙 X) ⊗  …
    slice_lhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    -- ⊢ (i.hom ⊗ 𝟙 (𝟙_ C)) ≫ (𝟙 Y' ⊗ η_ X Y') ≫ (α_ Y' X Y').inv ≫ (ε_ X Y' ⊗ 𝟙 Y')  …
    slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    -- ⊢ (i.hom ⊗ 𝟙 (𝟙_ C)) ≫ ((ρ_ Y').hom ≫ (λ_ Y').inv) ≫ (𝟙 (𝟙_ C) ⊗ i.inv) = (ρ_  …
    slice_lhs 3 4 => rw [associator_inv_naturality]
    -- ⊢ (((ρ_ Y).hom ≫ i.hom) ≫ (λ_ Y').inv) ≫ (𝟙 (𝟙_ C) ⊗ i.inv) = (ρ_ Y).hom ≫ (λ_ …
    slice_lhs 4 5 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    -- ⊢ (ρ_ Y).hom ≫ i.hom ≫ i.inv ≫ (λ_ Y).inv = (ρ_ Y).hom ≫ (λ_ Y).inv
    slice_lhs 2 4 => rw [coevaluation_evaluation]
    -- 🎉 no goals
    slice_lhs 1 2 => rw [rightUnitor_naturality]
    slice_lhs 3 4 => rw [← leftUnitor_inv_naturality]
    simp
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
    -- 🎉 no goals
  inv_hom_id := by
    rw [← @comp_rightAdjointMate C _ _ X X X ⟨Y₂⟩ ⟨Y₁⟩ ⟨Y₂⟩, Category.comp_id,
      @rightAdjointMate_id _ _ _ _ ⟨Y₂⟩]
    rfl
    -- 🎉 no goals
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
    -- 🎉 no goals
  inv_hom_id := by
    rw [← @comp_leftAdjointMate C _ _ Y Y Y ⟨X₂⟩ ⟨X₁⟩ ⟨X₂⟩, Category.comp_id,
      @leftAdjointMate_id _ _ _ _ ⟨X₂⟩]
    rfl
    -- 🎉 no goals
#align category_theory.left_dual_iso CategoryTheory.leftDualIso

@[simp]
theorem rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by
  ext
  -- ⊢ (rightDualIso p p).hom = (Iso.refl Y).hom
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id _ _ _ _ ⟨Y⟩]
  -- 🎉 no goals
#align category_theory.right_dual_iso_id CategoryTheory.rightDualIso_id

@[simp]
theorem leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by
  ext
  -- ⊢ (leftDualIso p p).hom = (Iso.refl X).hom
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id _ _ _ _ ⟨X⟩]
  -- 🎉 no goals
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
`category_theory.monoidal.left_rigid_functor_category`. Moreover, in concrete applications there is
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

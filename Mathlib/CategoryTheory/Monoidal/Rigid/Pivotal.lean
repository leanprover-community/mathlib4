/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Pivotal monoidal categories

A pivotal category is a rigid monoidal category equipped with a monoidal natural isomorphism
from the identity functor to the double right dual functor (`X ↦ Xᘁᘁ`).

## Main definitions

* `pivotalExactPairing X`: an exact pairing between `Xᘁ` and `X` in a pivotal category.
* `leftDualIsoRightDual X`: an isomorphism `ᘁX ≅ Xᘁ` in a pivotal category.
* `dualFunctorIso`: a natural isomorphism between the left and right dual functors in a
  pivotal category.

## Tags

rigid category, monoidal category, pivotal category

-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

section

namespace CategoryTheory

/-- A pivotal category is a rigid monoidal category equipped with a monoidal natural
isomorphism from the identity functor to the double right dual functor. -/
class PivotalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] where
  /-- A natural isomorphism from the identity to the double right dual. -/
  pivotalIso : 𝟭 C ≅ doubleRightDualFunctor C
  pivotalIso_isMonoidal : NatTrans.IsMonoidal pivotalIso.hom := by infer_instance

attribute [instance] PivotalCategory.pivotalIso_isMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C]

/-- The chosen natural isomorphism from the identity to the double right dual. -/
abbrev pivotalIso : 𝟭 C ≅ doubleRightDualFunctor C := PivotalCategory.pivotalIso

set_option backward.isDefEq.respectTransparency false in
lemma rightAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    (fᘁ)ᘁ = (pivotalIso.app X).inv ≫ f ≫ (pivotalIso.app Y).hom := by
  rw [← cancel_mono (pivotalIso.app Y).inv]
  erw [pivotalIso.inv.naturality]
  simp

/-- In a pivotal category, `X` is a left dual of its right dual `Xᘁ`. -/
@[implicit_reducible]
def pivotalExactPairing (X : C) : ExactPairing Xᘁ X :=
  let : ExactPairing Xᘁ ((doubleRightDualFunctor C).obj X) := HasRightDual.exact
  exactPairingCongrRight (pivotalIso.app X)

@[simp]
lemma pivotalExactPairing_coevaluation (X : C) :
    letI := pivotalExactPairing X
    η_ Xᘁ X = η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ (pivotalIso.app X).inv := rfl

@[simp]
lemma pivotalExactPairing_evaluation (X : C) :
    letI := pivotalExactPairing X
    ε_ Xᘁ X = (pivotalIso.app X).hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ := rfl

/-- In a pivotal category, left and right duals are isomorphic. -/
def leftDualIsoRightDual (X : C) : (ᘁX) ≅ Xᘁ :=
  leftDualIso HasLeftDual.exact (pivotalExactPairing X)

omit [PivotalCategory C] in
private lemma leftAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    leftAdjointMate (rightAdjointMate f) = f := by
  rw [← cancel_mono (ρ_ Y).inv]
  have h : _ ≫ ε_ Y Yᘁ = _ :=
    (leftAdjointMate_comp_evaluation (fᘁ)).trans (rightAdjointMate_comp_evaluation f)
  have e (g : X ⟶ Y) :=
    @tensorLeftHomEquiv_whiskerLeft_comp_evaluation C _ _ X (Yᘁ) ⟨Y⟩ g
  change ∀ g, (tensorLeftHomEquiv X Y (Yᘁ) (𝟙_ C))
    ((Yᘁ) ◁ g ≫ ε_ Y (Yᘁ)) = g ≫ (ρ_ Y).inv at e
  rw [← e, h, e]

private lemma pivotalLeftAdjointMate {X Y : C} (f : X ⟶ Y) :
    letI : HasLeftDual X := { leftDual := Xᘁ, exact := pivotalExactPairing X }
    letI : HasLeftDual Y := { leftDual := Yᘁ, exact := pivotalExactPairing Y }
  leftAdjointMate f = fᘁ := by
  rw [← leftAdjointMate_rightAdjointMate (fᘁ), rightAdjointMate_rightAdjointMate]
  dsimp only [leftAdjointMate]
  rw [pivotalExactPairing_coevaluation, pivotalExactPairing_evaluation]
  monoidal

@[reassoc]
lemma leftDualIsoRightDual_hom_naturality {X Y : C} (f : X ⟶ Y) :
    (ᘁf) ≫ (leftDualIsoRightDual X).hom = (leftDualIsoRightDual Y).hom ≫ fᘁ := by
  simp [leftDualIsoRightDual, leftDualIso, ← @comp_leftAdjointMate, ← pivotalLeftAdjointMate f,
    ← @comp_leftAdjointMate]

@[reassoc]
lemma leftDualIsoRightDual_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (leftDualIsoRightDual Y).inv ≫ (ᘁf) = fᘁ ≫ (leftDualIsoRightDual X).inv := by
  simp [← cancel_mono (leftDualIsoRightDual X).hom, leftDualIsoRightDual_hom_naturality]

/-- The left and right dual functors are isomorphic. -/
@[simps!]
def dualFunctorIso :
    leftDualFunctor C ≅ rightDualFunctor C :=
  NatIso.ofComponents
    (fun X ↦ (leftDualIsoRightDual X).symm.op.mop)
    (fun f ↦ MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj (leftDualIsoRightDual_inv_naturality f)))

end CategoryTheory

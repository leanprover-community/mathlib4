/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Drinfeld

/-!
# Pivotal monoidal categories

A pivotal category is a right rigid monoidal category equipped with a monoidal natural isomorphism
from the identity functor to the double right dual functor (`X ↦ Xᘁᘁ`).

## Main definitions

* `PivotalCategory`: a right rigid monoidal category equipped with a monoidal natural isomorphism
  from the identity functor to the double right dual functor.
* `pivotalExactPairing X`: an exact pairing between `Xᘁ` and `X` in a pivotal category.
* `leftDualIsoRightDual X`: an isomorphism `ᘁX ≅ Xᘁ` in a pivotal category.
* `dualFunctorIso`: a natural isomorphism between the left and right dual functors in a
  pivotal category.
* `symmetricPivotalCategory`: the canonical pivotal structure on a right rigid symmetric
  monoidal category, given by the Drinfeld isomorphism.

## Tags

rigid category, monoidal category, pivotal category

-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

section

namespace CategoryTheory

/-- A pivotal category is a right rigid monoidal category equipped with a monoidal natural
isomorphism from the identity functor to the double right dual functor. -/
class PivotalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] where
  /-- A natural isomorphism from the identity to the double right dual. -/
  pivotalIso : 𝟭 C ≅ doubleRightDualFunctor C
  pivotalIso_isMonoidal : NatTrans.IsMonoidal pivotalIso.hom := by infer_instance

attribute [instance] PivotalCategory.pivotalIso_isMonoidal

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [SymmetricCategory C]

/-- The canonical pivotal structure on a right rigid symmetric monoidal category, selecting the
Drinfeld isomorphism as its pivotal isomorphism. -/
instance symmetricPivotalCategory : PivotalCategory C where
  pivotalIso := drinfeldIso C

end Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [PivotalCategory C]

lemma rightAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    fᘁᘁ = (PivotalCategory.pivotalIso.app X).inv ≫ f ≫
      (PivotalCategory.pivotalIso.app Y).hom := by
  change (doubleRightDualFunctor C).map f = _
  rw [← cancel_mono (PivotalCategory.pivotalIso.inv.app Y)]
  simpa using PivotalCategory.pivotalIso.inv.naturality f

/-- In a pivotal category, `X` is a left dual of its right dual `Xᘁ`. -/
@[implicit_reducible]
def pivotalExactPairing (X : C) : ExactPairing Xᘁ X :=
  let : ExactPairing Xᘁ ((doubleRightDualFunctor C).obj X) := HasRightDual.exact
  exactPairingCongrRight (PivotalCategory.pivotalIso.app X)

lemma pivotalExactPairing_coevaluation (X : C) :
    letI := pivotalExactPairing X
    η_ Xᘁ X = η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ (PivotalCategory.pivotalIso.app X).inv := rfl

lemma pivotalExactPairing_evaluation (X : C) :
    letI := pivotalExactPairing X
    ε_ Xᘁ X = (PivotalCategory.pivotalIso.app X).hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ := rfl

/-- In a pivotal category, left and right duals are isomorphic. -/
def leftDualIsoRightDual (X : C) [HasLeftDual X] : (ᘁX) ≅ Xᘁ :=
  leftDualIso HasLeftDual.exact (pivotalExactPairing X)

lemma pivotal_adjointMate {X Y : C} (f : X ⟶ Y) :
    letI : HasLeftDual X := (pivotalExactPairing X).hasLeftDual
    letI : HasLeftDual Y := (pivotalExactPairing Y).hasLeftDual
  (ᘁf) = fᘁ := by
  unfold ExactPairing.hasLeftDual
  rw [← leftAdjointMate_rightAdjointMate (fᘁ), rightAdjointMate_rightAdjointMate]
  dsimp only [leftAdjointMate]
  rw [pivotalExactPairing_coevaluation, pivotalExactPairing_evaluation]
  monoidal

@[reassoc]
lemma leftDualIsoRightDual_hom_naturality {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) :
    (ᘁf) ≫ (leftDualIsoRightDual X).hom = (leftDualIsoRightDual Y).hom ≫ fᘁ := by
  simp [leftDualIsoRightDual, leftDualIso, ← @comp_leftAdjointMate, ← pivotal_adjointMate f,
    ← @comp_leftAdjointMate]

@[reassoc]
lemma leftDualIsoRightDual_inv_naturality {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) :
    (leftDualIsoRightDual Y).inv ≫ (ᘁf) = fᘁ ≫ (leftDualIsoRightDual X).inv := by
  simp [← cancel_mono (leftDualIsoRightDual X).hom, leftDualIsoRightDual_hom_naturality]

/-- The left and right dual functors are isomorphic. -/
@[simps!]
def dualFunctorIso [LeftRigidCategory C] :
    leftDualFunctor C ≅ rightDualFunctor C :=
  NatIso.ofComponents
    (fun X ↦ (leftDualIsoRightDual X).symm.op.mop)
    (fun f ↦ MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj (leftDualIsoRightDual_inv_naturality f)))

end CategoryTheory

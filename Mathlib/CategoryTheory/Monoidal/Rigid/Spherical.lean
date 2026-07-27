/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Monoidal.Rigid.Trace

/-!
# Spherical monoidal categories

A pivotal category is spherical when its left and right traces agree.

The canonical pivotal structure on a rigid symmetric monoidal category is compatible with
the braiding in the sense of `PivotalCategory.IsBraidingCompatible`. Such a pivotal category
is spherical.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A pivotal structure is compatible with a braiding when its induced left pairing
is the pairing obtained by applying the braiding to the right pairing. -/
class PivotalCategory.IsBraidingCompatible
    [PivotalCategory C] [BraidedCategory C] : Prop where
  coevaluation_eq (X : C) :
    letI := pivotalExactPairing X
    η_ Xᘁ X = η_ X Xᘁ ≫ (β_ Xᘁ X).inv
  evaluation_eq (X : C) :
    letI := pivotalExactPairing X
    ε_ Xᘁ X = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

/-- A pivotal category is spherical when its left and right traces agree. -/
class SphericalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] : Prop where
  leftTrace_eq_rightTrace {X : C} (f : X ⟶ X) : leftTrace f = rightTrace f

/-- A symmetric pivotal category whose pivotal structure is compatible with the braiding
is spherical. -/
instance PivotalCategory.IsBraidingCompatible.toSphericalCategory
    [PivotalCategory C] [SymmetricCategory C]
    [PivotalCategory.IsBraidingCompatible (C := C)] : SphericalCategory C where
  leftTrace_eq_rightTrace {X} f := by
    rw [leftTrace, rightTrace,
      PivotalCategory.IsBraidingCompatible.coevaluation_eq,
      PivotalCategory.IsBraidingCompatible.evaluation_eq,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding Xᘁ X,
      Category.assoc, BraidedCategory.braiding_naturality_left_assoc]

/-- The common trace in a spherical category. -/
@[nolint unusedArguments]
def trace [PivotalCategory C] [SphericalCategory C]
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftTrace f

variable [PivotalCategory C] [SphericalCategory C]

lemma trace_eq_leftTrace {X : C} (f : X ⟶ X) : trace f = leftTrace f := rfl

lemma trace_eq_rightTrace {X : C} (f : X ⟶ X) : trace f = rightTrace f :=
  SphericalCategory.leftTrace_eq_rightTrace f

example [SymmetricCategory C]
    [PivotalCategory.IsBraidingCompatible (C := C)]
    {X : C} (f : X ⟶ X) :
    trace f =
      η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [trace_eq_rightTrace, rightTrace,
    PivotalCategory.IsBraidingCompatible.evaluation_eq]

end CategoryTheory

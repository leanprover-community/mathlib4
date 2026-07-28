/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Trace

/-!
# Spherical monoidal categories

A pivotal category is spherical when its left and right traces agree.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A pivotal category is spherical when its left and right traces agree. -/
class SphericalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] : Prop where
  leftTrace_eq_rightTrace {X : C} (f : X ⟶ X) : leftTrace f = rightTrace f

/-- The trace in a spherical category. -/
@[nolint unusedArguments]
def trace [PivotalCategory C] [SphericalCategory C]
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftTrace f

variable [PivotalCategory C] [SphericalCategory C]

lemma trace_eq_leftTrace {X : C} (f : X ⟶ X) : trace f = leftTrace f := rfl

lemma trace_eq_rightTrace {X : C} (f : X ⟶ X) : trace f = rightTrace f :=
  SphericalCategory.leftTrace_eq_rightTrace f

end CategoryTheory

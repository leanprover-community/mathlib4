/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Pivotal

/-!
# Traces in pivotal categories

The left and right traces of an endomorphism in a pivotal category.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [PivotalCategory C]

/-- The left trace of an endomorphism in a pivotal category. -/
def leftTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  letI := pivotalExactPairing X
  η_ Xᘁ X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ

/-- The right trace of an endomorphism in a pivotal category. -/
def rightTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  letI := pivotalExactPairing X
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ ε_ Xᘁ X

end CategoryTheory

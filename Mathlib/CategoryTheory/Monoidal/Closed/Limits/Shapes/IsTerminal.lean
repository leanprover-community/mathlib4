/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Terminal / initial objects in monoidal closed categories

Results about terminal / initial objects in monoidal closed categories.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonoidalClosed Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The isomorphism `(A ⟹ ⋆) ≅ ⋆` in a monoidal closed category with pullbacks and a terminal
object. -/
@[simps]
def terminalPow {A : C} [Closed A] {T : C} (t : IsTerminal T) :
    (ihom A).obj T ≅ T where
  hom := t.from _
  inv := curry (t.from _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff]
    apply t.hom_ext

end CategoryTheory

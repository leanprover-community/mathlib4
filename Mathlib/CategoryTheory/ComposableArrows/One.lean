/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Functors to `ComposableArrows C 1`

-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable (C : Type u) [Category.{v} C]

/-- The functor `ComposableArrows C n ⥤ ComposableArrows C 1`
which sends `S` to `mk₁ (S.map' i j)` when `i`, `j` and `n`
are such that `i ≤ j` and `j ≤ n`. -/
@[simps]
noncomputable def functorArrows (i j n : ℕ) (hij : i ≤ j := by lia) (hj : j ≤ n := by lia) :
    ComposableArrows C n ⥤ ComposableArrows C 1 where
  obj S := mk₁ (S.map' i j)
  map {S S'} φ := homMk₁ (φ.app _) (φ.app _) (φ.naturality _)

/-- The natural transformation `functorArrows C i j n ⟶ functorArrows C i' j' n`
when `i ≤ i'` and `j ≤ j'`. -/
@[simps]
noncomputable def mapFunctorArrows (i j i' j' n : ℕ)
    (_ : i ≤ j := by lia) (_ : i' ≤ j' := by lia)
    (_ : i ≤ i' := by lia) (_ : j ≤ j' := by lia)
    (_ : j' ≤ n := by lia) :
    functorArrows C i j n ⟶ functorArrows C i' j' n where
  app S := homMk₁ (S.map' i i') (S.map' j j')
    (by simp [← Functor.map_comp])

end ComposableArrows

end CategoryTheory

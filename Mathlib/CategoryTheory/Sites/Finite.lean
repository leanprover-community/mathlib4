/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.Data.Set.Finite.Lattice

/-! # The Finite Pretopology

In this file we define the finite pretopology on a category, which consists of presieves that
contain only finitely many arrows.

## Main Definitions

- `CategoryTheory.Pretopology.finite`: The finite pretopology on a category.
-/

universe v v₁ u u₁

namespace CategoryTheory

open Limits

namespace Pretopology

open Presieve

/-- The finite pretopology on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
def finite (C : Type u) [Category.{v} C] [HasPullbacks C] : Pretopology C where
  coverings X := { s : Presieve X | s.uncurry.Finite }
  has_isos X Y f _ := by simp
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ ↦ (ht _ _).image _

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

@[simp] lemma mem_finite_coverings {X : C} {s : Presieve X} :
    s ∈ (finite C).coverings X ↔ s.uncurry.Finite := Iff.rfl

theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    ofArrows Y f ∈ (finite C).coverings X := by
  simpa using Set.finite_range _

end Pretopology

end CategoryTheory

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

- `CategoryTheory.Precoverage.finite`: The finite precoverage on a category.
- `CategoryTheory.Pretopology.finite`: The finite pretopology on a category.
-/

universe v v₁ u u₁

namespace CategoryTheory

open Presieve

namespace Precoverage

/-- The finite precoverage on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
def finite (C : Type u) [Category.{v} C] : Precoverage C where
  coverings X := { s : Presieve X | s.uncurry.Finite }

variable {C : Type u} [Category.{v} C]

@[simp] lemma mem_finite_iff {X : C} {s : Presieve X} :
    s ∈ finite C X ↔ s.uncurry.Finite := Iff.rfl

theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    ofArrows Y f ∈ finite C X := by
  simpa using Set.finite_range _

instance : (finite C).HasIsos where
  mem_coverings_of_isIso := by simp

end Precoverage

namespace Pretopology

open Limits

/-- The finite pretopology on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
@[simps toPrecoverage]
def finite (C : Type u) [Category.{v} C] [HasPullbacks C] : Pretopology C where
  __ := Precoverage.finite C
  has_isos _ _ _ := Precoverage.mem_coverings_of_isIso _
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ ↦ (ht _ _).image _

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    ofArrows Y f ∈ (finite C).coverings X :=
  Precoverage.ofArrows_mem_finite _ _

end Pretopology

end CategoryTheory

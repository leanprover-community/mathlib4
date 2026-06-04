/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# Star-convex sets

This file defines star-convex sets in a convex space.

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.
-/

open Finsupp Set

public noncomputable section

namespace Convexity
variable {ι R X Y : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X → Y} {w : StdSimplex R X} {x : X} {s t : Set X} {y : X}

variable (R x s) in
/-- A set `s` is star-convex at a point `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
@[expose]
def IsStarConvexSet : Prop :=
  ∀ ⦃a b ha hb hab y⦄, y ∈ s → convexCombPair (R := R) a b ha hb hab x y ∈ s

@[simp] protected lemma IsStarConvexSet.empty : IsStarConvexSet R x ∅ := by simp [IsStarConvexSet]

@[simp]
protected lemma IsStarConvexSet.univ : IsStarConvexSet R x .univ := by simp [IsStarConvexSet]

@[simp] protected lemma IsStarConvexSet.singleton : IsStarConvexSet R x {x} := by
  simp [IsStarConvexSet]

protected lemma IsStarConvexSet.inter (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s ∩ t) := by simp +contextual [IsStarConvexSet, hs _, ht _]

protected lemma IsStarConvexSet.sInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋂₀ S) := by simp +contextual [IsStarConvexSet, hS _ _ _]

protected lemma IsStarConvexSet.iInter {ι : Sort*} {s : ι → Set X}
    (hs : ∀ i, IsStarConvexSet R x (s i)) : IsStarConvexSet R x (⋂ i, s i) := by
  simp +contextual [IsStarConvexSet, hs _ _]

lemma IsStarConvexSet.iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : ∀ i, κ i → Set X}
    (h : ∀ i j, IsStarConvexSet R x (s i j)) : IsStarConvexSet R x (⋂ (i) (j), s i j) :=
  .iInter fun i ↦ .iInter <| h i

protected lemma IsStarConvexSet.sUnion {S : Set (Set X)} (hS : ∀ s ∈ S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋃₀ S) := by rintro a ha b hb hab y ⟨s, hs, hy⟩; exact ⟨s, hs, hS _ hs hy⟩

protected lemma IsStarConvexSet.iUnion {ι : Sort*} {s : ι → Set X}
    (hs : ∀ i, IsStarConvexSet R x (s i)) : IsStarConvexSet R x (⋃ i, s i) := .sUnion <| by simpa

protected lemma IsStarConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f)
    (hs : IsStarConvexSet R (f x) s) : IsStarConvexSet R x (f ⁻¹' s) :=
  fun a b ha hb hab y hy ↦ by simpa [mem_preimage, hf.map_convexCombPair] using hs hy

protected lemma IsStarConvexSet.image (hf : IsAffineMap R f) (hs : IsStarConvexSet R x s) :
    IsStarConvexSet R (f x) (f '' s) := by
  rintro _ a b ha hb hab ⟨y, hy, rfl⟩; exact ⟨_, hs hy, hf.map_convexCombPair ..⟩

protected lemma IsStarConvexSet.prod {t : Set Y} {y : Y} (hs : IsStarConvexSet R x s)
    (ht : IsStarConvexSet R y t) : IsStarConvexSet R (x, y) (s ×ˢ t) := by
  rintro a b ha hb hab ⟨w, z⟩ ⟨hw, hz⟩; exact ⟨by simpa using hs hw, by simpa using ht hz⟩

protected lemma IsStarConvexSet.pi {X : ι → Type*} [∀ i, ConvexSpace R (X i)] {s : Set ι}
    {x : ∀ i, X i} {t : ∀ i, Set (X i)} (ht : ∀ i ∈ s, IsStarConvexSet R (x i) (t i)) :
    IsStarConvexSet R x (s.pi t) := fun a b ha hb hab y hy i hi ↦ by simpa using ht _ hi <| hy _ hi

end Semiring
end Convexity

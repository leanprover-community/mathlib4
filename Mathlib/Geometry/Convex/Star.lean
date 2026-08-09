/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Set

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

public section

namespace Convexity
variable {R X Y : Type*} {ι : Sort*} {κ : ι → Sort*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X → Y} {w : StdSimplex R X} {x : X} {s t : Set X} {y : X}

variable (R x s) in
/-- A set `s` is star-convex at a point `x` if every segment from `x` to a point in `s` is
contained in `s`.

TODO: Replace `StarConvex` with this predicate. -/
@[expose]
def IsStarConvexSet : Prop :=
  ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : R⦄ ha hb hab, convexCombPair a b ha hb hab x y ∈ s

@[simp] protected lemma IsStarConvexSet.empty : IsStarConvexSet R x ∅ := by simp [IsStarConvexSet]

@[simp]
protected lemma IsStarConvexSet.univ : IsStarConvexSet R x .univ := by simp [IsStarConvexSet]

@[simp] protected lemma IsStarConvexSet.singleton : IsStarConvexSet R x {x} := by
  simp [IsStarConvexSet]

@[grind ←]
protected lemma IsStarConvexSet.inter (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s ∩ t) := by simp +contextual [IsStarConvexSet, hs _, ht _]

@[grind ←]
protected lemma IsStarConvexSet.union (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s ∪ t) := by simp +contextual [IsStarConvexSet, hs _, ht _, or_imp]

@[grind ←]
protected lemma IsStarConvexSet.sInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋂₀ S) := by simp +contextual [IsStarConvexSet, hS _ _ _]

@[grind ←]
protected lemma IsStarConvexSet.iInter {s : ι → Set X} (hs : ∀ i, IsStarConvexSet R x (s i)) :
    IsStarConvexSet R x (⋂ i, s i) := by simp +contextual [IsStarConvexSet, hs _ _]

lemma IsStarConvexSet.iInter₂ {s : ∀ i, κ i → Set X} (h : ∀ i j, IsStarConvexSet R x (s i j)) :
    IsStarConvexSet R x (⋂ i, ⋂ j, s i j) := .iInter fun i ↦ .iInter <| h i

@[grind ←]
protected lemma IsStarConvexSet.sUnion {S : Set (Set X)} (hS : ∀ s ∈ S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋃₀ S) := by
  rintro y ⟨s, hs, hy⟩ a ha b hb hab; exact ⟨s, hs, hS _ hs hy _ ..⟩

@[grind ←]
protected lemma IsStarConvexSet.iUnion {s : ι → Set X} (hs : ∀ i, IsStarConvexSet R x (s i)) :
    IsStarConvexSet R x (⋃ i, s i) := .sUnion <| by simpa

protected lemma IsStarConvexSet.iUnion₂ {s : ∀ i, κ i → Set X}
    (h : ∀ i j, IsStarConvexSet R x (s i j)) : IsStarConvexSet R x (⋃ i, ⋃ j, s i j) :=
  .iUnion fun i ↦ .iUnion <| h i

lemma IsConvexSet.isStarConvexSet (hs : IsConvexSet R s) (hx : x ∈ s) : IsStarConvexSet R x s :=
  fun _y hy _a _b _ha _hb _hab ↦ hs.convexCombPair_mem hx hy ..

lemma IsStarConvexSet.mem (hs : IsStarConvexSet R x s) (hs₀ : s.Nonempty) : x ∈ s := by
  obtain ⟨y, hy⟩ := hs₀; simpa using hs hy zero_le_one le_rfl (add_zero _)

@[grind ←]
protected lemma IsStarConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f)
    (hs : IsStarConvexSet R (f x) s) : IsStarConvexSet R x (f ⁻¹' s) :=
  fun y hy a b ha hb hab ↦ by simpa [mem_preimage, hf.map_convexCombPair] using hs hy _ ..

@[grind <=]
protected lemma IsStarConvexSet.image (hf : IsAffineMap R f) (hs : IsStarConvexSet R x s) :
    IsStarConvexSet R (f x) (f '' s) := by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab; exact ⟨_, hs hy _ .., hf.map_convexCombPair ..⟩

@[grind ←]
protected lemma IsStarConvexSet.prod {t : Set Y} {y : Y} (hs : IsStarConvexSet R x s)
    (ht : IsStarConvexSet R y t) : IsStarConvexSet R (x, y) (s ×ˢ t) := by
  rintro ⟨w, z⟩ ⟨hw, hz⟩ a b ha hb hab; exact ⟨by simpa using hs hw _ .., by simpa using ht hz _ ..⟩

@[grind ←]
protected lemma IsStarConvexSet.pi {ι : Type*} {X : ι → Type*} [∀ i, ConvexSpace R (X i)]
    {s : Set ι} {x : ∀ i, X i} {t : ∀ i, Set (X i)} (ht : ∀ i ∈ s, IsStarConvexSet R (x i) (t i)) :
    IsStarConvexSet R x (s.pi t) :=
  fun y hy a b ha hb hab i hi ↦ by simpa using ht _ hi (hy _ hi) _ ..

end Semiring
end Convexity

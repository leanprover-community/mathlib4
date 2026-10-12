/-
Copyright (c) 2026 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICPNSP.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Data.Set.Insert

/-!
# Segments in convex spaces

In an R-convex space, we define the following objects:
* `segment R x y`: Closed segment joining `x` and `y`.
* `openSegment R x y`: Open segment joining `x` and `y`.

## TODO

Should we rename `segment` and `openSegment` to `Convexity.Icc` and `Convexity.Ioo`? Should we also
define `clopenSegment`/`Convexity.Ico`/`Convexity.Ioc`?
-/

namespace Convexity

open Convexity Function Set

section Semiring

variable (R) {X} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] {s : Set X}
  {x y z : X}

/-- Segments in a convex space. Denoted as `segment R x y` within the `Convex` namespace. -/
def segment (x y : X) : Set X :=
  { z : X | ∃ (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    convexCombPair a b ha hb hab x y = z }

/-- Open segment in a convex space. Note that `openSegment R x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : X) : Set X :=
  { z : X | ∃ (a b : R) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
    convexCombPair a b ha.le hb.le hab x y = z }

/- [x,y] = [y,x] -/
theorem segment_symm (x y : X) : segment R x y = segment R y x := by
  ext z
  constructor
  all_goals (intro h; rcases h with ⟨m, n, hm , hn , hmn , hz⟩; use n, m, hn, hm)
  all_goals (rw [convexCombPair_symm] at hz; rw [add_comm] at hmn; use hmn)

/- (x,y) = (y,x) -/
theorem openSegment_symm (x y : X) : openSegment R x y = openSegment R y x := by
  ext z
  constructor
  all_goals (intro h; rcases h with ⟨m, n, hm , hn , hmn , hz⟩; use n, m, hn, hm)
  all_goals (rw [convexCombPair_symm] at hz; rw [add_comm] at hmn; use hmn)

theorem openSegment_subset_segment (x y : X) : openSegment R x y ⊆ segment R x y :=
  fun _ ⟨a, b, ha, hb, hab, hz⟩ => ⟨a, b, ha.le, hb.le, hab, hz⟩

theorem segment_subset_iff :
    segment R x y ⊆ s ↔
    ∀ (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), convexCombPair a b ha hb hab x y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

theorem openSegment_subset_iff :
    openSegment R x y ⊆ s ↔
    ∀ (a b : R) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
      convexCombPair a b ha.le hb.le hab x y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩

theorem left_mem_segment (x y : X) : x ∈ segment R x y :=
  ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [convexCombPair_one]⟩

theorem right_mem_segment (x y : X) : y ∈ segment R x y :=
  segment_symm R y x ▸ left_mem_segment R y x

@[simp]
theorem segment_same (x : X) : segment R x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
      fun h => mem_singleton_iff.1 h ▸ left_mem_segment R z z⟩

theorem insert_endpoints_openSegment (x y : X) :
    insert x (insert y (openSegment R x y)) = segment R x y := by
  simp only [subset_antisymm_iff, insert_subset_iff, left_mem_segment, right_mem_segment,
    openSegment_subset_segment, true_and]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine hb.eq_or_lt.imp ?_ fun hb' => ha.eq_or_lt.imp ?_ fun ha' => ?_
  · rintro rfl
    simp [add_zero a ▸ hab]
  · rintro rfl
    simp [zero_add b ▸ hab]
  · exact ⟨a, b, ha', hb', hab, rfl⟩

variable {R}

theorem mem_openSegment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ segment R x y) :
    z ∈ openSegment R x y := by
  rw [← insert_endpoints_openSegment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

theorem openSegment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) :
    openSegment R x y ⊆ s ↔ segment R x y ⊆ s := by
  simp only [← insert_endpoints_openSegment, insert_subset_iff, *, true_and]

end Semiring

section DenselyOrderedRing

variable (R) {X} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [DenselyOrdered R]

@[simp]
theorem openSegment_same (x : X) : openSegment R x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [convexCombPair_same, mem_singleton_iff, eq_comm] using hz,
    fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : R) 1 zero_lt_one
      refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, ?_⟩
      rw [convexCombPair_same, h]⟩

end DenselyOrderedRing

end Convexity

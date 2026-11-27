/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Pi

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Diameters of sets in extended metric spaces

In this file we define the diameter of a set in the extended metric space
as an extended nonnegative real number.
-/

@[expose] public section

open Set

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

variable {α X : Type*} {s t : Set X} {x y z : X}

namespace Metric

section WeakPseudoEMetricSpace

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
noncomputable def ediam [EDist X] (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), eDist x y

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]

theorem ediam_eq_sSup (s : Set X) : ediam s = sSup (image2 eDist s s) := sSup_image2.symm

theorem ediam_le_iff {d : ℝ≥0∞} : ediam s ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, eDist x y ≤ d := by
  simp only [ediam, iSup_le_iff]

theorem ediam_image_le_iff {d : ℝ≥0∞} {f : α → X} {s : Set α} :
    ediam (f '' s) ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, eDist (f x) (f y) ≤ d := by
  simp only [ediam_le_iff, forall_mem_image]

theorem eDist_le_of_ediam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : ediam s ≤ d) : eDist x y ≤ d :=
  ediam_le_iff.1 hd x hx y hy

@[deprecated (since := "2026-11-27")] alias edist_le_of_ediam_le := eDist_le_of_ediam_le

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem eDist_le_ediam_of_mem (hx : x ∈ s) (hy : y ∈ s) : eDist x y ≤ ediam s :=
  eDist_le_of_ediam_le hx hy le_rfl

@[deprecated (since := "2026-11-27")] alias edist_le_ediam_of_mem := eDist_le_ediam_of_mem

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem ediam_le {d : ℝ≥0∞} (h : ∀ x ∈ s, ∀ y ∈ s, eDist x y ≤ d) : ediam s ≤ d :=
  ediam_le_iff.2 h

/-- The diameter of a subsingleton vanishes. -/
theorem ediam_subsingleton (hs : s.Subsingleton) : ediam s = 0 :=
  nonpos_iff_eq_zero.1 <| ediam_le fun _x hx y hy => (hs hx hy).symm ▸ eDist_self y ▸ le_rfl

alias _root_.Set.Subsingleton.ediam_eq := ediam_subsingleton

/-- The diameter of the empty set vanishes -/
@[simp]
theorem ediam_empty : ediam (∅ : Set X) = 0 :=
  ediam_subsingleton subsingleton_empty

/-- The extended diameter of a singleton vanishes -/
@[simp]
theorem ediam_singleton : ediam ({x} : Set X) = 0 :=
  ediam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]
theorem ediam_one [One X] : ediam (1 : Set X) = 0 :=
  ediam_singleton

theorem ediam_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set X) :
    ediam (⋃ i ∈ o, s i) = ⨆ i ∈ o, ediam (s i) := by cases o <;> simp

theorem ediam_insert : ediam (insert x s) = max (⨆ y ∈ s, eDist x y) (ediam s) :=
  eq_of_forall_ge_iff fun d => by simp +contextual [ediam_le_iff, eDist_comm]

theorem ediam_pair : ediam {x, y} = eDist x y := by simp [ediam_insert]

theorem ediam_triple : ediam {x, y, z} = max (max (eDist x y) (eDist x z)) (eDist y z) := by
  simp only [ediam_insert, iSup_insert, iSup_singleton, ediam_singleton, max_zero]

/-- The extended diameter is monotonous with respect to inclusion -/
@[gcongr]
theorem ediam_mono (h : s ⊆ t) : ediam s ≤ ediam t :=
  ediam_le fun _x hx _y hy => eDist_le_ediam_of_mem (h hx) (h hy)

/-- The extended diameter of a union is controlled by the diameter of the sets,
and the edistance between two points in the sets. -/
theorem ediam_union_le_add_eDist (xs : x ∈ s) (yt : y ∈ t) :
    ediam (s ∪ t) ≤ ediam s + eDist x y + ediam t := by
  have A : ∀ a ∈ s, ∀ b ∈ t, eDist a b ≤ ediam s + eDist x y + ediam t := fun a ha b hb =>
    calc
      eDist a b ≤ eDist a x + eDist x y + eDist y b := eDist_triangle4 _ _ _ _
      _ ≤ ediam s + eDist x y + ediam t := by
        gcongr
        exacts [eDist_le_ediam_of_mem ha xs, eDist_le_ediam_of_mem yt hb]
  refine ediam_le fun a ha b hb => ?_
  rw [mem_union] at ha hb
  rcases ha with h'a | h'a <;> rcases hb with h'b | h'b
  · calc
      eDist a b ≤ ediam s := eDist_le_ediam_of_mem h'a h'b
      _ ≤ ediam s + (eDist x y + ediam t) := le_self_add
      _ = ediam s + eDist x y + ediam t := (add_assoc _ _ _).symm
  · exact A a h'a b h'b
  · have Z := A b h'b a h'a
    rwa [eDist_comm] at Z
  · calc
      eDist a b ≤ ediam t := eDist_le_ediam_of_mem h'a h'b
      _ ≤ ediam s + eDist x y + ediam t := le_add_self

@[deprecated (since := "2026-11-27")] alias ediam_union_le_add_edist := ediam_union_le_add_eDist

/-- If two sets have nonempty intersection, then the extended diameter of their union
is estimated from above by the sum of their union. -/
theorem ediam_union_le (h : (s ∩ t).Nonempty) : ediam (s ∪ t) ≤ ediam s + ediam t := by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using ediam_union_le_add_eDist xs xt

theorem ediam_closedEBall_le {r : ℝ≥0∞} : ediam (closedEBall x r) ≤ 2 * r :=
  ediam_le fun a ha b hb =>
    calc
      eDist a b ≤ eDist a x + eDist b x := eDist_triangle_right _ _ _
      _ ≤ r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm

theorem ediam_eball_le {r : ℝ≥0∞} : ediam (eball x r) ≤ 2 * r :=
  le_trans (ediam_mono eball_subset_closedEBall) ediam_closedEBall_le

theorem ediam_pi_le_of_le {ι : Type*} {X : ι → Type*} [Fintype ι] [∀ i, PseudoEMetricSpace (X i)]
    {s : ∀ i : ι, Set (X i)} {c : ℝ≥0∞} (h : ∀ b, ediam (s b) ≤ c) : ediam (Set.pi univ s) ≤ c := by
  refine ediam_le fun x hx y hy => eDist_pi_le_iff.mpr ?_
  rw [mem_univ_pi] at hx hy
  exact fun b => ediam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

end WeakPseudoEMetricSpace

section WeakEMetricSpace

variable [TopologicalSpace X] [WeakEMetricSpace X]

theorem ediam_eq_zero_iff : ediam s = 0 ↔ s.Subsingleton :=
  ⟨fun h _x hx _y hy => eDist_le_zero.1 <| h ▸ eDist_le_ediam_of_mem hx hy, ediam_subsingleton⟩

theorem ediam_pos_iff : 0 < ediam s ↔ s.Nontrivial := by
  simp only [pos_iff_ne_zero, Ne, ediam_eq_zero_iff, Set.not_subsingleton_iff]

theorem ediam_pos_iff' : 0 < ediam s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  simp only [ediam_pos_iff, Set.Nontrivial]

end WeakEMetricSpace

end Metric

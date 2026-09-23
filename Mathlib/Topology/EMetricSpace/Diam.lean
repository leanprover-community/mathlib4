/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Pi

/-!
# Diameters of sets in extended metric spaces

In this file we define the diameter of a set in the extended metric space
as an extended nonnegative real number.
-/

@[expose] public section

open Set Filter

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

variable {α X : Type*} {s t : Set X} {x y z : X}

namespace Metric

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
noncomputable def ediam (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

theorem ediam_eq_sSup (s : Set X) : ediam s = sSup (image2 edist s s) := sSup_image2.symm

theorem ediam_le_iff {d : ℝ≥0∞} : ediam s ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d := by
  simp only [ediam, iSup_le_iff]

theorem ediam_image_le_iff {d : ℝ≥0∞} {f : α → X} {s : Set α} :
    ediam (f '' s) ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ d := by
  simp only [ediam_le_iff, forall_mem_image]

theorem edist_le_of_ediam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : ediam s ≤ d) : edist x y ≤ d :=
  ediam_le_iff.1 hd x hx y hy

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem edist_le_ediam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ ediam s :=
  edist_le_of_ediam_le hx hy le_rfl

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem ediam_le {d : ℝ≥0∞} (h : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d) : ediam s ≤ d :=
  ediam_le_iff.2 h

/-- The diameter of a subsingleton vanishes. -/
theorem ediam_subsingleton (hs : s.Subsingleton) : ediam s = 0 :=
  nonpos_iff_eq_zero.1 <| ediam_le fun _x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

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

theorem ediam_insert : ediam (insert x s) = max (⨆ y ∈ s, edist x y) (ediam s) :=
  eq_of_forall_ge_iff fun d => by simp +contextual [ediam_le_iff, edist_comm]

theorem ediam_pair : ediam ({x, y} : Set X) = edist x y := by simp [ediam_insert]

theorem ediam_triple :
    ediam ({x, y, z} : Set X) = max (max (edist x y) (edist x z)) (edist y z) := by
  simp only [ediam_insert, iSup_insert, iSup_singleton, ediam_singleton, ENNReal.max_zero_right]

/-- The extended diameter is monotonous with respect to inclusion -/
@[gcongr]
theorem ediam_mono (h : s ⊆ t) : ediam s ≤ ediam t :=
  ediam_le fun _x hx _y hy => edist_le_ediam_of_mem (h hx) (h hy)

/-- The extended diameter of a union is controlled by the diameter of the sets,
and the edistance between two points in the sets. -/
theorem ediam_union_le_add_edist (xs : x ∈ s) (yt : y ∈ t) :
    ediam (s ∪ t) ≤ ediam s + edist x y + ediam t := by
  have A : ∀ a ∈ s, ∀ b ∈ t, edist a b ≤ ediam s + edist x y + ediam t := fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ ≤ ediam s + edist x y + ediam t := by
        gcongr
        exacts [edist_le_ediam_of_mem ha xs, edist_le_ediam_of_mem yt hb]
  refine ediam_le fun a ha b hb => ?_
  rw [mem_union] at ha hb
  rcases ha with h'a | h'a <;> rcases hb with h'b | h'b
  · calc
      edist a b ≤ ediam s := edist_le_ediam_of_mem h'a h'b
      _ ≤ ediam s + (edist x y + ediam t) := le_self_add
      _ = ediam s + edist x y + ediam t := (add_assoc _ _ _).symm
  · exact A a h'a b h'b
  · have Z := A b h'b a h'a
    rwa [edist_comm] at Z
  · calc
      edist a b ≤ ediam t := edist_le_ediam_of_mem h'a h'b
      _ ≤ ediam s + edist x y + ediam t := le_add_self

/-- If two sets have nonempty intersection, then the extended diameter of their union
is estimated from above by the sum of their union. -/
theorem ediam_union_le (h : (s ∩ t).Nonempty) : ediam (s ∪ t) ≤ ediam s + ediam t := by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using ediam_union_le_add_edist xs xt

theorem ediam_closedEBall_le {r : ℝ≥0∞} : ediam (closedEBall x r) ≤ 2 * r :=
  ediam_le fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist b x := edist_triangle_right _ _ _
      _ ≤ r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm

theorem ediam_eball_le {r : ℝ≥0∞} : ediam (eball x r) ≤ 2 * r :=
  le_trans (ediam_mono eball_subset_closedEBall) ediam_closedEBall_le

theorem ediam_pi_le_of_le {ι : Type*} {X : ι → Type*} [Fintype ι] [∀ i, PseudoEMetricSpace (X i)]
    {s : ∀ i : ι, Set (X i)} {c : ℝ≥0∞} (h : ∀ b, ediam (s b) ≤ c) : ediam (Set.pi univ s) ≤ c := by
  refine ediam_le fun x hx y hy => edist_pi_le_iff.mpr ?_
  rw [mem_univ_pi] at hx hy
  exact fun b => ediam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace X]

theorem ediam_eq_zero_iff : ediam s = 0 ↔ s.Subsingleton :=
  ⟨fun h _x hx _y hy => edist_le_zero.1 <| h ▸ edist_le_ediam_of_mem hx hy, ediam_subsingleton⟩

theorem ediam_pos_iff : 0 < ediam s ↔ s.Nontrivial := by
  simp only [pos_iff_ne_zero, Ne, ediam_eq_zero_iff, Set.not_subsingleton_iff]

theorem ediam_pos_iff' : 0 < ediam s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  simp only [ediam_pos_iff, Set.Nontrivial]

end EMetricSpace

end Metric

namespace EMetric

open Metric

@[deprecated (since := "2026-01-04")] alias diam := Metric.ediam
@[deprecated (since := "2026-01-04")] alias diam_eq_sSup := ediam_eq_sSup
@[deprecated (since := "2026-01-04")] alias diam_le_iff := ediam_le_iff
@[deprecated (since := "2026-01-04")] alias diam_image_le_iff := ediam_image_le_iff
@[deprecated (since := "2026-01-04")] alias edist_le_of_diam_le := edist_le_of_ediam_le
@[deprecated (since := "2026-01-04")] alias edist_le_diam_of_mem := edist_le_ediam_of_mem
@[deprecated (since := "2026-01-04")] alias diam_le := ediam_le
@[deprecated (since := "2026-01-04")] alias diam_subsingleton := ediam_subsingleton
@[deprecated (since := "2026-01-04")] alias diam_empty := ediam_empty
@[deprecated (since := "2026-01-04")] alias diam_singleton := ediam_singleton
@[deprecated (since := "2026-01-04")] alias diam_zero := ediam_zero
@[to_additive existing, deprecated (since := "2026-01-04")] alias diam_one := ediam_one
@[deprecated (since := "2026-01-04")] alias diam_iUnion_mem_option := ediam_iUnion_mem_option
@[deprecated (since := "2026-01-04")] alias diam_insert := ediam_insert
@[deprecated (since := "2026-01-04")] alias diam_pair := ediam_pair
@[deprecated (since := "2026-01-04")] alias diam_triple := ediam_triple
@[deprecated (since := "2026-01-04")] alias diam_mono := ediam_mono
@[deprecated (since := "2026-01-04")] alias diam_union := ediam_union_le_add_edist
@[deprecated (since := "2026-01-04")] alias diam_union' := ediam_union_le
@[deprecated (since := "2026-01-04")] alias diam_closedBall := ediam_closedEBall_le
@[deprecated (since := "2026-01-04")] alias diam_ball := ediam_eball_le
@[deprecated (since := "2026-01-04")] alias diam_pi_le_of_le := ediam_pi_le_of_le
@[deprecated (since := "2026-01-04")] alias diam_eq_zero_iff := ediam_eq_zero_iff
@[deprecated (since := "2026-01-04")] alias diam_pos_iff := ediam_pos_iff
@[deprecated (since := "2026-01-04")] alias diam_pos_iff' := ediam_pos_iff'

end EMetric

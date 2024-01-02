/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Connectedness of subsets of vector spaces

We show several results related to the (path)-connectedness of subsets of real vector spaces:
* `Set.Countable.isPathConnected_compl_of_one_lt_rank` asserts that the complement of a countable
  set is path-connected in a space of dimension `> 1`.
* `isPathConnected_compl_singleton_of_one_lt_rank` is the special case of the complement of a
  singleton.
* `isPathConnected_sphere` shows that any sphere is path-connected in dimension `> 1`.

Statements with connectedness instead of path-connectedness are also given.
-/

open Convex Set Metric

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
[TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- In a real vector space of dimension `> 1`, the complement of any countable set is path
connected. -/
theorem Set.Countable.isPathConnected_compl_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {s : Set E} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := (hs.dense_compl ℝ).nonempty
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl|hab
  · exact JoinedIn.refl ha
  /- Assume `b ≠ a`. Write `a = c - x` and `b = c + x` for some nonzero `x`. Choose `y` which
  is linearly independent from `x`. Then the segments joining `a = c - x` to `c + ty` are pairwise
  disjoint for varying `t` (except for the endpoint `a`) so only countably many of them can
  intersect `s`. In the same way, there are countably many `t`s for which the segment
  from `b = c + x` to `c + ty` intersects `s`. Choosing `t` outside of these countable exceptions,
  one gets a path in the complement of `s` from `a` to `z = c + ty` and then to `b`.
  -/
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [smul_add, smul_sub]
    abel_nf
    simp [zsmul_eq_smul_cast ℝ 2]
  have Ib : c + x = b := by
    simp only [smul_add, smul_sub]
    abel_nf
    simp [zsmul_eq_smul_cast ℝ 2]
  have x_ne_zero : x ≠ 0 := by simpa using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right _ _) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right _ _) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  obtain ⟨t, ht⟩ : Set.Nonempty ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty}
      ∪ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty})ᶜ := ((A.union B).dense_compl ℝ).nonempty
  let z := c + t • y
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_nonempty_iff_eq_empty]
    at ht
  have JA : JoinedIn sᶜ a z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert ht.2
    exact Ia.symm
  have JB : JoinedIn sᶜ b z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert ht.1
    exact Ib.symm
  exact JA.trans JB.symm

/-- In a real vector space of dimension `> 1`, the complement of any countable set is
connected. -/
theorem Set.Countable.isConnected_compl_of_one_lt_rank (h : 1 < Module.rank ℝ E) {s : Set E}
    (hs : s.Countable) : IsConnected sᶜ :=
  (hs.isPathConnected_compl_of_one_lt_rank h).isConnected

/-- In a real vector space of dimension `> 1`, the complement of a singleton is path
connected. -/
theorem isPathConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (x : E) :
    IsPathConnected {x}ᶜ :=
  Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

/-- In a real vector space of dimension `> 1`, the complement of a singleton is
connected. -/
theorem isConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (x : E) :
    IsConnected {x}ᶜ :=
  (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

end TopologicalVectorSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real vector space of dimension `> 1`, any sphere of nonnegative radius is
path connected. -/
theorem isPathConnected_sphere (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (sphere x r) := by
  /- when `r > 0`, we write the sphere as the image of `{0}ᶜ` under the map
  `y ↦ x + (r * ‖y‖⁻¹) • y`. Since the image under a continuous map of a path connected set
  is path connected, this concludes the proof. -/
  rcases hr.eq_or_lt with rfl|rpos
  · simpa using isPathConnected_singleton x
  let f : E → E := fun y ↦ x + (r * ‖y‖⁻¹) • y
  have A : ContinuousOn f {0}ᶜ := by
    intro y hy
    apply (continuousAt_const.add _).continuousWithinAt
    apply (continuousAt_const.mul (ContinuousAt.inv₀ continuousAt_id.norm ?_)).smul continuousAt_id
    simpa using hy
  have B : IsPathConnected ({0}ᶜ : Set E) := isPathConnected_compl_singleton_of_one_lt_rank h 0
  have C : IsPathConnected (f '' {0}ᶜ) := B.image' A
  have : f '' {0}ᶜ = sphere x r := by
    apply Subset.antisymm
    · rintro - ⟨y, hy, rfl⟩
      have : ‖y‖ ≠ 0 := by simpa using hy
      simp [norm_smul, abs_of_nonneg hr, mul_assoc, inv_mul_cancel this]
    · intro y hy
      refine ⟨y - x, ?_, ?_⟩
      · intro H
        simp only [mem_singleton_iff, sub_eq_zero] at H
        simp only [H, mem_sphere_iff_norm, sub_self, norm_zero] at hy
        exact rpos.ne hy
      · simp [mem_sphere_iff_norm.1 hy, mul_inv_cancel rpos.ne']
  rwa [this] at C

/-- In a real vector space of dimension `> 1`, any sphere of nonnegative radius is connected. -/
theorem isConnected_sphere (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (sphere x r) :=
  (isPathConnected_sphere h x hr).isConnected

/-- In a real vector space of dimension `> 1`, any sphere is preconnected. -/
theorem isPreconnected_sphere (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (sphere x r) := by
  rcases le_or_lt 0 r with hr|hr
  · exact (isConnected_sphere h x hr).isPreconnected
  · simpa [hr] using isPreconnected_empty

end NormedSpace

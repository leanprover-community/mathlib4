/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Analysis.Convolution
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.CountableCover
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# this is a test file

But the header is still correctly formatted to appease the linter
-/

set_option autoImplicit false

open LinearMap Set

open BigOperators Classical Convex Pointwise Filter

universe u v

open Filter Set

open scoped Cardinal Topology


lemma segment_inter_eq_endpoint_of_linearIndependent
    {E : Type _} [AddCommGroup E] [Module ℝ E] {x y : E} (h : LinearIndependent ℝ ![x, y])
    {s t : ℝ} (hs : s ≠ t) (c : E) :
    [c + x -[ℝ] c + t • y] ∩ [c + x -[ℝ] c + s • y] ⊆ {c + x} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have H' : (1 - q) • x + (q * s) • y = (1 - p) • x + (p * t) • y := by
    rw [← sub_eq_zero] at H ⊢
    rw [← H]
    simp only [smul_smul, smul_add, sub_smul]
    abel
  obtain rfl : q = p := by simpa using (h.eq_of_pair H').1
  rcases q0.eq_or_gt with rfl|hq0'
  · simp
  · have A : s = t := by simpa [mul_eq_mul_left_iff, hq0'.ne'] using (h.eq_of_pair H').2
    exact (hs A).elim

theorem JoinedIn_of_segment_subset {E : Type _} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {x y : E} {s : Set E} (h : [x -[ℝ] y] ⊆ s) : JoinedIn s x y := by
  have A : Continuous (fun t ↦ (1 - t) • x + t • y : ℝ → E) := by continuity
  apply JoinedIn.ofLine A.continuousOn (by simp) (by simp)
  convert h
  rw [segment_eq_image ℝ x y]

open Function

theorem countable_nonempty_setOf_of_disjoint {α : Type u} {ι : Type v} {f : ι → Set α}
    (hf : Pairwise (Disjoint on f)) {s : Set α} (h'f : ∀ t, f t ⊆ s) (hs : s.Countable) :
    Set.Countable {t | (f t).Nonempty} := by
  rw [← Set.countable_coe_iff] at hs ⊢
  have : ∀ t : {t // (f t).Nonempty}, ∃ x : s, x.1 ∈ f t := by
    rintro ⟨t, ⟨x, hx⟩⟩
    exact ⟨⟨x, (h'f t hx)⟩, hx⟩
  choose F hF using this
  have A : Injective F := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
    have A : (f t ∩ f t').Nonempty := by
      refine ⟨F ⟨t, ht⟩, hF _, ?_⟩
      rw [htt']
      exact hF _
    simp only [Subtype.mk.injEq]
    by_contra H
    exact not_disjoint_iff_nonempty_inter.2 A (hf H)
  exact Injective.countable A

section

variable {E : Type _} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]



/-- In a real vector space of dimension `> 1`, the complement of any countable set is path
connected. -/
theorem Set.Countable.isPathConnected_compl_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {s : Set E} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := hs.dense_compl.nonempty
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
    exists_linear_independent_pair_of_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_nonempty_setOf_of_disjoint _ (fun t ↦ inter_subset_right _ _) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply segment_inter_eq_endpoint_of_linearIndependent hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_nonempty_setOf_of_disjoint _ (fun t ↦ inter_subset_right _ _) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply segment_inter_eq_endpoint_of_linearIndependent _ htt'.symm
    convert hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  obtain ⟨t, ht⟩ : Set.Nonempty ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty}
                       ∪ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty})ᶜ :=
    (A.union B).dense_compl.nonempty
  let z := c + t • y
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_nonempty_iff_eq_empty]
    at ht
  have JA : JoinedIn sᶜ a z := by
    apply JoinedIn_of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert ht.2
    exact Ia.symm
  have JB : JoinedIn sᶜ b z := by
    apply JoinedIn_of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert ht.1
    exact Ib.symm
  exact JA.trans JB.symm

/-- In a real vector space of dimension `> 1`, the complement of any countable set is
connected. -/
theorem Set.Countable.isConnected_compl_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {s : Set E} (hs : s.Countable) :
    IsConnected sᶜ :=
  (hs.isPathConnected_compl_of_one_lt_rank h).isConnected

/-- In a real vector space of finite dimension `> 1`, the complement of any countable set is path
connected. -/
theorem Set.Countable.isPathConnected_compl_of_one_lt_finrank
    (h : 1 < FiniteDimensional.finrank ℝ E) {s : Set E} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  apply hs.isPathConnected_compl_of_one_lt_rank
  simpa using FiniteDimensional.rank_lt_of_finrank_lt h

/-- In a real vector space of finite dimension `> 1`, the complement of any countable set is
connected. -/
theorem Set.Countable.isConnected_compl_of_one_lt_finrank
    (h : 1 < FiniteDimensional.finrank ℝ E) {s : Set E} (hs : s.Countable) :
    IsConnected sᶜ :=
  (hs.isPathConnected_compl_of_one_lt_finrank h).isConnected

/-- In a real vector space of dimension `> 1`, the complement of a singleton is path
connected. -/
theorem isPathConnected_compl_singleton_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) (x : E) :
    IsPathConnected {x}ᶜ :=
  Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

/-- In a real vector space of dimension `> 1`, the complement of a singleton is
connected. -/
theorem isConnected_compl_singleton_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) (x : E) :
    IsConnected {x}ᶜ :=
  (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

/-- In a real vector space of finite dimension `> 1`, the complement of any countable set is path
connected. -/
theorem isPathConnected_compl_singleton_of_one_lt_finrank
    (h : 1 < FiniteDimensional.finrank ℝ E) (x : E) :
    IsPathConnected {x}ᶜ :=
  Set.Countable.isPathConnected_compl_of_one_lt_finrank h (countable_singleton x)

/-- In a real vector space of finite dimension `> 1`, the complement of any countable set is
connected. -/
theorem isConnected_compl_singleton_of_one_lt_finrank
    (h : 1 < FiniteDimensional.finrank ℝ E) (x : E) :
    IsConnected {x}ᶜ :=
  (isPathConnected_compl_singleton_of_one_lt_finrank h x).isConnected

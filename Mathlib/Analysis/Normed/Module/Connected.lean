/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Connectedness of subsets of vector spaces

We show several results related to the (path)-connectedness of subsets of real vector spaces:
* `Set.Countable.isPathConnected_compl_of_one_lt_rank` asserts that the complement of a countable
  set is path-connected in a space of dimension `> 1`.
* `isPathConnected_compl_singleton_of_one_lt_rank` is the special case of the complement of a
  singleton.
* `isPathConnected_sphere` shows that any sphere is path-connected in dimension `> 1`.
* `isPathConnected_compl_of_one_lt_codim` shows that the complement of a subspace
  of codimension `> 1` is path-connected.

Statements with connectedness instead of path-connectedness are also given.

* `ContinuousLinearMap.connectedComponents_compl_hyperplane_equiv_bool` shows that the complement
  of a convex hyperplane defined by a surjective continuous linear functional `F →L[ℝ] ℝ` has
  exactly two connected components (`ConnectedComponents _ ≃ Bool`); a version assuming `f ≠ 0` and
  cardinality (`Nat.card _ = 2`) are also proved.
* `ContinuousLinearMap.zerothHomotopy_compl_hyperplane_equiv_bool` is the corresponding
  path-component statement (`ZerothHomotopy _ ≃ Bool`).
-/

public section

assert_not_exists Subgroup.index Nat.divisors
-- TODO assert_not_exists Cardinal

open Set Function Metric Topology
open scoped Convex ENNReal

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
  rcases eq_or_ne a b with rfl | hab
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
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
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

/-- In a real vector space of dimension `> 1`, the complement of any singleton is path-connected. -/
theorem isPathConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (x : E) :
    IsPathConnected {x}ᶜ :=
  Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

/-- In a real vector space of dimension `> 1`, the complement of a singleton is connected. -/
theorem isConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (x : E) :
    IsConnected {x}ᶜ :=
  (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

end TopologicalVectorSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Ball

namespace Metric

theorem contractibleSpace_ball {x : E} {r : ℝ} (hr : 0 < r) :
    ContractibleSpace (ball x r) :=
  (convex_ball _ _).contractibleSpace (by simpa)

@[deprecated (since := "2026-02-02")]
alias ball_contractible := contractibleSpace_ball

theorem contractibleSpace_eball {x : E} {r : ℝ≥0∞} (hr : 0 < r) :
    ContractibleSpace (eball x r) :=
  (convex_eball _ _).contractibleSpace ⟨x, by simpa⟩

@[deprecated (since := "2026-02-02")]
alias eball_contractible := contractibleSpace_eball

theorem contractibleSpace_closedBall {x : E} {r : ℝ} (hr : 0 ≤ r) :
    ContractibleSpace (closedBall x r) :=
  (convex_closedBall _ _).contractibleSpace (by simpa)

instance contractibleSpace_closedEBall {x : E} {r : ℝ≥0∞} :
    ContractibleSpace (closedEBall x r) :=
  (convex_closedEBall _ _).contractibleSpace ⟨x, by simp⟩

theorem isPathConnected_ball {x : E} {r : ℝ} (hr : 0 < r) :
    IsPathConnected (ball x r) :=
  convex_ball _ _ |>.isPathConnected <| by simpa

theorem isPathConnected_eball {x : E} {r : ℝ≥0∞} (hr : 0 < r) :
    IsPathConnected (eball x r) :=
  convex_eball _ _ |>.isPathConnected ⟨x, by simpa⟩

theorem isPathConnected_closedBall {x : E} {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (closedBall x r) :=
  convex_closedBall _ _ |>.isPathConnected ⟨x, by simpa⟩

theorem isPathConnected_closedEBall {x : E} {r : ℝ≥0∞} :
    IsPathConnected (closedEBall x r) :=
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem isPreconnected_ball {x : E} {r : ℝ} : IsPreconnected (ball x r) :=
  (convex_ball _ _).isPreconnected

theorem isPreconnected_eball {x : E} {r : ℝ≥0∞} : IsPreconnected (eball x r) :=
  (convex_eball _ _).isPreconnected

theorem isPreconnected_closedBall {x : E} {r : ℝ} : IsPreconnected (closedBall x r) :=
  (convex_closedBall _ _).isPreconnected

theorem isPreconnected_closedEBall {x : E} {r : ℝ≥0∞} : IsPreconnected (closedEBall x r) :=
  (convex_closedEBall _ _).isPreconnected

theorem isConnected_ball {x : E} {r : ℝ} (hr : 0 < r) :
    IsConnected (ball x r) :=
  (isPathConnected_ball hr).isConnected

theorem isConnected_eball {x : E} {r : ℝ≥0∞} (hr : 0 < r) :
    IsConnected (eball x r) :=
  (isPathConnected_eball hr).isConnected

theorem isConnected_closedBall {x : E} {r : ℝ} (hr : 0 ≤ r) : IsConnected (closedBall x r) :=
  ⟨⟨x, by simpa⟩, isPreconnected_closedBall⟩

theorem isConnected_closedEBall {x : E} {r : ℝ≥0∞} : IsConnected (closedEBall x r) :=
  ⟨⟨x, mem_closedEBall_self⟩, isPreconnected_closedEBall⟩

end Metric

end Ball

/-- In a real vector space of dimension `> 1`, any sphere of nonnegative radius is
path connected. -/
theorem isPathConnected_sphere (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (sphere x r) := by
  /- when `r > 0`, we write the sphere as the image of `{0}ᶜ` under the map
  `y ↦ x + (r * ‖y‖⁻¹) • y`. Since the image under a continuous map of a path connected set
  is path connected, this concludes the proof. -/
  rcases hr.eq_or_lt with rfl | rpos
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
      simp [f, norm_smul, abs_of_nonneg hr, mul_assoc, inv_mul_cancel₀ this]
    · intro y hy
      refine ⟨y - x, ?_, ?_⟩
      · intro H
        simp only [mem_singleton_iff, sub_eq_zero] at H
        simp only [H, mem_sphere_iff_norm, sub_self, norm_zero] at hy
        exact rpos.ne hy
      · simp [f, mem_sphere_iff_norm.1 hy, mul_inv_cancel₀ rpos.ne']
  rwa [this] at C

/-- In a real vector space of dimension `> 1`, any sphere of nonnegative radius is connected. -/
theorem isConnected_sphere (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (sphere x r) :=
  (isPathConnected_sphere h x hr).isConnected

/-- In a real vector space of dimension `> 1`, any sphere is preconnected. -/
theorem isPreconnected_sphere (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (sphere x r) := by
  rcases le_or_gt 0 r with hr | hr
  · exact (isConnected_sphere h x hr).isPreconnected
  · simpa [hr] using isPreconnected_empty

end NormedSpace

section CodimensionOne

namespace ContinuousLinearMap

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] (f : F →L[ℝ] ℝ) (c : ℝ)

private def boolConnectedComponents : Bool → Set ↥({x : F | f x = c}ᶜ)
| true => {x | c < f x.val}
| false => {x | f x.val < c}

private lemma boolConnectedComponents_compl (i : Bool) :
    (boolConnectedComponents f c i)ᶜ = boolConnectedComponents f c !i := by
  ext x
  simp only [boolConnectedComponents, mem_compl_iff]
  grind

private lemma boolConnectedComponents_clopen (i : Bool) :
    IsClopen (boolConnectedComponents f c i) := by
  have hopen : ∀ i, IsOpen (boolConnectedComponents f c i) := by
    intro i
    fin_cases i
    · exact isOpen_Ioi.preimage (f.continuous.comp continuous_subtype_val)
    · exact isOpen_Iio.preimage (f.continuous.comp continuous_subtype_val)
  have := (hopen !i).isClosed_compl
  rw [boolConnectedComponents_compl, Bool.not_not] at this
  exact ⟨this, hopen i⟩

private lemma boolConnectedComponents_disjoint :
    Pairwise (Disjoint on f.boolConnectedComponents c) := by
  intro i j _
  fin_cases i <;> fin_cases j <;> (try contradiction) <;> simp +contextual [
    disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, boolConnectedComponents, le_of_lt]

private lemma boolConnectedComponents_iUnion : ⋃ i, f.boolConnectedComponents c i = univ := by
  ext x
  grind [boolConnectedComponents, mem_iUnion, Bool.exists_bool]

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {f}

private lemma boolConnectedComponents_pathConnected (hf : Surjective f) (i : Bool) :
    IsPathConnected (f.boolConnectedComponents c i) := by
  fin_cases i
  · haveI : PathConnectedSpace {x : F | c < f x} := isPathConnected_iff_pathConnectedSpace.mp <| by
      obtain ⟨x, hx⟩ := hf (c + 1)
      exact (convex_halfSpace_gt f.isLinear c).isPathConnected ⟨x, by simp [hx]⟩
    have hAs : {x : F | c < f x} ⊆ {x : F | f x = c}ᶜ := fun x hx => ne_of_gt hx
    have hU0 : boolConnectedComponents f c true = Set.range (Set.inclusion hAs) := by
      ext x
      grind [Subtype.exists, boolConnectedComponents]
    exact hU0 ▸ isPathConnected_range (continuous_inclusion hAs)
  · haveI : PathConnectedSpace {x : F | f x < c} := isPathConnected_iff_pathConnectedSpace.mp <| by
      obtain ⟨x, hx⟩ := hf (c - 1)
      exact (convex_halfSpace_lt f.isLinear c).isPathConnected ⟨x, by simp [hx]⟩
    have hBs : {x : F | f x < c} ⊆ {x : F | f x = c}ᶜ := fun x hx => ne_of_lt hx
    have hU1 : boolConnectedComponents f c false = Set.range (Set.inclusion hBs) := by
      ext x
      grind [Subtype.exists, boolConnectedComponents]
    exact hU1 ▸ isPathConnected_range (continuous_inclusion hBs)

theorem connectedComponents_compl_hyperplane_card_eq_two (hf : Surjective f) :
    Nat.card (ConnectedComponents ↥({x : F | f x = c}ᶜ)) = 2 :=
  (Nat.card_congr (ConnectedComponents.equivOfIsClopenOfIsConnected
    (boolConnectedComponents_clopen f c) (boolConnectedComponents_disjoint f c)
    (boolConnectedComponents_iUnion f c)
    fun i ↦ (boolConnectedComponents_pathConnected c hf i).isConnected)).trans <| by simp

theorem zerothHomotopy_compl_hyperplane_card_eq_two (hf : Surjective f) :
    Nat.card (ZerothHomotopy ↥({x : F | f x = c}ᶜ)) = 2 :=
  (Nat.card_congr (ZerothHomotopy.equivOfIsClopenOfIsPathConnected
    (boolConnectedComponents_clopen f c) (boolConnectedComponents_disjoint f c)
    (boolConnectedComponents_iUnion f c) (boolConnectedComponents_pathConnected c hf))).trans
    <| by simp

end ContinuousLinearMap
end CodimensionOne

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is path-connected. -/
theorem isPathConnected_compl_of_one_lt_codim {E : Submodule ℝ F}
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) : IsPathConnected (Eᶜ : Set F) := by
  rcases E.exists_isCompl with ⟨E', hE'⟩
  refine isPathConnected_compl_of_isPathConnected_compl_zero hE'.symm
    (isPathConnected_compl_singleton_of_one_lt_rank ?_ 0)
  rwa [← (E.quotientEquivOfIsCompl E' hE').rank_eq]

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is connected. -/
theorem isConnected_compl_of_one_lt_codim {E : Submodule ℝ F} (hcodim : 1 < Module.rank ℝ (F ⧸ E)) :
    IsConnected (Eᶜ : Set F) :=
  (isPathConnected_compl_of_one_lt_codim hcodim).isConnected

theorem Submodule.connectedComponentIn_eq_self_of_one_lt_codim (E : Submodule ℝ F)
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) {x : F} (hx : x ∉ E) :
    connectedComponentIn ((E : Set F)ᶜ) x = (E : Set F)ᶜ :=
  (isConnected_compl_of_one_lt_codim hcodim).2.connectedComponentIn hx

end

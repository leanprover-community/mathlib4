/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu, Andrew Yang, Violeta Hernández Palacios, Johannes Hölzl, Mario Carneiro
-/
module

import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen

import Mathlib.Data.Fintype.Option
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Compactness.Compact

/-!
# Small inductive dimension

The small inductive dimension of a space is inductively defined as follows. Empty spaces have
small inductive dimension less than 0, and a topological space has dimension less than `n + 1` if
it has a topological basis whose elements have frontiers of dimension strictly less `n`.

In this file we formalize this notion, and characterize the cases `n = 0` and `n = 1`.

## Main definitions

* `HasSmallInductiveDimensionLT X n` : Provides a class stating that `X` has small inductive
  dimension less than `n`.
* `HasSmallInductiveDimensionLE X n` : Provides an abbrev for
  `HasSmallInductiveDimensionLT X (n + 1)`.
* `smallInductiveDimension X` : The small inductive dimension of `X`, with values in `WithBot ℕ∞`.

## References

* https://en.wikipedia.org/wiki/Inductive_dimension
-/

@[expose] public section

open Set TopologicalSpace Topology

/--
For a topological space, the property of having small inductive dimension less than `n : ℕ`  is
inductively defined as follows. Empty spaces have small inductive dimension less than 0, and a
topological space has dimension less than `n + 1` if it has a topological basis whose elements have
frontiers of dimension strictly less `n`.
-/
class inductive HasSmallInductiveDimensionLT.{u} :
  ∀ (X : Type u) [TopologicalSpace X], ℕ → Prop where
  | zero {X : Type u} [TopologicalSpace X] [IsEmpty X] : HasSmallInductiveDimensionLT X 0
  | succ {X : Type u} [TopologicalSpace X] (n : ℕ) (s : Set (Set X)) (hs : IsTopologicalBasis s)
      (h : ∀ U ∈ s, HasSmallInductiveDimensionLT (frontier U) n) :
      HasSmallInductiveDimensionLT X (n + 1)

variable {X : Type*} [TopologicalSpace X]

variable (X) in
/-- A topological space has dimension `≤ n` if it has dimension `< n + 1`. -/
abbrev HasSmallInductiveDimensionLE (n : ℕ) :=
  HasSmallInductiveDimensionLT X (n + 1)

variable (X) in
/-- The small inductive dimension of a topological space. -/
@[no_expose]
noncomputable def smallInductiveDimension : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasSmallInductiveDimensionLT X i}

lemma hasSmallInductiveDimensionLT_zero_iff : HasSmallInductiveDimensionLT X 0 ↔ IsEmpty X :=
  ⟨fun h ↦ by cases h; assumption, fun _ ↦ .zero⟩

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_zero_iff := hasSmallInductiveDimensionLT_zero_iff

theorem HasSmallInductiveDimensionLT.mono {m n : ℕ} (hmn : m ≤ n)
    (H : HasSmallInductiveDimensionLT X m) : HasSmallInductiveDimensionLT X n := by
  induction n generalizing m X with
  | zero => simp_all
  | succ m IH =>
    cases H with
    | zero => exact .succ _ ∅ (by simpa) (by simp)
    | succ n s hs h =>
      refine .succ _ s hs fun U hU ↦ IH ?_ (h U hU)
      rwa [add_le_add_iff_right] at hmn

theorem HasSmallInductiveDimensionLE.mono {m n : ℕ} (hmn : m ≤ n)
    (H : HasSmallInductiveDimensionLE X m) : HasSmallInductiveDimensionLE X n := by
  apply HasSmallInductiveDimensionLT.mono _ H
  rwa [add_le_add_iff_right]

theorem HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE {n : ℕ}
    (H : HasSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLE X n :=
  HasSmallInductiveDimensionLT.mono n.le_succ H

instance (n : ℕ) [IsEmpty X] : HasSmallInductiveDimensionLT X n :=
  .mono zero_le <| hasSmallInductiveDimensionLT_zero_iff.2 ‹_›

/-! ### Zero-dimensional spaces -/

variable (X) in
/-- A zero-dimensional topological space is defined as one with small inductive dimension ≤ 0. In
particular, our definition of `ZeroDimensionalSpace` allows the empty space even though, strictly
speaking, it is (-1)-dimensional.

An equivalent characterization is that a zero-dimensional space is one with a basis of clopen
sets. -/
abbrev ZeroDimensionalSpace :=
  HasSmallInductiveDimensionLT X 1

theorem zeroDimensionalSpace_def : ZeroDimensionalSpace X ↔ HasSmallInductiveDimensionLT X 1 :=
  .rfl

theorem zeroDimensionalSpace_def' : ZeroDimensionalSpace X ↔ HasSmallInductiveDimensionLE X 0 :=
  .rfl

lemma zeroDimensionalSpace_iff_isTopologicalBasis :
    ZeroDimensionalSpace X ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU ↦ hU.isOpen) (fun U hU ↦ ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h ↦ .succ 0 _ h fun _ hU ↦ hU.frontier_eq ▸ .zero

@[deprecated (since := "2026-07-28")]
alias hasSmallInductiveDimensionLT_one_iff := zeroDimensionalSpace_iff_isTopologicalBasis

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_one_iff := zeroDimensionalSpace_iff_isTopologicalBasis

theorem isTopologicalBasis_isClopen [ZeroDimensionalSpace X] :
    IsTopologicalBasis { s : Set X | IsClopen s } :=
  zeroDimensionalSpace_iff_isTopologicalBasis.1 ‹_›

theorem ZeroDimensionalSpace.of_isTopologicalBasis {u : Set (Set X)} (hs : ∀ s ∈ u, IsClopen s)
    (hu : IsTopologicalBasis u) : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis]
  exact hu.of_isOpen_of_subset (fun _ ↦ IsClopen.isOpen) hs

theorem zeroDimensionalSpace_iff_isTopologicalBasis_iff_nhds_basis :
    ZeroDimensionalSpace X ↔ ∀ x : X, (𝓝 x).HasBasis (fun s ↦ IsClopen s ∧ x ∈ s) id where
  mp _ _ := isTopologicalBasis_isClopen.nhds_hasBasis
  mpr H := by
    rw [zeroDimensionalSpace_iff_isTopologicalBasis]
    exact .of_hasBasis_nhds H

theorem nhds_basis_isClopen [ZeroDimensionalSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s : Set X ↦ IsClopen s ∧ x ∈ s) id :=
  (isTopologicalBasis_isClopen (X := X)).nhds_hasBasis

@[deprecated nhds_basis_isClopen (since := "2026-07-28")]
theorem nhds_basis_clopen [ZeroDimensionalSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s : Set X ↦ x ∈ s ∧ IsClopen s) id := by
  simp_rw [and_comm]; exact nhds_basis_isClopen x

theorem exists_isClopen_mem_of_isOpen [ZeroDimensionalSpace X] {x : X} {U : Set X}
    (hU : IsOpen U) (hx : x ∈ U) : ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  isTopologicalBasis_isClopen.mem_nhds_iff.1 (hU.mem_nhds hx)

@[deprecated (since := "2026-07-28")]
alias compact_exists_isClopen_in_isOpen := exists_isClopen_mem_of_isOpen

theorem ZeroDimensionalSpace.of_hasBasis
    (H : ∀ x : X, ∃ (ι : Sort*) (p : ι → Prop) (s : ι → Set X),
      (∀ i, p i → IsClopen (s i)) ∧ (𝓝 x).HasBasis p s) :
    ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_iff_nhds_basis]
  intro x
  obtain ⟨ι, p, s, hx, hx'⟩ := H x
  apply hx'.to_hasBasis'
  · exact fun i hi ↦ ⟨s i, ⟨hx i hi, mem_of_mem_nhds (hx'.mem_of_mem hi)⟩, subset_rfl⟩
  · exact fun s ⟨hs, hx⟩ ↦ hs.isOpen.mem_nhds hx

instance [DiscreteTopology X] : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis]
  simpa using isTopologicalBasis_opens (α := X)

instance [IndiscreteTopology X] : ZeroDimensionalSpace X := by
  refine ZeroDimensionalSpace.of_hasBasis fun x ↦ ?_
  rw [IndiscreteTopology.nhds_eq]
  exact ⟨_, _, _, fun _ _ ↦ isClopen_univ, Filter.hasBasis_top⟩

section CompactSpace
variable [ZeroDimensionalSpace X] [CompactSpace X]

/-- In a zero-dimensional compact space `X`, if `Z ⊆ U` are subsets with `Z` closed
and `U` open, there exists a clopen `C` with `Z ⊆ C ⊆ U`. -/
theorem exists_clopen_of_closed_subset_open
    {Z U : Set X} (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every `z ∈ Z` has clopen neighborhood `V z ⊆ U`
  choose V hV using fun z : Z ↦ exists_isClopen_mem_of_isOpen hU (hZU z.property)
  -- the `V z` cover `Z`
  have V_cover : Z ⊆ ⋃ z, V z := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- choose a finite subcover
  choose I hI using hZ.isCompact.elim_finite_subcover V (fun z ↦ (hV z).1.isOpen) V_cover
  -- the union of this finite subcover does the job
  exact ⟨⋃ i ∈ I, V i, I.finite_toSet.isClopen_biUnion (fun i _ ↦ (hV i).1), hI, by simp_all⟩

/-- Let `X` be a totally disconnected compact Hausdorff space, `D i ⊆ X` a finite family of clopens,
and `Z i ⊆ D i` closed. Assume that the `Z i` are pairwise disjoint. Then there exist clopens
`Z i ⊆ C i ⊆ D i` with the `C i` disjoint, and such that `∪ D i ⊆ ∪ C i`. -/
theorem exists_clopen_partition_of_clopen_cover
    {I : Type*} [Finite I] {Z D : I → Set X}
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : univ.PairwiseDisjoint Z) :
    ∃ C : I → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    ⋃ i, D i ⊆ ⋃ i, C i ∧ univ.PairwiseDisjoint C := by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := IH (Z := Z ∘ e) (D := D ∘ e)
      (fun i ↦ Z_closed (e i)) (fun i ↦ D_clopen (e i))
      (fun i ↦ Z_subset_D (e i)) (by simpa [← e.injective.injOn.pairwiseDisjoint_image])
    refine ⟨C ∘ e.symm, fun i ↦ h1 (e.symm i), fun i ↦ by simpa using h2 (e.symm i),
      fun i ↦ by simpa using h3 (e.symm i), ?_,
      by simpa [← e.symm.injective.injOn.pairwiseDisjoint_image]⟩
    simp only [Function.comp_apply, iUnion_subset_iff] at h4
    simpa [e.symm.surjective.iUnion_comp C] using fun i ↦ h4 (e.symm i)
  | h_empty => exact ⟨fun _ ↦ univ, by simp, by simp, by simp, by simp, fun i ↦ PEmpty.elim i⟩
  | @h_option I _ IH =>
    -- let `Z'` be the restriction of `Z` along `some : I → Option I`
    let Z' : I → Set X := fun i ↦ Z (some i)
    have Z'_closed (i : I) : IsClosed (Z (some i)) := Z_closed (some i)
    have Z'_disj : univ.PairwiseDisjoint (Z ∘ some) := by
      rw [← (Option.some_injective _).injOn.pairwiseDisjoint_image]
      exact PairwiseDisjoint.subset Z_disj (by simp)
    -- find `Z none ⊆ V ⊆ D none \ ⋃ Z'` using `exists_clopen_of_closed_subset_open`
    let U : Set X := D none \ ⋃ i, Z (some i)
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen none).2
      (isClosed_iUnion_of_finite (fun i ↦ Z_closed (some i)))
    have Z0_subset_U : Z none ⊆ U := by
      rw [subset_sdiff]
      simpa using ⟨Z_subset_D none, fun i ↦ (by apply Z_disj; all_goals simp)⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      exists_clopen_of_closed_subset_open (Z_closed none) U_open Z0_subset_U
    have V_subset_D0 : V ⊆ D none := subset_trans V_subset_U sdiff_subset
    -- choose `Z' i ⊆ C' i ⊆ D' i = D i.succ \ V` using the inductive hypothesis
    let D' : I → Set X := fun i ↦ D (some i) \ V
    have D'_clopen (i : I) : IsClopen (D' i) := (D_clopen (some i)).diff V_clopen
    have Z'_subset_D' (i : I) : Z' i ⊆ D' i := by
      rw [subset_sdiff]
      refine ⟨by grind, Disjoint.mono_right V_subset_U ?_⟩
      exact Disjoint.mono_left (subset_iUnion_of_subset i fun _ h ↦ h) (by grind)
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      IH Z'_closed D'_clopen Z'_subset_D' Z'_disj
    -- now choose `C0 = D none \ ⋃ C' i`
    let C0 : Set X := D none \ ⋃ i, C' i
    have : IsClopen C0 := (D_clopen none).diff (isClopen_iUnion_of_finite C'_clopen)
    have : Z none ⊆ C0 := by
      simp only [C0, subset_sdiff]
      exact ⟨by grind, Disjoint.mono_left Z0_subset_V (by simp; grind)⟩
    -- patch together to define `C none := C0`, `C (some i) := C' i`
    -- and verify the needed properties
    let C : Option I → Set X := fun i ↦ Option.casesOn i C0 C'
    refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rintro (_ | i); all_goals grind
    · intro x hx
      rw [mem_iUnion] at hx ⊢
      by_cases hx0 : x ∈ C0; { exact ⟨none, hx0⟩ }
      by_cases hxD : x ∈ D none
      · have hxC' : x ∈ ⋃ i, C' i := by grind
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
        exact ⟨some i, hi⟩
      · obtain ⟨none | j, hi⟩ := hx; {grind}
        have hxD' : x ∈ ⋃ i, D' i := mem_iUnion.mpr ⟨j, by grind⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp <| C'_cover_D' hxD'
        exact ⟨some k, hk⟩
    · rw [Set.pairwiseDisjoint_iff]
      rintro (_ | i) _ (_ | j) _
      · simp
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_right (subset_iUnion C' j) disjoint_sdiff_left
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_left (subset_iUnion C' i) disjoint_sdiff_right
      · simpa using (Set.pairwiseDisjoint_iff.mp C'_disj) (by trivial) (by trivial)

end CompactSpace

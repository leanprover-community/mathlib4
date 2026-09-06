/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.ClosedUnion
public import Mathlib.Topology.CoveringDimension.Partition
public import Mathlib.Topology.CoveringDimension.ClosedSwelling
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.SmallInductiveDimension

/-! # Covering dimension and small inductive dimension -/

public section

open TopologicalSpace

universe u

/-- A covering-dimension bound separates a closed set from the
complement of an open neighborhood by an open set with lower-dimensional frontier. -/
lemma exists_open_between_frontier_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {K U : Set X} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ V : Set X,
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧
        HasCoveringDimensionLT ↥(frontier V) n := by
  -- Apply the closed-pair partition theorem to `K` and the closed complement of `U`.
  simpa only [compl_compl] using
    existsOpenPartition_of_hasCoveringDimensionLE h hK hU.isClosed_compl hKU.disjoint_compl_right

/-- Finitely many locally controlled neighborhoods cover a closed
compact set while their union still has closure inside the prescribed ambient open set. -/
lemma existsFiniteLocalFrontierCover
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n)
    {K U : Set X} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (s : Finset K) (V : K → Set X),
      (∀ x, IsOpen (V x) ∧ x.1 ∈ V x ∧ closure (V x) ⊆ U ∧
        HasCoveringDimensionLT ↥(frontier (V x)) n) ∧
      K ⊆ ⋃ x ∈ s, V x ∧
      IsOpen (⋃ x ∈ s, V x) ∧
      closure (⋃ x ∈ s, V x) ⊆ U ∧
      frontier (⋃ x ∈ s, V x) ⊆ ⋃ x ∈ s, frontier (V x) := by
  classical
  -- Choose one controlled neighborhood for every point of the closed set.
  have hchoice (x : K) :
      ∃ V : Set X,
        IsOpen V ∧ x.1 ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n :=
    hlocal x.1 U (hKU x.2) hU
  choose V hVopen hxV hVclosure hVfrontier using hchoice
  -- Compactness reduces this point-indexed cover to finitely many chosen neighborhoods.
  have hKcover : K ⊆ ⋃ x : K, V x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨s, hscover⟩ := hK.isCompact.elim_finite_subcover V hVopen hKcover
  refine ⟨s, V, ?_, hscover, ?_, ?_, ?_⟩
  · intro x
    exact ⟨hVopen x, hxV x, hVclosure x, hVfrontier x⟩
  · exact isOpen_biUnion fun x _ ↦ hVopen x
  · -- Finite unions commute with closure, so each selected closure remains inside `U`.
    rw [Finset.closure_biUnion]
    exact Set.iUnion₂_subset fun x _ ↦ hVclosure x
  · -- The union frontier lies in the finite union of the selected controlled frontiers.
    exact s.frontier_biUnion_subset V

/-- A finite open cover decomposes away from its
frontiers into pairwise disjoint open cores, each contained in its original member. -/
lemma existsPairwiseDisjointOpenCores
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (V : ι → Opens X) (hVcover : IsOpenCover V) :
    ∃ D : ι → Set X,
      (∀ i, IsOpen (D i)) ∧
      (∀ i, D i ⊆ V i) ∧
      Pairwise (fun i j ↦ Disjoint (D i) (D j)) ∧
      (⋃ i, frontier (V i : Set X))ᶜ ⊆ ⋃ i, D i := by
  classical
  let _ := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let D : ι → Set X := fun i ↦
    (V i : Set X) \ ⋃ j : {j : ι // j < i}, closure (V j.1 : Set X)
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · -- Earlier closures form a finite closed union, so removing them preserves openness.
    intro i
    exact (V i).2.sdiff <| isClosed_iUnion_of_finite fun j ↦ isClosed_closure
  · -- Every core is obtained by deleting points from its indexed cover member.
    intro i
    exact Set.sdiff_subset
  · -- The later core omits the closure of every earlier cover member.
    intro i j hij
    simp only [D, Set.disjoint_left, Set.mem_sdiff, Set.mem_iUnion, Subtype.exists]
    grind [subset_closure]
  · -- Choose the least cover member containing the point; off all frontiers, no earlier closure
    -- can contain it, because closure minus frontier is the open set itself.
    intro x hxfrontier
    obtain ⟨i, hxi, himin⟩ :=
      Set.exists_min_image {i : ι | x ∈ V i} (fun i ↦ i) (Set.toFinite _)
        (hVcover.exists_mem x)
    refine Set.mem_iUnion.mpr ⟨i, hxi, ?_⟩
    intro hxEarlier
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxEarlier
    have hxnotFrontier : x ∉ frontier (V j.1 : Set X) := by
      intro hxjfrontier
      exact hxfrontier <| Set.mem_iUnion.mpr ⟨j.1, hxjfrontier⟩
    have hxjOpen : x ∈ V j.1 := by
      exact interior_subset (closure_sdiff_frontier (s := (V j.1 : Set X)) ▸ ⟨hxj, hxnotFrontier⟩)
    exact (not_lt_of_ge (himin j.1 hxjOpen)) j.2

/-- Every controlled closed-pair partition yields the corresponding
covering-dimension bound on a compact metrizable space. -/
lemma hasCoveringDimensionLE_of_openPartitions
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (hpartition : ∀ K F : Set X, IsClosed K → IsClosed F → Disjoint K F →
      ∃ V : Set X,
        IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Fᶜ ∧
          HasCoveringDimensionLT ↥(frontier V) n) :
    HasCoveringDimensionLE X n := by
  classical
  -- Begin with a finite shrinking of the requested cover and separate each closed shrinking from
  -- the complement of its parent open set.
  rw [hasCoveringDimensionLE_iff]
  intro 𝒜 h𝒜open h𝒜cover
  let A : 𝒜 → Opens X := fun U ↦ ⟨U.1, h𝒜open U.1 U.2⟩
  have hA : IsOpenCover A :=
    IsOpenCover.of_sets _ (by simpa only [← Set.sUnion_eq_iUnion] using h𝒜cover)
  obtain ⟨ι, hιfinite, B, C, hBcover, hCcover, _, hBmem, hCclosure⟩ :=
    hA.exists_finite_shrinking
  have hBmem' (i : ι) : (B i : Set X) ∈ 𝒜 := by
    obtain ⟨U, hU⟩ := hBmem i
    rw [← hU]
    exact U.2
  let p : ι → 𝒜 := fun i ↦ ⟨B i, hBmem' i⟩
  have hBp (i : ι) : (B i : Set X) ⊆ p i := Set.Subset.rfl
  let _ : Finite ι := hιfinite
  have hseparator (i : ι) :
      ∃ V : Set X,
        IsOpen V ∧ closure (C i : Set X) ⊆ V ∧ closure V ⊆ B i ∧
          HasCoveringDimensionLT ↥(frontier V) n := by
    simpa only [compl_compl] using
      hpartition (closure (C i : Set X)) (B i : Set X)ᶜ isClosed_closure
        (B i).2.isClosed_compl (hCclosure i).disjoint_compl_right
  choose V hVopen hCV hVclosure hVfrontier using hseparator
  let VO : ι → Opens X := fun i ↦ ⟨V i, hVopen i⟩
  have hVcover : IsOpenCover VO := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := hCcover.exists_mem x
    exact Set.mem_iUnion.mpr ⟨i, hCV i (subset_closure hxi)⟩
  obtain ⟨D, hDopen, hDV, hDdisjoint, hDcover⟩ :=
    existsPairwiseDisjointOpenCores VO hVcover
  -- The only points not covered by the disjoint cores lie in the finite union of controlled
  -- frontiers, which still has strict covering dimension below `n`.
  let L : Set X := ⋃ i, frontier (V i)
  have hLclosed : IsClosed L := isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier
  have hLdim : HasCoveringDimensionLT L n :=
    hasCoveringDimensionLT_finiteUnionClosedSubtypes
      (fun i ↦ frontier (V i)) (fun _ ↦ isClosed_frontier) hVfrontier
  cases n with
  | zero =>
      have hLempty : IsEmpty L := hLdim
      have hDcoverUniv : ⋃ i, D i = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        have hxnotL : x ∉ L := by
          intro hx
          exact hLempty.false ⟨x, hx⟩
        exact hDcover hxnotL
      refine ⟨Set.range D, ?_, ?_, ?_, ?_⟩
      · rintro U ⟨i, rfl⟩
        exact ⟨p i, (p i).2,
          (hDV i).trans (subset_closure.trans (hVclosure i) |>.trans (hBp i))⟩
      · rintro U ⟨i, rfl⟩
        exact hDopen i
      · rw [Set.sUnion_range]
        exact hDcoverUniv
      · exact Set.hasOrderLE_one_iff.mpr hDdisjoint.range_pairwise
  | succ q =>
      -- Refine the traces of the original finite cover on the closed frontier locus, then swell
      -- its closed shrinking back into the ambient space without changing its nerve.
      let _ : CompactSpace L := isCompact_iff_compactSpace.mp hLclosed.isCompact
      let A : ι → Opens L := fun i ↦ (B i).comap ⟨Subtype.val, continuous_subtype_val⟩
      have hA : IsOpenCover A := hBcover.comap ⟨Subtype.val, continuous_subtype_val⟩
      obtain ⟨κ, hκfinite, R, S, a, hRcover, hScover, hRorder, hRinjective,
          hRparent, hSclosure⟩ :=
        existsFiniteIndexedShrinkingRefinement hLdim A hA
      let _ : Finite κ := hκfinite
      have hRA : ∀ j, Subtype.val '' (R j : Set L) ⊆ (B (a j) : Set X) :=
        fun j ↦ Set.image_subset_iff.mpr (hRparent j)
      obtain ⟨E, hLE, hEclosure, hEorder⟩ :=
        existsAmbientOpenSwelling_of_closedSubtypeCover hLclosed hScover hRorder
          hRinjective hSclosure (fun j ↦ B (a j)) hRA
      let F : Sum κ ι → Set X := Sum.elim (fun j ↦ (E j : Set X)) D
      refine ⟨Set.range F, ?_, ?_, ?_, ?_⟩
      · rintro U ⟨j, rfl⟩
        cases j with
        | inl j =>
            exact ⟨p (a j), (p (a j)).2,
              subset_closure.trans (hEclosure j) |>.trans (hBp (a j))⟩
        | inr i =>
            exact ⟨p i, (p i).2,
              (hDV i).trans (subset_closure.trans (hVclosure i) |>.trans (hBp i))⟩
      · rintro U ⟨j, rfl⟩
        cases j with
        | inl j => exact (E j).isOpen
        | inr i => exact hDopen i
      · rw [Set.sUnion_range]
        apply Set.eq_univ_of_forall
        intro x
        by_cases hxL : x ∈ L
        · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hLE hxL)
          exact Set.mem_iUnion.mpr ⟨Sum.inl j, hxj⟩
        · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hDcover hxL)
          exact Set.mem_iUnion.mpr ⟨Sum.inr i, hxi⟩
      · simpa only [F, Set.Sum.elim_range] using
          hEorder.union (Set.hasOrderLE_one_iff.mpr hDdisjoint.range_pairwise)

/-- Local frontier control produces a controlled partition between
any two disjoint closed subsets. -/
lemma existsOpenPartition_of_localFrontier
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n)
    {K F : Set X} (hK : IsClosed K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ V : Set X,
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Fᶜ ∧
        HasCoveringDimensionLT ↥(frontier V) n := by
  -- Select finitely many local neighborhoods around `K` inside the complement of `F`.
  classical
  obtain ⟨s, V, hV, hKcover, hopen, hclosure, hfrontier⟩ :=
    existsFiniteLocalFrontierCover hlocal hK hF.isOpen_compl hKF.subset_compl_right
  let ι := {x : K // x ∈ s}
  let Y : ι → Set X := fun i ↦ frontier (V i.1)
  have hYclosed : ∀ i, IsClosed (Y i) := fun _ ↦ isClosed_frontier
  have hYdim : ∀ i, HasCoveringDimensionLT (Y i) n := fun i ↦ (hV i.1).2.2.2
  have hunion : HasCoveringDimensionLT (⋃ i, Y i) n :=
    hasCoveringDimensionLT_finiteUnionClosedSubtypes Y hYclosed hYdim
  have hfrontierUnion : frontier (⋃ x ∈ s, V x) ⊆ ⋃ i, Y i := by
    simpa only [Y, ι, Set.iUnion_subtype] using hfrontier
  have hfrontierDim : HasCoveringDimensionLT ↥(frontier (⋃ x ∈ s, V x)) n :=
    hunion.closedSubset hfrontierUnion isClosed_frontier
  exact ⟨⋃ x ∈ s, V x, hopen, hKcover, hclosure, hfrontierDim⟩

/-- Locally available neighborhoods with lower-dimensional
frontiers imply the corresponding covering-dimension bound. -/
lemma hasCoveringDimensionLE_of_local_frontier
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n) :
    HasCoveringDimensionLE X n := by
  -- Build the required closed-pair partitions from the local neighborhoods, then invoke the
  -- finite-cover partition characterization.
  apply hasCoveringDimensionLE_of_openPartitions
  intro K F hK hF hKF
  exact existsOpenPartition_of_localFrontier hlocal hK hF hKF

/-- A local supply of open neighborhoods with controlled frontiers
forms a topological basis. -/
lemma frontierControlledBasis_of_local_frontier
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n) :
    ∃ s : Set (Set X),
      IsTopologicalBasis s ∧ ∀ U ∈ s, HasCoveringDimensionLT ↥(frontier U) n := by
  -- Use all open sets with controlled frontier and verify the local basis criterion.
  let s : Set (Set X) :=
    {U | IsOpen U ∧ HasCoveringDimensionLT ↥(frontier U) n}
  have hs : IsTopologicalBasis s := by
    apply isTopologicalBasis_opens.isTopologicalBasis_of_exists_subset
    · intro U hUs
      exact hUs.1
    · intro U hU x hxU
      obtain ⟨V, hVopen, hxV, hVclosure, hVfrontier⟩ := hlocal x U hxU hU
      exact ⟨V, ⟨hVopen, hVfrontier⟩, hxV, subset_closure.trans hVclosure⟩
  refine ⟨s, hs, ?_⟩
  intro U hUs
  exact hUs.2

/-- A frontier-bounded basis gives the corresponding covering
dimension bound on a compact metrizable space. -/
lemma hasCoveringDimensionLE_of_basis_frontier
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (s : Set (Set X)) (hs : IsTopologicalBasis s)
    (hfrontier : ∀ U ∈ s, HasCoveringDimensionLT ↥(frontier U) n) :
    HasCoveringDimensionLE X n := by
  -- Use the closure-controlled neighborhood basis of a regular space.
  apply hasCoveringDimensionLE_of_local_frontier
  intro x U hxU hU
  obtain ⟨V, hVs, hxV, hVU⟩ := hs.exists_closure_subset (hU.mem_nhds hxU)
  exact ⟨V, hs.isOpen hVs, hxV, hVU, hfrontier V hVs⟩

/-- A covering dimension bound on a compact metrizable space yields
a basis whose frontiers satisfy the preceding strict bound. -/
lemma exists_basis_frontier_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) :
    ∃ s : Set (Set X),
      IsTopologicalBasis s ∧ ∀ U ∈ s, HasCoveringDimensionLT ↥(frontier U) n := by
  -- Apply the separator theorem to singletons and package the resulting neighborhoods as a basis.
  apply frontierControlledBasis_of_local_frontier
  intro x U hxU hU
  obtain ⟨V, hVopen, hxV, hVclosure, hVfrontier⟩ :=
    exists_open_between_frontier_of_hasCoveringDimensionLE h isClosed_singleton hU
      (Set.singleton_subset_iff.mpr hxU)
  exact ⟨V, hVopen, hxV rfl, hVclosure, hVfrontier⟩

/-- Strict small inductive and covering dimension bounds agree on
compact metrizable spaces. -/
lemma hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] (k : ℕ) :
    HasSmallInductiveDimensionLT X k ↔ HasCoveringDimensionLT X k := by
  -- Induct on the strict bound, using emptiness at zero and the frontier-basis interface at
  -- successor bounds.
  induction k generalizing X with
  | zero =>
      rw [hasSmallInductiveDimensionLT_zero_iff, hasCoveringDimensionLT_zero_iff]
  | succ n ih =>
      constructor
      · intro hsmall
        cases hsmall with
        | succ _ s hs hfrontier =>
            apply hasCoveringDimensionLE_of_basis_frontier s hs
            intro U hU
            let _ : CompactSpace ↥(frontier U) :=
              isCompact_iff_compactSpace.mp isClosed_frontier.isCompact
            exact (ih ↥(frontier U)).mp (hfrontier U hU)
      · intro hcover
        obtain ⟨s, hs, hfrontier⟩ := exists_basis_frontier_of_hasCoveringDimensionLE hcover
        refine .succ n s hs ?_
        intro U hU
        let _ : CompactSpace ↥(frontier U) :=
          isCompact_iff_compactSpace.mp isClosed_frontier.isCompact
        exact (ih ↥(frontier U)).mpr (hfrontier U hU)

/-- On compact metrizable spaces, the small inductive dimension has the same
value as the covering dimension, including the value `⊥` for the empty space. -/
theorem smallInductiveDimension_eq_coveringDimension
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] :
    smallInductiveDimension X = coveringDimension X := by
  refine eq_of_forall_ge_iff fun d ↦ ?_
  cases d with
  | bot =>
      rw [le_bot_iff, le_bot_iff, smallInductiveDimension_eq_bot,
        coveringDimension_eq_bot_iff]
  | coe d =>
      cases d with
      | top => simp
      | coe n =>
          exact smallInductiveDimension_le_iff.trans <|
            (hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT X (n + 1)).trans <|
              (coveringDimension_le_iff X n).symm

/-- On compact metrizable spaces, the natural-valued upper-bound predicates for small inductive
dimension and covering dimension agree. -/
theorem hasSmallInductiveDimensionLE_iff_hasCoveringDimensionLE
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] (n : ℕ) :
    HasSmallInductiveDimensionLE X n ↔ HasCoveringDimensionLE X n := by
  -- The non-strict predicates are the strict predicates at the common successor bound.
  exact hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT X (n + 1)

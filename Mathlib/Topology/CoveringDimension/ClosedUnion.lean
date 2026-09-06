/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Basic
import Mathlib.Data.Fintype.Lattice

/-! # Covering dimension of finite unions of closed subspaces -/

public section

open TopologicalSpace

open scoped CoveringDimension

universe u v

/-- Helper for Theorem 50.2: an open cover can be refined with controlled order at
the points of a closed subspace whose covering dimension is bounded. -/
private lemma existsOpenRefinementWithOrderOnClosedSet
    {X : Type u} [TopologicalSpace X] {S : Set X} {n : ℕ} {ι : Type v}
    (hSclosed : IsClosed S) (hSdim : HasCoveringDimensionLE S n)
    (A : ι → Opens X) (hA : IsOpenCover A) :
    ∃ (κ : Type (max u v)) (B : κ → Opens X),
      IsOpenCover B ∧ IsCofinalFor (Set.range B) (Set.range A) ∧
        ∀ s : S, Set.encard {U ∈ Set.range (fun i ↦ (B i : Set X)) | s.1 ∈ U} ≤
          (n + 1 : ℕ) := by
  classical
  let f : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨κ, V, hV, hVA, hVorder⟩ :=
    hSdim.exists_refinement (fun i ↦ (A i).comap f) (hA.comap f)
  -- Extend each distinct trace member inside a parent from the original cover.
  let 𝒱 := Set.range fun j ↦ (V j : Set S)
  have hlift (T : 𝒱) :
      ∃ (U : Opens X) (i : ι), f ⁻¹' (U : Set X) = T.1 ∧ U ≤ A i := by
    obtain ⟨j, hj⟩ := T.2
    obtain ⟨_, ⟨i, rfl⟩, hji⟩ := hVA (Set.mem_range_self j)
    change (V j : Set S) ⊆ f ⁻¹' (A i : Set X) at hji
    obtain ⟨U, hU, htrace⟩ := isOpen_induced_iff.mp (V j).isOpen
    refine ⟨⟨U, hU⟩ ⊓ A i, i, ?_, inf_le_right⟩
    change (Subtype.val ⁻¹' U) ∩ (f ⁻¹' (A i : Set X)) = T.1
    rw [htrace, Set.inter_eq_left.mpr hji]
    exact hj
  choose extended parent htrace hparent using hlift
  let outside (i : ι) : Opens X := ⟨(A i : Set X) \ S, (A i).isOpen.sdiff hSclosed⟩
  let B := Sum.elim extended outside
  refine ⟨𝒱 ⊕ ι, B, ?_, ?_, ?_⟩
  · apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxS : x ∈ S
    · obtain ⟨j, hj⟩ := hV.exists_mem ⟨x, hxS⟩
      let T : 𝒱 := ⟨V j, Set.mem_range_self j⟩
      apply Set.mem_iUnion.mpr ⟨Sum.inl T, ?_⟩
      exact show (⟨x, hxS⟩ : S) ∈ f ⁻¹' (extended T : Set X) from
        (htrace T).symm ▸ hj
    · obtain ⟨i, hi⟩ := hA.exists_mem x
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi, hxS⟩
  · rintro _ ⟨T | i, rfl⟩
    · exact ⟨A (parent T), Set.mem_range_self _, hparent T⟩
    · exact ⟨A i, Set.mem_range_self _, Set.sdiff_subset⟩
  · -- Reindexing by distinct trace members ensures repeated indices are counted only once.
    intro s
    let source : Set 𝒱 := {T | s ∈ T.1}
    have hsub : {U ∈ Set.range (fun i ↦ (B i : Set X)) | s.1 ∈ U} ⊆
        (fun T ↦ (extended T : Set X)) '' source := by
      rintro _ ⟨⟨T | i, rfl⟩, hs⟩
      · exact ⟨T, show s ∈ T.1 from htrace T ▸ hs, rfl⟩
      · exact (hs.2 s.2).elim
    calc
      _ ≤ Set.encard ((fun T ↦ (extended T : Set X)) '' source) := Set.encard_mono hsub
      _ ≤ Set.encard source := Set.encard_image_le _ _
      _ ≤ Set.encard {T ∈ 𝒱 | s ∈ T} :=
        Set.encard_le_encard_of_injOn (fun T hT ↦ ⟨T.2, hT⟩)
          Subtype.val_injective.injOn
      _ ≤ n + 1 := (Set.hasOrderLE_iff.mp hVorder) s

namespace HasCoveringDimensionLE

/-- Helper for Theorem 50.2: a common covering-dimension bound on two closed
subspaces covering `X` is also a bound on `X`. -/
theorem unionClosed
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (hYclosed : IsClosed Y) (hZclosed : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    (hYdim : HasCoveringDimensionLE Y n)
    (hZdim : HasCoveringDimensionLE Z n) :
    HasCoveringDimensionLE X n := by
  classical
  rw [hasCoveringDimensionLE_iff]
  intro 𝒜 h𝒜open h𝒜cover
  let A : 𝒜 → Opens X := fun U ↦ ⟨U.1, h𝒜open U.1 U.2⟩
  have hA : IsOpenCover A :=
    IsOpenCover.of_sets _ (by simpa only [← Set.sUnion_eq_iUnion] using h𝒜cover)
  -- First control multiplicity on `Y`, then refine once more to control it on `Z`.
  obtain ⟨κ, B, hB, hBA, hℬorderY⟩ :=
    existsOpenRefinementWithOrderOnClosedSet hYclosed hYdim A hA
  obtain ⟨ι, C, hC, hCB, h𝒞orderZ⟩ :=
    existsOpenRefinementWithOrderOnClosedSet hZclosed hZdim B hB
  let ℬ := Set.range fun i ↦ (B i : Set X)
  let 𝒞 := Set.range fun i ↦ (C i : Set X)
  have hℬrefines : IsCofinalFor ℬ 𝒜 := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hBA (Set.mem_range_self i)
    exact ⟨j.1, j.2, hj⟩
  have hparentExists (U : 𝒞) : ∃ V : ℬ, U.1 ⊆ V.1 := by
    obtain ⟨i, hi⟩ := U.2
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hCB (Set.mem_range_self i)
    exact ⟨⟨B j, Set.mem_range_self j⟩, hi ▸ hj⟩
  choose parent hparent using hparentExists
  -- Group all second-stage members having the same first-stage parent.
  let grouped : ℬ → Set X := fun B ↦
    ⋃ C : {C : 𝒞 // parent C = B}, (C.1.1 : Set X)
  let 𝒟 : Set (Set X) := Set.range grouped
  have h𝒟refinesℬ : IsCofinalFor 𝒟 ℬ := by
    rintro D ⟨B, rfl⟩
    refine ⟨B, B.2, ?_⟩
    intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    rw [← C.2]
    exact hparent C.1 hxC
  have h𝒟open : ∀ D ∈ 𝒟, IsOpen D := by
    rintro D ⟨B, rfl⟩
    apply isOpen_iUnion
    intro U
    obtain ⟨i, hi⟩ := U.1.2
    exact hi ▸ (C i).isOpen
  refine ⟨𝒟, h𝒟refinesℬ.trans hℬrefines, h𝒟open, ?_, ?_⟩
  · -- Each second-stage member lies in the group indexed by its chosen parent.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := hC.exists_mem x
    rw [Set.mem_sUnion]
    let j : 𝒞 := ⟨C i, Set.mem_range_self i⟩
    have hxGrouped : x ∈ grouped (parent j) := by
      rw [Set.mem_iUnion]
      exact ⟨⟨j, rfl⟩, hxi⟩
    exact ⟨grouped (parent j), ⟨parent j, rfl⟩, hxGrouped⟩
  · -- Over `Y` count parents; over `Z` count chosen second-stage witnesses.
    rw [Set.hasOrderLE_iff]
    intro x
    have hxYZ : x ∈ Y ∪ Z := hcover.symm ▸ Set.mem_univ x
    rcases hxYZ with hxY | hxZ
    · let y : Y := ⟨x, hxY⟩
      let source : Set ℬ := {B | x ∈ (B.1 : Set X)}
      have hsub : {D ∈ 𝒟 | x ∈ D} ⊆ grouped '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        have hxB : x ∈ (B.1 : Set X) := by
          rw [← C.2]
          exact hparent C.1 hxC
        exact ⟨B, hxB, rfl⟩
      calc
        Set.encard {D ∈ 𝒟 | x ∈ D}
            ≤ Set.encard (grouped '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le grouped source
        _ ≤ Set.encard {B ∈ ℬ | x ∈ B} :=
          Set.encard_le_encard_of_injOn (fun B hB ↦ ⟨B.2, hB⟩)
            Subtype.val_injective.injOn
        _ ≤ n + 1 := hℬorderY y
    · let z : Z := ⟨x, hxZ⟩
      let source : Set 𝒞 := {C | x ∈ (C.1 : Set X)}
      let groupOf : 𝒞 → Set X := fun C ↦ grouped (parent C)
      have hsub : {D ∈ 𝒟 | x ∈ D} ⊆ groupOf '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        refine ⟨C.1, hxC, ?_⟩
        exact congrArg grouped C.2
      calc
        Set.encard {D ∈ 𝒟 | x ∈ D}
            ≤ Set.encard (groupOf '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le groupOf source
        _ ≤ Set.encard {C ∈ 𝒞 | x ∈ C} :=
          Set.encard_le_encard_of_injOn (fun C hC ↦ ⟨C.2, hC⟩)
            Subtype.val_injective.injOn
        _ ≤ n + 1 := h𝒞orderZ z

end HasCoveringDimensionLE

/-- Theorem 50.2. If two closed subspaces cover `X`, then the covering dimension
of `X` is the maximum of their covering dimensions. -/
theorem coveringDimension_union_closed
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hY : IsClosed Y) (hZ : IsClosed Z) (hcover : Y ∪ Z = Set.univ) :
    dim X = max (dim Y) (dim Z) := by
  refine eq_of_forall_ge_iff fun d ↦ ?_
  cases d with
  | bot =>
      rw [le_bot_iff, le_bot_iff, max_eq_bot, coveringDimension_eq_bot_iff,
        coveringDimension_eq_bot_iff, coveringDimension_eq_bot_iff]
      constructor
      · intro hX
        exact ⟨⟨fun y ↦ hX.false y.1⟩, ⟨fun z ↦ hX.false z.1⟩⟩
      · rintro ⟨hYempty, hZempty⟩
        refine ⟨fun x ↦ ?_⟩
        rcases (show x ∈ Y ∪ Z from hcover.symm ▸ Set.mem_univ x) with hx | hx
        · exact hYempty.false ⟨x, hx⟩
        · exact hZempty.false ⟨x, hx⟩
  | coe d =>
      cases d with
      | top => simp
      | coe n =>
          change dim X ≤ (n : WithBot ℕ∞) ↔ max (dim Y) (dim Z) ≤ (n : WithBot ℕ∞)
          rw [max_le_iff, coveringDimension_le_iff, coveringDimension_le_iff,
            coveringDimension_le_iff]
          exact ⟨fun h ↦ ⟨h.closedSubtype hY, h.closedSubtype hZ⟩,
            fun h ↦ HasCoveringDimensionLE.unionClosed hY hZ hcover h.1 h.2⟩

/-! ### Finite closed unions -/

/-- Helper for Corollary 50.3: the covering dimension of the union of two
closed subsets is the maximum of their covering dimensions. -/
private lemma coveringDimension_closedUnion
    {X : Type u} [TopologicalSpace X] {S T : Set X}
    (hS : IsClosed S) (hT : IsClosed T) :
    dim (S ∪ T : Set X) = max (dim S) (dim T) := by
  -- Apply Theorem 50.2 inside the union subtype and hide its nested-subtype pieces.
  let U : Set X := S ∪ T
  let S' : Set U := (Subtype.val : U → X) ⁻¹' S
  let T' : Set U := (Subtype.val : U → X) ⁻¹' T
  have hS' : IsClosed S' := hS.preimage continuous_subtype_val
  have hT' : IsClosed T' := hT.preimage continuous_subtype_val
  have hcover : S' ∪ T' = Set.univ := Set.eq_univ_of_forall fun x ↦ x.2
  have hSsub : S ⊆ U := Set.subset_union_left
  have hTsub : T ⊆ U := Set.subset_union_right
  calc
    dim (S ∪ T : Set X) = dim U := rfl
    _ = max (dim S') (dim T') := coveringDimension_union_closed hS' hT' hcover
    _ = max (dim S) (dim T) := congrArg₂ max
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using hSsub)).coveringDimension_congr
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using hTsub)).coveringDimension_congr

/-- Helper for Corollary 50.3: covering dimension turns a finite union of
closed subsets into the finite supremum of their dimensions. -/
private lemma coveringDimension_finset_iUnion_closed
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (Y : I → Set X) (s : Finset I) (hclosed : ∀ i ∈ s, IsClosed (Y i)) :
    dim (⋃ i ∈ s, Y i) = s.sup fun i ↦ dim (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sup_insert]
      have hs : ∀ i ∈ s, IsClosed (Y i) := fun i hi ↦ hclosed i (Finset.mem_insert_of_mem hi)
      rw [coveringDimension_closedUnion (hclosed a (Finset.mem_insert_self _ _))
        (isClosed_biUnion_finset hs), ih hs]

/-- The covering dimension of a finite union of closed subsets is the supremum of their
covering dimensions. -/
theorem coveringDimension_iUnion_of_isClosed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i)) :
    dim (⋃ i, Y i) = ⨆ i, dim (Y i) := by
  let _ := Fintype.ofFinite ι
  have hunion : (⋃ i ∈ (Finset.univ : Finset ι), Y i) = ⋃ i, Y i := by simp
  rw [← hunion, coveringDimension_finset_iUnion_closed Y Finset.univ (fun i _ ↦ hclosed i),
    Finset.sup_univ_eq_iSup]

/-- Corollary 50.3. The covering dimension of a finite closed cover is the
maximum of the covering dimensions of its members. -/
theorem coveringDimension_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ) :
    dim X = Finset.univ.sup fun i ↦ dim (Y i) := by
  rw [Finset.sup_univ_eq_iSup, ← coveringDimension_iUnion_of_isClosed Y hclosed, hcover]
  exact (Homeomorph.Set.univ X).coveringDimension_congr.symm

/-- Helper for Definition 50.8: a finite closed cover inherits the common
covering-dimension bound. -/
lemma HasCoveringDimensionLE.finite_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ)
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE X n := by
  -- Convert the finite closed-union formula into numerical upper bounds.
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← coveringDimension_le_iff, coveringDimension_iUnion_closed Y hclosed hcover,
    Finset.sup_le_iff]
  intro i _
  exact (coveringDimension_le_iff (Y i) n).mpr (hdim i)

/-- Helper for Definition 50.8: a finite union of closed subspaces with a common
covering-dimension bound has that same bound. -/
lemma HasCoveringDimensionLE.finiteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE (⋃ i, Y i) n := by
  rw [← coveringDimension_le_iff, coveringDimension_iUnion_of_isClosed Y hclosed, iSup_le_iff]
  exact fun i ↦ (coveringDimension_le_iff (Y i) n).mpr (hdim i)

/-- Helper for Definition 50.8: the strict covering-dimension bound is preserved by finite
unions of closed subspaces. -/
lemma hasCoveringDimensionLT_finiteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLT (Y i) n) :
    HasCoveringDimensionLT (⋃ i, Y i) n := by
  -- At zero every member is empty; at a successor use the non-strict union theorem.
  cases n with
  | zero =>
      refine ⟨fun ⟨x, hx⟩ ↦ ?_⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (hdim i).false ⟨x, hi⟩
  | succ n =>
      exact HasCoveringDimensionLE.finiteUnionClosedSubtypes Y hclosed hdim

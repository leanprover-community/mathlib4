/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Separation properties: profinite spaces
-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Profinite

/-- A T0 space with a clopen basis is totally separated. -/
theorem totallySeparatedSpace_of_t0_of_basis_clopen [T0Space X]
    (h : IsTopologicalBasis { s : Set X | IsClopen s }) : TotallySeparatedSpace X := by
  constructor
  rintro x - y - hxy
  choose U hU using exists_isOpen_xor'_mem hxy
  obtain ⟨hU₀, hU₁⟩ := hU
  rcases hU₁ with hx | hy
  · choose V hV using h.isOpen_iff.mp hU₀ x hx.1
    exact ⟨V, Vᶜ, hV.1.isOpen, hV.1.compl.isOpen, hV.2.1, notMem_subset hV.2.2 hx.2,
      (union_compl_self V).superset, disjoint_compl_right⟩
  · choose V hV using h.isOpen_iff.mp hU₀ y hy.1
    exact ⟨Vᶜ, V, hV.1.compl.isOpen, hV.1.isOpen, notMem_subset hV.2.2 hy.2, hV.2.1,
      (union_comm _ _ ▸ union_compl_self V).superset, disjoint_compl_left⟩

@[deprecated (since := "2025-09-11")]
alias totallySeparatedSpace_of_t1_of_basis_clopen := totallySeparatedSpace_of_t0_of_basis_clopen

variable [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]

theorem nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id :=
  ⟨fun U => by
    constructor
    · have hx : connectedComponent x = {x} :=
        totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x
      rw [connectedComponent_eq_iInter_isClopen] at hx
      intro hU
      let N := { s // IsClopen s ∧ x ∈ s }
      rsuffices ⟨⟨s, hs, hs'⟩, hs''⟩ : ∃ s : N, s.val ⊆ U
      · exact ⟨s, ⟨hs', hs⟩, hs''⟩
      haveI : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
      have hNcl : ∀ s : N, IsClosed s.val := fun s => s.property.1.1
      have hdir : Directed Superset fun s : N => s.val := by
        rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
        exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left, inter_subset_right⟩
      have h_nhds : ∀ y ∈ ⋂ s : N, s.val, U ∈ 𝓝 y := fun y y_in => by
        rw [hx, mem_singleton_iff] at y_in
        rwa [y_in]
      exact exists_subset_nhds_of_compactSpace hdir hNcl h_nhds
    · rintro ⟨V, ⟨hxV, -, V_op⟩, hUV : V ⊆ U⟩
      rw [mem_nhds_iff]
      exact ⟨V, hUV, V_op, hxV⟩⟩

theorem isTopologicalBasis_isClopen : IsTopologicalBasis { s : Set X | IsClopen s } := by
  apply isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U ∈ 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩
  use V
  tauto

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set. -/
theorem compact_exists_isClopen_in_isOpen {x : X} {U : Set X} (is_open : IsOpen U) (memU : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  isTopologicalBasis_isClopen.mem_nhds_iff.1 (is_open.mem_nhds memU)

end Profinite

section LocallyCompact

variable {H : Type*} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
theorem loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] :
    IsTopologicalBasis { s : Set H | IsClopen s } := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) fun x U memU hU => ?_
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  let u : Set s := ((↑) : s → H) ⁻¹' interior s
  have u_open_in_s : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  lift x to s using interior_subset xs
  haveI : CompactSpace s := isCompact_iff_compactSpace.1 comp
  obtain ⟨V : Set s, VisClopen, Vx, V_sub⟩ := compact_exists_isClopen_in_isOpen u_open_in_s xs
  have VisClopen' : IsClopen (((↑) : s → H) '' V) := by
    refine ⟨comp.isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.1 VisClopen.1,
      ?_⟩
    let v : Set u := ((↑) : u → s) ⁻¹' V
    have : ((↑) : u → H) = ((↑) : s → H) ∘ ((↑) : u → s) := rfl
    have f0 : IsEmbedding ((↑) : u → H) := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    have f1 : IsOpenEmbedding ((↑) : u → H) := by
      refine ⟨f0, ?_⟩
      · have : Set.range ((↑) : u → H) = interior s := by
          rw [this, Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe]
          apply Set.inter_eq_self_of_subset_right interior_subset
        rw [this]
        apply isOpen_interior
    have f2 : IsOpen v := VisClopen.2.preimage continuous_subtype_val
    have f3 : ((↑) : s → H) '' V = ((↑) : u → H) '' v := by
      rw [this, image_comp, Subtype.image_preimage_coe, inter_eq_self_of_subset_right V_sub]
    rw [f3]
    apply f1.isOpenMap v f2
  use (↑) '' V, VisClopen', by simp [Vx], Subset.trans (by simp) sU

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep :
    TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H := by
  constructor
  · intro h
    exact totallySeparatedSpace_of_t0_of_basis_clopen loc_compact_Haus_tot_disc_of_zero_dim
  apply TotallySeparatedSpace.totallyDisconnectedSpace

/-- A totally disconnected compact Hausdorff space is totally separated. -/
instance (priority := 100) [TotallyDisconnectedSpace H] : TotallySeparatedSpace H :=
  loc_compact_t2_tot_disc_iff_tot_sep.mp inferInstance

/-- In a totally disconnected compact Hausdorff space `X`, if `Z ⊆ U` are subsets with `Z` closed
and `U` open, there exists a clopen `C` with `Z ⊆ C ⊆ U`. -/
lemma exists_clopen_of_closed_subset_open {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {Z U : Set X} (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every `z ∈ Z` has clopen neighborhood `V z ⊆ U`
  choose V hV using fun (z : Z) ↦ compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the `V z` cover `Z`
  have V_cover : Z ⊆ ⋃ z, V z := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- choose a finite subcover
  choose I hI using hZ.isCompact.elim_finite_subcover V (fun z ↦ (hV z).1.isOpen) V_cover
  -- the union of this finite subcover does the job
  exact ⟨⋃ (i ∈ I), V i, I.finite_toSet.isClopen_biUnion (fun i _ ↦ (hV i).1), hI, by simp_all⟩

/-- Let `X` be a totally disconnected compact Hausdorff space, `D i ⊆ X` a finite family of clopens,
and `Z i ⊆ D i` closed. Assume that the `Z i` are pairwise disjoint. Then there exist clopens
`Z i ⊆ C i ⊆ D i` with the `C i` disjoint, and such that `∪ D i ⊆ ∪ C i`. -/
lemma exists_clopen_partition_of_clopen_cover
    {X I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [Finite I] {Z D : I → Set X}
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : univ.PairwiseDisjoint Z) :
    ∃ C : I → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    (⋃ i, D i) ⊆ (⋃ i, C i) ∧ (univ.PairwiseDisjoint C) := by
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
      rw [subset_diff]
      simpa using ⟨Z_subset_D none, fun i ↦ (by apply Z_disj; all_goals simp)⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      exists_clopen_of_closed_subset_open (Z_closed none) U_open Z0_subset_U
    have V_subset_D0 : V ⊆ D none := subset_trans V_subset_U diff_subset
    -- choose `Z' i ⊆ C' i ⊆ D' i = D i.succ \ V` using the inductive hypothesis
    let D' : I → Set X := fun i ↦ D (some i) \ V
    have D'_clopen (i : I) : IsClopen (D' i) := (D_clopen (some i)).diff V_clopen
    have Z'_subset_D' (i : I) : Z' i ⊆ D' i := by
      rw [subset_diff]
      refine ⟨by grind, Disjoint.mono_right V_subset_U ?_⟩
      exact Disjoint.mono_left (subset_iUnion_of_subset i fun _ h ↦ h) (by grind)
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      IH Z'_closed D'_clopen Z'_subset_D' Z'_disj
    -- now choose `C0 = D none \ ⋃ C' i`
    let C0 : Set X := D none \ ⋃ i, C' i
    have : IsClopen C0 := (D_clopen none).diff (isClopen_iUnion_of_finite C'_clopen)
    have : Z none ⊆ C0 := by
      simp only [C0, subset_diff]
      exact ⟨by grind, Disjoint.mono_left Z0_subset_V (by simpa using by grind)⟩
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

end LocallyCompact

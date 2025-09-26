/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Separation properties: profinite spaces
-/

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

end LocallyCompact

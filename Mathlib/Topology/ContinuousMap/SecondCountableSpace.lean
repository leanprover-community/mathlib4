/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.CompactOpen

/-!
# Second countable topology on `C(X, Y)`

In this file we prove that `C(X, Y)` with compact-open topology has second countable topology, if

- both `X` and `Y` have second countable topology;
- `X` is a locally compact space;
- `X` is an `R₁` space.
-/

open scoped Topology
open Set Function Filter TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem compactOpen_eq_generateFrom {S : Set (Set X)} {T : Set (Set Y)}
    (hS₁ : ∀ K ∈ S, IsCompact K) (hT : IsTopologicalBasis T)
    (hS₂ : ∀ f : C(X, Y), ∀ x, ∀ V ∈ 𝓝 (f x), ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    compactOpen = .generateFrom (.image2 (fun K t ↦
      {f : C(X, Y) | MapsTo f K (⋃₀ t)}) S {t : Set (Set Y) | t.Finite ∧ t ⊆ T}) := by
  apply le_antisymm
  · apply_rules [generateFrom_anti, image2_subset_iff.mpr]
    intro K hK t ht
    exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h ↦ hT.isOpen <| ht.2 h)
  · refine le_of_nhds_le_nhds fun f ↦ ?_
    simp only [nhds_compactOpen, le_iInf_iff, le_principal_iff]
    intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
    simp only [TopologicalSpace.nhds_generateFrom]
    obtain ⟨t, htT, htf, hTU, hKT⟩ : ∃ t ⊆ T, t.Finite ∧ (∀ V ∈ t, V ⊆ U) ∧ f '' K ⊆ ⋃₀ t := by
      rw [hT.open_eq_sUnion' hU, mapsTo', sUnion_eq_biUnion] at hfKU
      obtain ⟨t, ht, hfin, htK⟩ :=
        (hK.image (map_continuous f)).elim_finite_subcover_image (fun V hV ↦ hT.isOpen hV.1) hfKU
      refine ⟨t, fun _ h ↦ (ht h).1, hfin, fun _ h ↦ (ht h).2, ?_⟩
      rwa [sUnion_eq_biUnion]
    rw [image_subset_iff] at hKT
    obtain ⟨s, hsS, hsf, hKs, hst⟩ : ∃ s ⊆ S, s.Finite ∧ K ⊆ ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
      choose! L hLS hLmem hLt using fun x hx ↦ hS₂ f x (⋃₀ t)
        ((isOpen_sUnion fun _ h ↦ hT.isOpen (htT h)).mem_nhds (hKT hx))
      rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
      refine ⟨L '' s, image_subset_iff.2 fun x hx ↦ hLS x <| hsK x hx, s.finite_toSet.image _,
        by rwa [sUnion_image], ?_⟩
      rw [mapsTo_sUnion, forall_mem_image]
      exact fun x hx ↦ hLt x <| hsK x hx
    have hsub : (⋂ L ∈ s, {g : C(X, Y) | MapsTo g L (⋃₀ t)}) ⊆ {g | MapsTo g K U} := by
      simp only [← setOf_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
      exact fun g hg ↦ hg.mono hKs (sUnion_subset hTU)
    refine mem_of_superset ((biInter_mem hsf).2 fun L hL ↦ ?_) hsub
    refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_principal_self _
    exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩

instance instSecondCountableTopology
    [SecondCountableTopology X] [LocallyCompactPair X Y] [R1Space X]
    [SecondCountableTopology Y] : SecondCountableTopology C(X, Y) where
  is_open_generated_countable := by
    set S := (closure '' countableBasis X) ∩ {K | IsCompact K}
    refine ⟨_, ?_, compactOpen_eq_generateFrom (S := S) ?_ (isBasis_countableBasis _) ?_⟩
    · refine .image2 (((countable_countableBasis X).image _).mono inter_subset_left) ?_ _
      exact countable_setOf_finite_subset (countable_countableBasis Y)
    · exact fun K ↦ And.right
    · intro f x V hV
      rcases exists_mem_nhds_isCompact_mapsTo (map_continuous f) (interior_mem_nhds.2 hV)
        with ⟨K, hKx, hKc, hKV⟩
      rcases (isBasis_countableBasis X).mem_nhds_iff.mp hKx with ⟨s, hs, hxs, hsK⟩
      refine ⟨closure s, ⟨mem_image_of_mem _ hs, ?_⟩, ?_, ?_⟩
      · exact hKc.closure_of_subset hsK
      · exact mem_of_superset ((isBasis_countableBasis X).mem_nhds hs hxs) subset_closure
      · suffices MapsTo f (closure K) (interior V) from
          this.mono (closure_mono hsK) interior_subset
        exact hKc.closure_subset_of_isOpen (isOpen_interior.preimage (map_continuous f)) hKV

end ContinuousMap

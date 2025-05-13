/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

/-!
# Results on subbases of topological spaces

In this file, we prove results when some topology is given a subbasis.

## Main results

* `alexander_subbasis hTS`. If `X` has a topology `T` and `hTS : T = generateFrom S`, then `X` is
  compact if any open cover of `X` with elements in `S` has a finite subcover.
-/

open TopologicalSpace

variable {X : Type*} [T : TopologicalSpace X] {S : Set (Set X)}

lemma TopologicalSpace.exists_subset_finte_of_mem_nhds_of_subbasis
    (hTS : T = generateFrom S) {x : X} {n : Set X} (hnx : n ∈ nhds x) :
    ∃ U ⊆ S, U.Finite ∧ x ∈ ⋂₀ U ∧ ⋂₀ U ⊆ n := by
  obtain ⟨s, hs, hxs, hsn⟩ := (IsTopologicalBasis.mem_nhds_iff <|
    isTopologicalBasis_of_subbasis hTS).1 hnx
  obtain ⟨V, ⟨hV, hVS⟩, hVs⟩ := (Set.mem_image _ _ _).1 hs
  refine ⟨V, hVS, hV, ?_⟩
  · rw [hVs]
    exact ⟨hxs, hsn⟩

lemma Filter.exists_mem_not_mem_of_not_le_nhds_of_subbasis
    (hTS : T = generateFrom S) {F : Filter X} {x : X} (hFx : ¬F ≤ nhds x) :
    ∃ s ∈ S, x ∈ s ∧ s ∉ F := by
  simp only [Filter.le_def, not_forall] at hFx
  obtain ⟨n, hnx, hnF⟩ := hFx
  obtain ⟨U, hUS, hU, hxU, hUn⟩ := exists_subset_finte_of_mem_nhds_of_subbasis hTS hnx
  have h2 : ⋂₀ U ∉ F := fun hUF => hnF <| F.sets_of_superset hUF hUn
  have h3 : ∃ s ∈ U, s ∉ F := by
    by_contra hUF
    have : U ⊆ F.sets := by simpa only [not_exists, not_and, not_not] using hUF
    exact h2 <| (Filter.sInter_mem hU).2 this
  obtain ⟨s, hsU, hsF⟩ := h3
  exact ⟨s, hUS hsU, hxU s hsU, hsF⟩

/--
The Alexander Subbasis Theorem. If `X` is a topological space with a subbasis `S`, then `X` is
compact if any open cover of `X` with elements in `S` has a finite subcover.
-/
theorem alexander_subbasis (hTS : T = generateFrom S) :
    (∀ P ⊆ S, ⋃₀ P = ⊤ → ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = ⊤) → CompactSpace X := by
  intro h
  rw [← isCompact_univ_iff, isCompact_iff_ultrafilter_le_nhds']
  intro F _
  by_contra hF
  simp only [Set.mem_univ, true_and, not_exists] at hF
  have hSF (x : X) := Filter.exists_mem_not_mem_of_not_le_nhds_of_subbasis hTS (hF x)
  let P := Set.range (fun x : X => (hSF x).choose)
  have hPS : P ⊆ S := Set.range_subset_iff.2 fun x => (hSF x).choose_spec.1
  have hP : ⋃₀ P = ⊤ := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    exact ⟨(hSF x).choose, Set.mem_range_self x, (hSF x).choose_spec.2.1⟩
  obtain ⟨Q, hQP, hQ1, hQ2⟩ := h P hPS hP
  have hQF : ⋂₀ (compl '' Q) ∈ F.sets := by
    refine (Filter.sInter_mem (Set.Finite.image compl hQ1)).2 ?_
    · intro s hsQ
      obtain ⟨r, ⟨x, hxr⟩, hrs⟩ := Set.image_mono hQP hsQ
      rw [← hrs, ← hxr]
      exact Ultrafilter.compl_mem_iff_not_mem.2 (hSF x).choose_spec.2.2
  rw [(Set.compl_sUnion Q).symm.trans (Set.compl_empty_iff.mpr hQ2)] at hQF
  exact Filter.empty_not_mem F.1 hQF

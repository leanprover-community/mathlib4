/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
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

/--
The Alexander Subbasis Theorem. If `X` is a topological space with a subbasis `S`, then `X` is
compact if any open cover of `X` with elements in `S` has a finite subcover.
-/
theorem alexander_subbasis (hTS : T = generateFrom S) :
    (∀ P ⊆ S, ⋃₀ P = .univ → ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = .univ) → CompactSpace X := by
  intro h
  rw [← isCompact_univ_iff, isCompact_iff_ultrafilter_le_nhds']
  intro F _
  by_contra hF
  subst hTS
  have hSF : ∀ (x : X), ∃ s, x ∈ s ∧ s ∈ S ∧ s ∉ F := by simpa [nhds_generateFrom] using hF
  choose U hxU hUS hUF using hSF
  obtain ⟨Q, hQP, hQ1, hQ2⟩ := h (Set.range U) (by simpa [Set.subset_def]) (by aesop)
  have hQF : ⋂₀ (compl '' Q) ∈ F.sets := by
    have : ∀ s ∈ Q, s ∉ F := fun s hsQ ↦ (hQP hsQ).choose_spec ▸ hUF _
    simpa [Filter.biInter_mem hQ1, F.compl_mem_iff_not_mem]
  simp [-Set.sInter_image, ← Set.compl_sUnion, hQ2] at hQF

/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Compactification.OnePoint

#align_import topology.instances.rat_lemmas from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Additional lemmas about the topology on rational numbers

The structure of a metric space on `ℚ` (`Rat.MetricSpace`) is introduced elsewhere, induced from
`ℝ`. In this file we prove some properties of this topological space and its one-point
compactification.

## Main statements

- `Rat.TotallyDisconnectedSpace`: `ℚ` is a totally disconnected space;

- `Rat.not_countably_generated_nhds_infty_opc`: the filter of neighbourhoods of infinity in
  `OnePoint ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `OnePoint ℚ`
-/


open Set Metric Filter TopologicalSpace

open Topology OnePoint

local notation "ℚ∞" => OnePoint ℚ

namespace Rat

variable {p q : ℚ} {s t : Set ℚ}

theorem interior_compact_eq_empty (hs : IsCompact s) : interior s = ∅ :=
  denseEmbedding_coe_real.toDenseInducing.interior_compact_eq_empty dense_irrational hs
#align rat.interior_compact_eq_empty Rat.interior_compact_eq_empty

theorem dense_compl_compact (hs : IsCompact s) : Dense sᶜ :=
  interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)
#align rat.dense_compl_compact Rat.dense_compl_compact

instance cocompact_inf_nhds_neBot : NeBot (cocompact ℚ ⊓ 𝓝 p) := by
  refine' (hasBasis_cocompact.inf (nhds_basis_opens _)).neBot_iff.2 _
  -- ⊢ ∀ {i : Set ℚ × Set ℚ}, IsCompact i.fst ∧ p ∈ i.snd ∧ IsOpen i.snd → Set.None …
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  -- ⊢ Set.Nonempty ((s, o).fstᶜ ∩ (s, o).snd)
                               -- ⊢ Set.Nonempty ((s, o).snd ∩ (s, o).fstᶜ)
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩
  -- 🎉 no goals
#align rat.cocompact_inf_nhds_ne_bot Rat.cocompact_inf_nhds_neBot

theorem not_countably_generated_cocompact : ¬IsCountablyGenerated (cocompact ℚ) := by
  intro H
  -- ⊢ False
  rcases exists_seq_tendsto (cocompact ℚ ⊓ 𝓝 0) with ⟨x, hx⟩
  -- ⊢ False
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  -- ⊢ False
                          -- ⊢ False
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ∉ insert (0 : ℚ) (range x)
  -- ⊢ ∃ n, ¬x n ∈ insert 0 (range x)
  exact (hxc.eventually hx0.isCompact_insert_range.compl_mem_cocompact).exists
  -- ⊢ False
  exact hn (Or.inr ⟨n, rfl⟩)
  -- 🎉 no goals
#align rat.not_countably_generated_cocompact Rat.not_countably_generated_cocompact

theorem not_countably_generated_nhds_infty_opc : ¬IsCountablyGenerated (𝓝 (∞ : ℚ∞)) := by
  intro
  -- ⊢ False
  have : IsCountablyGenerated (comap (OnePoint.some : ℚ → ℚ∞) (𝓝 ∞)) := by infer_instance
  -- ⊢ False
  rw [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact] at this
  -- ⊢ False
  exact not_countably_generated_cocompact this
  -- 🎉 no goals
#align rat.not_countably_generated_nhds_infty_alexandroff Rat.not_countably_generated_nhds_infty_opc

theorem not_firstCountableTopology_opc : ¬FirstCountableTopology ℚ∞ := by
  intro
  -- ⊢ False
  exact not_countably_generated_nhds_infty_opc inferInstance
  -- 🎉 no goals
#align rat.not_first_countable_topology_alexandroff Rat.not_firstCountableTopology_opc

theorem not_secondCountableTopology_opc : ¬SecondCountableTopology ℚ∞ := by
  intro
  -- ⊢ False
  exact not_firstCountableTopology_opc inferInstance
  -- 🎉 no goals
#align rat.not_second_countable_topology_alexandroff Rat.not_secondCountableTopology_opc

instance : TotallyDisconnectedSpace ℚ := by
  refine' ⟨fun s hsu hs x hx y hy => _⟩; clear hsu
  -- ⊢ x = y
                                         -- ⊢ x = y
  by_contra' H : x ≠ y
  -- ⊢ False
  wlog hlt : x < y
  -- ⊢ False
  · refine' this s hs y hy x hx H.symm <| H.lt_or_lt.resolve_left hlt <;> assumption
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  -- ⊢ False
  have := hs.image _ continuous_coe_real.continuousOn
  -- ⊢ False
  rw [isPreconnected_iff_ordConnected] at this
  -- ⊢ False
  have : z ∈ Rat.cast '' s :=
    this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩
  exact hz (image_subset_range _ _ this)
  -- 🎉 no goals

end Rat

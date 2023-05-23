/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.instances.rat_lemmas
! leanprover-community/mathlib commit 92ca63f0fb391a9ca5f22d2409a6080e786d99f7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Irrational
import Mathbin.Topology.Instances.Rat
import Mathbin.Topology.Alexandroff

/-!
# Additional lemmas about the topology on rational numbers

The structure of a metric space on `ℚ` (`rat.metric_space`) is introduced elsewhere, induced from
`ℝ`. In this file we prove some properties of this topological space and its one-point
compactification.

## Main statements

- `rat.totally_disconnected_space`: `ℚ` is a totally disconnected space;

- `rat.not_countably_generated_nhds_infty_alexandroff`: the filter of neighbourhoods of infinity in
  `alexandroff ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `alexandroff ℚ`
-/


open Set Metric Filter TopologicalSpace

open Topology Alexandroff

-- mathport name: «exprℚ∞»
local notation "ℚ∞" => Alexandroff ℚ

namespace Rat

variable {p q : ℚ} {s t : Set ℚ}

theorem interior_compact_eq_empty (hs : IsCompact s) : interior s = ∅ :=
  denseEmbedding_coe_real.to_denseInducing.interior_compact_eq_empty dense_irrational hs
#align rat.interior_compact_eq_empty Rat.interior_compact_eq_empty

theorem dense_compl_compact (hs : IsCompact s) : Dense (sᶜ) :=
  interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)
#align rat.dense_compl_compact Rat.dense_compl_compact

instance cocompact_inf_nhds_neBot : NeBot (cocompact ℚ ⊓ 𝓝 p) :=
  by
  refine' (has_basis_cocompact.inf (nhds_basis_opens _)).neBot_iff.2 _
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩
#align rat.cocompact_inf_nhds_ne_bot Rat.cocompact_inf_nhds_neBot

theorem not_countably_generated_cocompact : ¬IsCountablyGenerated (cocompact ℚ) :=
  by
  intro H
  rcases exists_seq_tendsto (cocompact ℚ ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ∉ insert (0 : ℚ) (range x)
  exact (hxc.eventually hx0.is_compact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl⟩)
#align rat.not_countably_generated_cocompact Rat.not_countably_generated_cocompact

theorem not_countably_generated_nhds_infty_alexandroff : ¬IsCountablyGenerated (𝓝 (∞ : ℚ∞)) :=
  by
  intro
  have : is_countably_generated (comap (coe : ℚ → ℚ∞) (𝓝 ∞)) := by infer_instance
  rw [Alexandroff.comap_coe_nhds_infty, coclosed_compact_eq_cocompact] at this
  exact not_countably_generated_cocompact this
#align rat.not_countably_generated_nhds_infty_alexandroff Rat.not_countably_generated_nhds_infty_alexandroff

theorem not_firstCountableTopology_alexandroff : ¬FirstCountableTopology ℚ∞ :=
  by
  intro
  exact not_countably_generated_nhds_infty_alexandroff inferInstance
#align rat.not_first_countable_topology_alexandroff Rat.not_firstCountableTopology_alexandroff

theorem not_secondCountableTopology_alexandroff : ¬SecondCountableTopology ℚ∞ :=
  by
  intro
  exact not_first_countable_topology_alexandroff inferInstance
#align rat.not_second_countable_topology_alexandroff Rat.not_secondCountableTopology_alexandroff

instance : TotallyDisconnectedSpace ℚ :=
  by
  refine' ⟨fun s hsu hs x hx y hy => _⟩; clear hsu
  by_contra' H : x ≠ y
  wlog hlt : x < y
  · exact this s hs y hy x hx H.symm (H.lt_or_lt.resolve_left hlt)
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  have := hs.image coe continuous_coe_real.continuous_on
  rw [isPreconnected_iff_ordConnected] at this
  have : z ∈ coe '' s := this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩
  exact hz (image_subset_range _ _ this)

end Rat


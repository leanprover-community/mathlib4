/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Metrizable.Uniformity

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

variable {p : ℚ} {s : Set ℚ}

theorem interior_compact_eq_empty (hs : IsCompact s) : interior s = ∅ :=
  isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty dense_irrational hs

theorem dense_compl_compact (hs : IsCompact s) : Dense sᶜ :=
  interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)

instance cocompact_inf_nhds_neBot : NeBot (cocompact ℚ ⊓ 𝓝 p) := by
  refine (hasBasis_cocompact.inf (nhds_basis_opens _)).neBot_iff.2 ?_
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩

theorem not_countably_generated_cocompact : ¬IsCountablyGenerated (cocompact ℚ) := by
  intro H
  rcases exists_seq_tendsto (cocompact ℚ ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ∉ insert (0 : ℚ) (range x) :=
    (hxc.eventually hx0.isCompact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl⟩)

theorem not_countably_generated_nhds_infty_opc : ¬IsCountablyGenerated (𝓝 (∞ : ℚ∞)) := by
  intro
  have : IsCountablyGenerated (comap (OnePoint.some : ℚ → ℚ∞) (𝓝 ∞)) := by infer_instance
  rw [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact] at this
  exact not_countably_generated_cocompact this

theorem not_firstCountableTopology_opc : ¬FirstCountableTopology ℚ∞ := by
  intro
  exact not_countably_generated_nhds_infty_opc inferInstance

theorem not_secondCountableTopology_opc : ¬SecondCountableTopology ℚ∞ := by
  intro
  exact not_firstCountableTopology_opc inferInstance

instance : TotallyDisconnectedSpace ℚ := by
  clear p s
  refine ⟨fun s hsu hs x hx y hy => ?_⟩; clear hsu
  by_contra! H : x ≠ y
  wlog hlt : x < y
  · apply this s hs y hy x hx H.symm <| H.lt_or_gt.resolve_left hlt
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  have := hs.image _ continuous_coe_real.continuousOn
  rw [isPreconnected_iff_ordConnected] at this
  have : z ∈ Rat.cast '' s :=
    this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩
  exact hz (image_subset_range _ _ this)

end Rat

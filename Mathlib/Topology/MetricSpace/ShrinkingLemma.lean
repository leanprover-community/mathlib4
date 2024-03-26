/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.ShrinkingLemma

#align_import topology.metric_space.shrinking_lemma from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Shrinking lemma in a proper metric space

In this file we prove a few versions of the shrinking lemma for coverings by balls in a proper
(pseudo) metric space.

## Tags

shrinking lemma, metric space
-/


universe u v

open Set Metric

open Topology

variable {α : Type u} {ι : Type v} [MetricSpace α] [ProperSpace α] {c : ι → α}
variable {x : α} {r : ℝ} {s : Set α}

/-- **Shrinking lemma** for coverings by open balls in a proper metric space. A point-finite open
cover of a closed subset of a proper metric space by open balls can be shrunk to a new cover by
open balls so that each of the new balls has strictly smaller radius than the old one. This version
assumes that `fun x ↦ ball (c i) (r i)` is a locally finite covering and provides a covering
indexed by the same type. -/
theorem exists_subset_iUnion_ball_radius_lt {r : ι → ℝ} (hs : IsClosed s)
    (uf : ∀ x ∈ s, { i | x ∈ ball (c i) (r i) }.Finite) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
    ∃ r' : ι → ℝ, (s ⊆ ⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i < r i := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_lt_subset_ball (hvc i) (hcv i)
  choose r' hlt hsub using this
  exact ⟨r', hsv.trans <| iUnion_mono <| hsub, hlt⟩
#align exists_subset_Union_ball_radius_lt exists_subset_iUnion_ball_radius_lt

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a proper metric space by open balls can be shrunk to a new cover by open balls so that each of
the new balls has strictly smaller radius than the old one. -/
theorem exists_iUnion_ball_eq_radius_lt {r : ι → ℝ} (uf : ∀ x, { i | x ∈ ball (c i) (r i) }.Finite)
    (uU : ⋃ i, ball (c i) (r i) = univ) :
    ∃ r' : ι → ℝ, ⋃ i, ball (c i) (r' i) = univ ∧ ∀ i, r' i < r i :=
  let ⟨r', hU, hv⟩ := exists_subset_iUnion_ball_radius_lt isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩
#align exists_Union_ball_eq_radius_lt exists_iUnion_ball_eq_radius_lt

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a closed subset of a proper metric space by nonempty open balls can be shrunk to a new cover by
nonempty open balls so that each of the new balls has strictly smaller radius than the old one. -/
theorem exists_subset_iUnion_ball_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hs : IsClosed s)
    (uf : ∀ x ∈ s, { i | x ∈ ball (c i) (r i) }.Finite) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
    ∃ r' : ι → ℝ, (s ⊆ ⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i ∈ Ioo 0 (r i) := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i)
  choose r' hlt hsub using this
  exact ⟨r', hsv.trans <| iUnion_mono hsub, hlt⟩
#align exists_subset_Union_ball_radius_pos_lt exists_subset_iUnion_ball_radius_pos_lt

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a proper metric space by nonempty open balls can be shrunk to a new cover by nonempty open balls
so that each of the new balls has strictly smaller radius than the old one. -/
theorem exists_iUnion_ball_eq_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (uf : ∀ x, { i | x ∈ ball (c i) (r i) }.Finite) (uU : ⋃ i, ball (c i) (r i) = univ) :
    ∃ r' : ι → ℝ, ⋃ i, ball (c i) (r' i) = univ ∧ ∀ i, r' i ∈ Ioo 0 (r i) :=
  let ⟨r', hU, hv⟩ :=
    exists_subset_iUnion_ball_radius_pos_lt hr isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩
#align exists_Union_ball_eq_radius_pos_lt exists_iUnion_ball_eq_radius_pos_lt

/-- Let `R : α → ℝ` be a (possibly discontinuous) function on a proper metric space.
Let `s` be a closed set in `α` such that `R` is positive on `s`. Then there exists a collection of
pairs of balls `Metric.ball (c i) (r i)`, `Metric.ball (c i) (r' i)` such that

* all centers belong to `s`;
* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `Metric.ball (c i) (r' i)` is locally finite;
* the balls `Metric.ball (c i) (r i)` cover `s`.

This is a simple corollary of `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`
and `exists_subset_iUnion_ball_radius_pos_lt`. -/
theorem exists_locallyFinite_subset_iUnion_ball_radius_lt (hs : IsClosed s) {R : α → ℝ}
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
      (∀ i, c i ∈ s ∧ 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ s ⊆ ⋃ i, ball (c i) (r i) := by
  have : ∀ x ∈ s, (𝓝 x).HasBasis (fun r : ℝ => 0 < r ∧ r < R x) fun r => ball x r := fun x hx =>
    nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs this with
    ⟨ι, c, r', hr', hsub', hfin⟩
  rcases exists_subset_iUnion_ball_radius_pos_lt (fun i => (hr' i).2.1) hs
      (fun x _ => hfin.point_finite x) hsub' with
    ⟨r, hsub, hlt⟩
  exact ⟨ι, c, r, r', fun i => ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩
#align exists_locally_finite_subset_Union_ball_radius_lt exists_locallyFinite_subset_iUnion_ball_radius_lt

/-- Let `R : α → ℝ` be a (possibly discontinuous) positive function on a proper metric space. Then
there exists a collection of pairs of balls `Metric.ball (c i) (r i)`, `Metric.ball (c i) (r' i)`
such that

* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `Metric.ball (c i) (r' i)` is locally finite;
* the balls `Metric.ball (c i) (r i)` cover the whole space.

This is a simple corollary of `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`
and `exists_iUnion_ball_eq_radius_pos_lt` or `exists_locallyFinite_subset_iUnion_ball_radius_lt`. -/
theorem exists_locallyFinite_iUnion_eq_ball_radius_lt {R : α → ℝ} (hR : ∀ x, 0 < R x) :
    ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
      (∀ i, 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ ⋃ i, ball (c i) (r i) = univ :=
  let ⟨ι, c, r, r', hlt, hfin, hsub⟩ :=
    exists_locallyFinite_subset_iUnion_ball_radius_lt isClosed_univ fun x _ => hR x
  ⟨ι, c, r, r', fun i => (hlt i).2, hfin, univ_subset_iff.1 hsub⟩
#align exists_locally_finite_Union_eq_ball_radius_lt exists_locallyFinite_iUnion_eq_ball_radius_lt

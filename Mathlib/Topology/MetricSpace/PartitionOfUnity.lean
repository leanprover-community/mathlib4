/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.partition_of_unity
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.EmetricParacompact
import Mathbin.Analysis.Convex.PartitionOfUnity

/-!
# Lemmas about (e)metric spaces that need partition of unity

The main lemma in this file (see `metric.exists_continuous_real_forall_closed_ball_subset`) says the
following. Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets,
let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, → ℝ)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. We also formulate versions of this lemma for extended metric
spaces and for different codomains (`ℝ`, `ℝ≥0`, and `ℝ≥0∞`).

We also prove a few auxiliary lemmas to be used later in a proof of the smooth version of this
lemma.

## Tags

metric space, partition of unity, locally finite
-/


open Topology ENNReal BigOperators NNReal Filter

open Set Function Filter TopologicalSpace

variable {ι X : Type _}

namespace Emetric

variable [EMetricSpace X] {K : ι → Set X} {U : ι → Set X}

/-- Let `K : ι → set X` be a locally finitie family of closed sets in an emetric space. Let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then for any point
`x : X`, for sufficiently small `r : ℝ≥0∞` and for `y` sufficiently close to `x`, for all `i`, if
`y ∈ K i`, then `emetric.closed_ball y r ⊆ U i`. -/
theorem eventually_nhds_zero_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ᶠ 𝓝 x, ∀ i, p.2 ∈ K i → closedBall p.2 p.1 ⊆ U i :=
  by
  suffices ∀ i, x ∈ K i → ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ᶠ 𝓝 x, closed_ball p.2 p.1 ⊆ U i
    by
    filter_upwards [tendsto_snd (hfin.Inter_compl_mem_nhds hK x),
      (eventually_all_finite (hfin.point_finite x)).2 this]
    rintro ⟨r, y⟩ hxy hyU i hi
    simp only [mem_Inter₂, mem_compl_iff, not_imp_not, mem_preimage] at hxy
    exact hyU _ (hxy _ hi)
  intro i hi
  rcases nhds_basis_closed_eball.mem_iff.1 ((hU i).mem_nhds <| hKU i hi) with ⟨R, hR₀, hR⟩
  rcases ennreal.lt_iff_exists_nnreal_btwn.mp hR₀ with ⟨r, hr₀, hrR⟩
  filter_upwards [prod_mem_prod (eventually_lt_nhds hr₀)
      (closed_ball_mem_nhds x (tsub_pos_iff_lt.2 hrR))]with p hp z hz
  apply hR
  calc
    edist z x ≤ edist z p.2 + edist p.2 x := edist_triangle _ _ _
    _ ≤ p.1 + (R - p.1) := (add_le_add hz <| le_trans hp.2 <| tsub_le_tsub_left hp.1.out.le _)
    _ = R := add_tsub_cancel_of_le (lt_trans hp.1 hrR).le
    
#align emetric.eventually_nhds_zero_forall_closed_ball_subset Emetric.eventually_nhds_zero_forall_closedBall_subset

theorem exists_forall_closedBall_subset_aux₁ (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∃ r : ℝ,
      ∀ᶠ y in 𝓝 x,
        r ∈ Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (hi : y ∈ K i), { r | closedBall y r ⊆ U i } :=
  by
  have :=
    (ennreal.continuous_of_real.tendsto' 0 0 ENNReal.ofReal_zero).Eventually
      (eventually_nhds_zero_forall_closed_ball_subset hK hU hKU hfin x).curry
  rcases this.exists_gt with ⟨r, hr0, hr⟩
  refine' ⟨r, hr.mono fun y hy => ⟨hr0, _⟩⟩
  rwa [mem_preimage, mem_Inter₂]
#align emetric.exists_forall_closed_ball_subset_aux₁ Emetric.exists_forall_closedBall_subset_aux₁

theorem exists_forall_closedBall_subset_aux₂ (y : X) :
    Convex ℝ
      (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (hi : y ∈ K i), { r | closedBall y r ⊆ U i }) :=
  (convex_Ioi _).inter <|
    OrdConnected.convex <|
      OrdConnected.preimage_ennreal_ofReal <|
        ordConnected_interᵢ fun i =>
          ordConnected_interᵢ fun hi => ordConnected_setOf_closedBall_subset y (U i)
#align emetric.exists_forall_closed_ball_subset_aux₂ Emetric.exists_forall_closedBall_subset_aux₂

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (ennreal.of_real (δ x)) ⊆ U i`. -/
theorem exists_continuous_real_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (ENNReal.ofReal <| δ x) ⊆ U i :=
  by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_Inter, @forall_swap ι X] using
    exists_continuous_forall_mem_convex_of_local_const exists_forall_closed_ball_subset_aux₂
      (exists_forall_closed_ball_subset_aux₁ hK hU hKU hfin)
#align emetric.exists_continuous_real_forall_closed_ball_subset Emetric.exists_continuous_real_forall_closedBall_subset

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_nNReal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  by
  rcases exists_continuous_real_forall_closed_ball_subset hK hU hKU hfin with ⟨δ, hδ₀, hδ⟩
  lift δ to C(X, ℝ≥0) using fun x => (hδ₀ x).le
  refine' ⟨δ, hδ₀, fun i x hi => _⟩
  simpa only [← ENNReal.ofReal_coe_nnreal] using hδ i x hi
#align emetric.exists_continuous_nnreal_forall_closed_ball_subset Emetric.exists_continuous_nNReal_forall_closedBall_subset

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0∞)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_eNNReal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0∞), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nNReal_forall_closedBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨coe, ENNReal.continuous_coe⟩ δ, fun x => ENNReal.coe_pos.2 (hδ₀ x), hδ⟩
#align emetric.exists_continuous_ennreal_forall_closed_ball_subset Emetric.exists_continuous_eNNReal_forall_closedBall_subset

end Emetric

namespace Metric

variable [MetricSpace X] {K : ι → Set X} {U : ι → Set X}

/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_nNReal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  by
  rcases Emetric.exists_continuous_nNReal_forall_closedBall_subset hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine' ⟨δ, hδ0, fun i x hx => _⟩
  rw [← emetric_closed_ball_nnreal]
  exact hδ i x hx
#align metric.exists_continuous_nnreal_forall_closed_ball_subset Metric.exists_continuous_nNReal_forall_closedBall_subset

/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_real_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nNReal_forall_closedBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨coe, NNReal.continuous_coe⟩ δ, hδ₀, hδ⟩
#align metric.exists_continuous_real_forall_closed_ball_subset Metric.exists_continuous_real_forall_closedBall_subset

end Metric


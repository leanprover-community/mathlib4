/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight

/-!
# Lemmas about (e)metric spaces that need partition of unity

The main lemma in this file (see `Metric.exists_continuous_real_forall_closedBall_subset`) says the
following. Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of closed sets,
let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`Metric.closedBall x (δ x) ⊆ U i`. We also formulate versions of this lemma for extended metric
spaces and for different codomains (`ℝ`, `ℝ≥0`, and `ℝ≥0∞`).

We also prove a few auxiliary lemmas to be used later in a proof of the smooth version of this
lemma.

## Tags

metric space, partition of unity, locally finite
-/

public section

open Topology ENNReal NNReal Filter Set Function TopologicalSpace Metric

variable {ι X : Type*}

namespace Metric

variable [EMetricSpace X] {K : ι → Set X} {U : ι → Set X}

/-- Let `K : ι → Set X` be a locally finite family of closed sets in an emetric space. Let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then for any point
`x : X`, for sufficiently small `r : ℝ≥0∞` and for `y` sufficiently close to `x`, for all `i`, if
`y ∈ K i`, then `Metric.closedEBall y r ⊆ U i`. -/
theorem eventually_nhds_zero_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ˢ 𝓝 x, ∀ i, p.2 ∈ K i → closedEBall p.2 p.1 ⊆ U i := by
  suffices ∀ i, x ∈ K i → ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ˢ 𝓝 x, closedEBall p.2 p.1 ⊆ U i by
    apply mp_mem ((eventually_all_finite (hfin.point_finite x)).2 this)
      (mp_mem (@tendsto_snd ℝ≥0∞ _ (𝓝 0) _ _ (hfin.iInter_compl_mem_nhds hK x)) _)
    apply univ_mem'
    rintro ⟨r, y⟩ hxy hyU i hi
    simp only [mem_iInter, mem_compl_iff, not_imp_not, mem_preimage] at hxy
    exact hyU _ (hxy _ hi)
  intro i hi
  rcases nhds_basis_closedEBall.mem_iff.1 ((hU i).mem_nhds <| hKU i hi) with ⟨R, hR₀, hR⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hR₀ with ⟨r, hr₀, hrR⟩
  filter_upwards [prod_mem_prod (eventually_lt_nhds hr₀)
      (closedEBall_mem_nhds x (tsub_pos_iff_lt.2 hrR))] with p hp z hz
  apply hR
  calc
    edist z x ≤ edist z p.2 + edist p.2 x := edist_triangle _ _ _
    _ ≤ p.1 + (R - p.1) := add_le_add hz <| le_trans hp.2 <| tsub_le_tsub_left hp.1.out.le _
    _ = R := add_tsub_cancel_of_le (lt_trans (by exact hp.1) hrR).le

/-- Auxiliary lemma for `exists_continuous_real_forall_closedEBall_subset`
and its smooth counterpart. -/
theorem exists_forall_closedEBall_subset_aux₁ (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∃ r : ℝ, ∀ᶠ y in 𝓝 x,
      r ∈ Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (_ : y ∈ K i), { r | closedEBall y r ⊆ U i } := by
  have := (ENNReal.continuous_ofReal.tendsto' 0 0 ENNReal.ofReal_zero).eventually
    (eventually_nhds_zero_forall_closedEBall_subset hK hU hKU hfin x).curry
  rcases this.exists_gt with ⟨r, hr0, hr⟩
  refine ⟨r, hr.mono fun y hy => ⟨hr0, ?_⟩⟩
  rwa [mem_preimage, mem_iInter₂]

/-- Auxiliary lemma for `exists_continuous_real_forall_closedEBall_subset`
and its smooth counterpart. -/
theorem exists_forall_closedEBall_subset_aux₂ (y : X) :
    Convex ℝ
      (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (_ : y ∈ K i), { r | closedEBall y r ⊆ U i }) :=
  (convex_Ioi _).inter <| OrdConnected.convex <| OrdConnected.preimage_ennreal_ofReal <|
    ordConnected_iInter fun i => ordConnected_iInter fun (_ : y ∈ K i) =>
      ordConnected_setOf_closedEBall_subset y (U i)

/-- Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite family of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`,
we have `Metric.closedEBall x (ENNReal.ofReal (δ x)) ⊆ U i`. -/
theorem exists_continuous_real_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧
      ∀ (i), ∀ x ∈ K i, closedEBall x (ENNReal.ofReal <| δ x) ⊆ U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_comm ι X] using
    exists_continuous_forall_mem_convex_of_local_const exists_forall_closedEBall_subset_aux₂
      (exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

/-- Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite family of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`,
we have `Metric.closedEBall x (δ x) ⊆ U i`. -/
theorem exists_continuous_nnreal_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedEBall x (δ x) ⊆ U i := by
  rcases exists_continuous_real_forall_closedEBall_subset hK hU hKU hfin with ⟨δ, hδ₀, hδ⟩
  lift δ to C(X, ℝ≥0) using fun x => (hδ₀ x).le
  refine ⟨δ, hδ₀, fun i x hi => ?_⟩
  simpa only [← ENNReal.ofReal_coe_nnreal] using hδ i x hi

/-- Let `X` be an extended metric space. Let `K : ι → Set X` be a locally finite family of closed
sets, let `U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0∞)` such that for any `i` and `x ∈ K i`,
we have `Metric.closedEBall x (δ x) ⊆ U i`. -/
theorem exists_continuous_ennreal_forall_closedEBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0∞), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedEBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nnreal_forall_closedEBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨Coe.coe, ENNReal.continuous_coe⟩ δ, fun x => ENNReal.coe_pos.2 (hδ₀ x), hδ⟩

end Metric

namespace EMetric
open Metric

@[deprecated (since := "2026-01-24")]
alias eventually_nhds_zero_forall_closedBall_subset :=
  eventually_nhds_zero_forall_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias exists_forall_closedBall_subset_aux₁ := exists_forall_closedEBall_subset_aux₁

@[deprecated (since := "2026-01-24")]
alias exists_forall_closedBall_subset_aux₂ := exists_forall_closedEBall_subset_aux₂

@[deprecated (since := "2026-01-24")]
alias exists_continuous_real_forall_closedBall_subset :=
  exists_continuous_real_forall_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias exists_continuous_nnreal_forall_closedBall_subset :=
  exists_continuous_nnreal_forall_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias exists_continuous_eNNReal_forall_closedBall_subset :=
  exists_continuous_ennreal_forall_closedEBall_subset

end EMetric

namespace Metric

variable [MetricSpace X] {K : ι → Set X} {U : ι → Set X}

/-- Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of closed sets, let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`, we have
`Metric.closedBall x (δ x) ⊆ U i`. -/
theorem exists_continuous_nnreal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i := by
  rcases Metric.exists_continuous_nnreal_forall_closedEBall_subset hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_coe]
  exact hδ i x hx

/-- Let `X` be a metric space. Let `K : ι → Set X` be a locally finite family of closed sets, let
`U : ι → Set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`Metric.closedBall x (δ x) ⊆ U i`. -/
theorem exists_continuous_real_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nnreal_forall_closedBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨Coe.coe, NNReal.continuous_coe⟩ δ, hδ₀, hδ⟩

end Metric

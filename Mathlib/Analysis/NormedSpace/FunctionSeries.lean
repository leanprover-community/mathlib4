/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.ENNReal

#align_import analysis.calculus.series from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Continuity of series of functions

We show that series of functions are continuous when each individual function in the series is and
additionally suitable uniform summable bounds are satisfied, in `continuous_tsum`.

For smoothness of series of functions, see the file `Analysis.Calculus.SmoothSeries`.
-/

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with general index set. -/
theorem tendstoUniformlyOn_tsum {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t : Finset α => fun x => ∑ n ∈ t, f n x) (fun x => ∑' n, f n x) atTop
      s := by
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have A : Summable fun n => ‖f n x‖ :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm, ← sum_add_tsum_subtype_compl A.of_norm t, add_sub_cancel_left]
  apply lt_of_le_of_lt _ ht
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  exact tsum_le_tsum (fun n => hfu _ _ hx) (A.subtype _) (hu.subtype _)
#align tendsto_uniformly_on_tsum tendstoUniformlyOn_tsum

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with index set `ℕ`. -/
theorem tendstoUniformlyOn_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun N => fun x => ∑ n ∈ Finset.range N, f n x) (fun x => ∑' n, f n x) atTop
      s :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tsum hu hfu v hv)
#align tendsto_uniformly_on_tsum_nat tendstoUniformlyOn_tsum_nat

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with general index set. -/
theorem tendstoUniformly_tsum {f : α → β → F} (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun t : Finset α => fun x => ∑ n ∈ t, f n x)
      (fun x => ∑' n, f n x) atTop := by
  rw [← tendstoUniformlyOn_univ]; exact tendstoUniformlyOn_tsum hu fun n x _ => hfu n x
#align tendsto_uniformly_tsum tendstoUniformly_tsum

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with index set `ℕ`. -/
theorem tendstoUniformly_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : Summable u)
    (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun N => fun x => ∑ n ∈ Finset.range N, f n x) (fun x => ∑' n, f n x)
      atTop :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformly_tsum hu hfu v hv)
#align tendsto_uniformly_tsum_nat tendstoUniformly_tsum_nat

/-- An infinite sum of functions with summable sup norm is continuous on a set if each individual
function is. -/
theorem continuousOn_tsum [TopologicalSpace β] {f : α → β → F} {s : Set β}
    (hf : ∀ i, ContinuousOn (f i) s) (hu : Summable u) (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    ContinuousOn (fun x => ∑' n, f n x) s := by
  classical
    refine (tendstoUniformlyOn_tsum hu hfu).continuousOn (eventually_of_forall ?_)
    intro t
    exact continuousOn_finset_sum _ fun i _ => hf i
#align continuous_on_tsum continuousOn_tsum

/-- An infinite sum of functions with summable sup norm is continuous if each individual
function is. -/
theorem continuous_tsum [TopologicalSpace β] {f : α → β → F} (hf : ∀ i, Continuous (f i))
    (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) : Continuous fun x => ∑' n, f n x := by
  simp_rw [continuous_iff_continuousOn_univ] at hf ⊢
  exact continuousOn_tsum hf hu fun n x _ => hfu n x
#align continuous_tsum continuous_tsum

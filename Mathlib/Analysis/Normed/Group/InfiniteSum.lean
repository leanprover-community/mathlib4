/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Heather Macbeth, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.UniformSpace.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Infinite sums in (semi)normed groups

In a complete (semi)normed group,

- `summable_iff_vanishing_norm`: a series `∑' i, f i` is summable if and only if for any `ε > 0`,
  there exists a finite set `s` such that the sum `∑ i ∈ t, f i` over any finite set `t` disjoint
  with `s` has norm less than `ε`;

- `Summable.of_norm_bounded`, `Summable.of_norm_bounded_eventually`: if `‖f i‖` is bounded above by
  a summable series `∑' i, g i`, then `∑' i, f i` is summable as well; the same is true if the
  inequality hold only off some finite set.

- `tsum_of_norm_bounded`, `HasSum.norm_le_of_bounded`: if `‖f i‖ ≤ g i`, where `∑' i, g i` is a
  summable series, then `‖∑' i, f i‖ ≤ ∑' i, g i`.

- versions of these lemmas for `nnnorm` and `enorm`.

## Tags

infinite series, absolute convergence, normed group
-/

public section

open Topology ENNReal NNReal

open Finset Filter Metric

variable {ι α E F ε : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [TopologicalSpace ε] [ESeminormedAddCommMonoid ε]

theorem cauchySeq_finset_iff_vanishing_norm {f : ι → E} :
    (CauchySeq fun s : Finset ι => ∑ i ∈ s, f i) ↔
      ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ‖∑ i ∈ t, f i‖ < ε := by
  rw [cauchySeq_finset_iff_sum_vanishing, nhds_basis_ball.forall_iff]
  · simp only [ball_zero_eq, Set.mem_setOf_eq]
  · rintro s t hst ⟨s', hs'⟩
    exact ⟨s', fun t' ht' => hst <| hs' _ ht'⟩

theorem summable_iff_vanishing_norm [CompleteSpace E] {f : ι → E} :
    Summable f ↔ ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ‖∑ i ∈ t, f i‖ < ε := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm]

theorem cauchySeq_finset_of_norm_bounded_eventually {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : CauchySeq fun s => ∑ i ∈ s, f i := by
  refine cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => ?_
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩
  classical
  refine ⟨s ∪ h.toFinset, fun t ht => ?_⟩
  have : ∀ i ∈ t, ‖f i‖ ≤ g i := by
    intro i hi
    simp only [disjoint_left, mem_union, not_or, h.mem_toFinset, Set.mem_compl_iff,
      Classical.not_not] at ht
    exact (ht hi).2
  calc
    ‖∑ i ∈ t, f i‖ ≤ ∑ i ∈ t, g i := norm_sum_le_of_le _ this
    _ ≤ ‖∑ i ∈ t, g i‖ := le_abs_self _
    _ < ε := hs _ (ht.mono_right le_sup_left)

theorem cauchySeq_finset_of_norm_bounded {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ i, ‖f i‖ ≤ g i) : CauchySeq fun s : Finset ι => ∑ i ∈ s, f i :=
  cauchySeq_finset_of_norm_bounded_eventually hg <| Eventually.of_forall h

/-- A version of the **direct comparison test** for conditionally convergent series.
See `cauchySeq_finset_of_norm_bounded` for the same statement about absolutely convergent ones. -/
theorem cauchySeq_range_of_norm_bounded {f : ℕ → E} {g : ℕ → ℝ}
    (hg : CauchySeq fun n => ∑ i ∈ range n, g i) (hf : ∀ i, ‖f i‖ ≤ g i) :
    CauchySeq fun n => ∑ i ∈ range n, f i := by
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  refine (Metric.cauchySeq_iff'.1 hg ε hε).imp fun N hg n hn => ?_
  specialize hg n hn
  rw [dist_eq_norm, ← sum_Ico_eq_sub _ hn] at hg ⊢
  calc
    ‖∑ k ∈ Ico N n, f k‖ ≤ ∑ k ∈ _, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ _, g k := sum_le_sum fun x _ => hf x
    _ ≤ ‖∑ k ∈ _, g k‖ := le_abs_self _
    _ < ε := hg

theorem cauchySeq_finset_of_summable_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) :
    CauchySeq fun s : Finset ι => ∑ a ∈ s, f a :=
  cauchySeq_finset_of_norm_bounded hf fun _i => le_rfl

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
theorem hasSum_of_subseq_of_summable {f : ι → E} (hf : Summable fun a => ‖f a‖) {s : α → Finset ι}
    {p : Filter α} [NeBot p] (hs : Tendsto s p atTop) {a : E}
    (ha : Tendsto (fun b => ∑ i ∈ s b, f i) p (𝓝 a)) : HasSum f a :=
  tendsto_nhds_of_cauchySeq_of_subseq (cauchySeq_finset_of_summable_norm hf) hs ha

theorem hasSum_iff_tendsto_nat_of_summable_norm {f : ℕ → E} {a : E} (hf : Summable fun i => ‖f i‖) :
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i ∈ range n, f i) atTop (𝓝 a) :=
  ⟨fun h => h.tendsto_sum_nat, fun h => hasSum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
theorem Summable.of_norm_bounded [CompleteSpace E] {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ i, ‖f i‖ ≤ g i) : Summable f := by
  rw [summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_of_norm_bounded hg h

theorem HasSum.enorm_le_of_bounded {f : ι → ε} {g : ι → ℝ≥0∞} {a : ε} {b : ℝ≥0∞} (hf : HasSum f a)
    (hg : HasSum g b) (h : ∀ i, ‖f i‖ₑ ≤ g i) : ‖a‖ₑ ≤ b := by
  exact le_of_tendsto_of_tendsto' hf.enorm hg fun _s ↦ enorm_sum_le_of_le _ fun i _hi ↦ h i

theorem HasSum.norm_le_of_bounded {f : ι → E} {g : ι → ℝ} {a : E} {b : ℝ} (hf : HasSum f a)
    (hg : HasSum g b) (h : ∀ i, ‖f i‖ ≤ g i) : ‖a‖ ≤ b := by
  exact le_of_tendsto_of_tendsto' hf.norm hg fun _s ↦ norm_sum_le_of_le _ fun i _hi ↦ h i

/-- Quantitative result associated to the direct comparison test for series:  If, for all `i`,
`‖f i‖ₑ ≤ g i`, then `‖∑' i, f i‖ₑ ≤ ∑' i, g i`. Note that we do not assume that `∑' i, f i` is
summable, and it might not be the case if `α` is not a complete space. -/
theorem tsum_of_enorm_bounded {f : ι → ε} {g : ι → ℝ≥0∞} {a : ℝ≥0∞} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖ₑ ≤ g i) : ‖∑' i : ι, f i‖ₑ ≤ a := by
  by_cases hf : Summable f
  · exact hf.hasSum.enorm_le_of_bounded hg h
  · simp [tsum_eq_zero_of_not_summable hf]

theorem enorm_tsum_le_tsum_enorm {f : ι → ε} :
    ‖∑' i, f i‖ₑ ≤ ∑' i, ‖f i‖ₑ :=
  tsum_of_enorm_bounded ENNReal.summable.hasSum fun _i => le_rfl

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `‖f i‖ ≤ g i`, then `‖∑' i, f i‖ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem tsum_of_norm_bounded {f : ι → E} {g : ι → ℝ} {a : ℝ} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖ ≤ g i) : ‖∑' i : ι, f i‖ ≤ a := by
  by_cases hf : Summable f
  · exact hf.hasSum.norm_le_of_bounded hg h
  · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
    classical exact ge_of_tendsto' hg fun s => sum_nonneg fun i _hi => (norm_nonneg _).trans (h i)

/-- If `∑' i, ‖f i‖` is summable, then `‖∑' i, f i‖ ≤ (∑' i, ‖f i‖)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem norm_tsum_le_tsum_norm {f : ι → E} (hf : Summable fun i => ‖f i‖) :
    ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ :=
  tsum_of_norm_bounded hf.hasSum fun _i => le_rfl

/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `‖f i‖₊ ≤ g i`, then `‖∑' i, f i‖₊ ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
theorem tsum_of_nnnorm_bounded {f : ι → E} {g : ι → ℝ≥0} {a : ℝ≥0} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖₊ ≤ g i) : ‖∑' i : ι, f i‖₊ ≤ a := by
  simp only [← NNReal.coe_le_coe, ← NNReal.hasSum_coe, coe_nnnorm] at *
  exact tsum_of_norm_bounded hg h

/-- If `∑' i, ‖f i‖₊` is summable, then `‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
theorem nnnorm_tsum_le {f : ι → E} (hf : Summable fun i => ‖f i‖₊) : ‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊ :=
  tsum_of_nnnorm_bounded hf.hasSum fun _i => le_rfl

variable [CompleteSpace E]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
theorem Summable.of_norm_bounded_eventually {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : Summable f :=
  summable_iff_cauchySeq_finset.2 <| cauchySeq_finset_of_norm_bounded_eventually hg h

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
theorem Summable.of_norm_bounded_eventually_nat {f : ℕ → E} {g : ℕ → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in atTop, ‖f i‖ ≤ g i) : Summable f :=
  .of_norm_bounded_eventually hg <| Nat.cofinite_eq_atTop ▸ h

theorem Summable.of_nnnorm_bounded {f : ι → E} {g : ι → ℝ≥0} (hg : Summable g)
    (h : ∀ i, ‖f i‖₊ ≤ g i) : Summable f :=
  .of_norm_bounded (NNReal.summable_coe.2 hg) h

theorem Summable.of_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) : Summable f :=
  .of_norm_bounded hf fun _i => le_rfl

theorem Summable.of_nnnorm {f : ι → E} (hf : Summable fun a => ‖f a‖₊) : Summable f :=
  .of_nnnorm_bounded hf fun _i => le_rfl

/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Disjoint
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Closure
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point of `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This file introduces:
* `Metric.infEDist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Metric.hausdorffEDist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `Metric.infDist`
  and `Metric.hausdorffDist`

## Main results
* `infEDist_closure`: the edistance to a set and its closure coincide
* `Metric.mem_closure_iff_infEDist_zero`: a point `x` belongs to the closure of `s` iff
  `infEDist x s = 0`
* `IsCompact.exists_infEDist_eq_edist`: if `s` is compact and non-empty, there exists a point `y`
  which attains this edistance
* `IsOpen.exists_iUnion_isClosed`: every open set `U` can be written as the increasing union
  of countably many closed subsets of `U`

* `hausdorffEDist_closure`: replacing a set by its closure does not change the Hausdorff edistance
* `hausdorffEDist_zero_iff_closure_eq_closure`: two sets have Hausdorff edistance zero
  iff their closures coincide
* the Hausdorff edistance is symmetric and satisfies the triangle inequality
* in particular, closed sets in an emetric space are an emetric space
  (this is shown in `EMetricSpace.Closeds.emetricSpace`)

* versions of these notions on metric spaces
* `hausdorffEDist_ne_top_of_nonempty_of_bounded`: if two sets in a metric space
  are nonempty and bounded in a metric space, they are at finite Hausdorff edistance.

## Tags
metric space, Hausdorff distance
-/

@[expose] public section


noncomputable section

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

namespace Metric

section InfEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/

/-- The minimal edistance of a point to a set -/
def infEDist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y

@[simp]
theorem infEDist_empty : infEDist x ∅ = ∞ :=
  iInf_emptyset

theorem le_infEDist {d} : d ≤ infEDist x s ↔ ∀ y ∈ s, d ≤ edist x y := by
  simp only [infEDist, le_iInf_iff]

/-- The edist to a union is the minimum of the edists -/
@[simp]
theorem infEDist_union : infEDist x (s ∪ t) = infEDist x s ⊓ infEDist x t :=
  iInf_union

@[simp]
theorem infEDist_iUnion (f : ι → Set α) (x : α) : infEDist x (⋃ i, f i) = ⨅ i, infEDist x (f i) :=
  iInf_iUnion f _

lemma infEDist_biUnion {ι : Type*} (f : ι → Set α) (I : Set ι) (x : α) :
    infEDist x (⋃ i ∈ I, f i) = ⨅ i ∈ I, infEDist x (f i) := by simp only [infEDist_iUnion]

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
theorem infEDist_singleton : infEDist x {y} = edist x y :=
  iInf_singleton

/-- The edist to a set is bounded above by the edist to any of its points -/
theorem infEDist_le_edist_of_mem (h : y ∈ s) : infEDist x s ≤ edist x y :=
  iInf₂_le y h

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
theorem infEDist_zero_of_mem (h : x ∈ s) : infEDist x s = 0 :=
  nonpos_iff_eq_zero.1 <| @edist_self _ _ x ▸ infEDist_le_edist_of_mem h

/-- The edist is antitone with respect to inclusion. -/
@[gcongr]
theorem infEDist_anti (h : s ⊆ t) : infEDist x t ≤ infEDist x s :=
  iInf_le_iInf_of_subset h

/-- The edist to a set is `< r` iff there exists a point in the set at edistance `< r` -/
theorem infEDist_lt_iff {r : ℝ≥0∞} : infEDist x s < r ↔ ∃ y ∈ s, edist x y < r := by
  simp_rw [infEDist, iInf_lt_iff, exists_prop]

/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
theorem infEDist_le_infEDist_add_edist : infEDist x s ≤ infEDist y s + edist x y :=
  calc
    ⨅ z ∈ s, edist x z ≤ ⨅ z ∈ s, edist y z + edist x y :=
      iInf₂_mono fun _ _ => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z ∈ s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]

theorem infEDist_le_edist_add_infEDist : infEDist x s ≤ edist x y + infEDist y s := by
  rw [add_comm]
  exact infEDist_le_infEDist_add_edist

theorem edist_le_infEDist_add_ediam (hy : y ∈ s) : edist x y ≤ infEDist x s + Metric.ediam s := by
  simp_rw [infEDist, ENNReal.iInf_add]
  refine le_iInf₂ fun i hi => ?_
  calc
    edist x y ≤ edist x i + edist i y := edist_triangle _ _ _
    _ ≤ edist x i + Metric.ediam s := add_le_add le_rfl (Metric.edist_le_ediam_of_mem hi hy)

/-- The edist to a set depends continuously on the point -/
@[continuity, fun_prop]
theorem continuous_infEDist : Continuous fun x => infEDist x s :=
  continuous_of_le_add_edist 1 (by simp) <| by
    simp only [one_mul, infEDist_le_infEDist_add_edist, forall₂_true_iff]

/-- The edist to a set and to its closure coincide -/
theorem infEDist_closure : infEDist x (closure s) = infEDist x s := by
  refine le_antisymm (infEDist_anti subset_closure) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_
  have ε0 : 0 < (ε / 2 : ℝ≥0∞) := by simpa [pos_iff_ne_zero] using εpos
  have : infEDist x (closure s) < infEDist x (closure s) + ε / 2 :=
    ENNReal.lt_add_right h.ne ε0.ne'
  obtain ⟨y : α, ycs : y ∈ closure s, hy : edist x y < infEDist x (closure s) + ↑ε / 2⟩ :=
    infEDist_lt_iff.mp this
  obtain ⟨z : α, zs : z ∈ s, dyz : edist y z < ↑ε / 2⟩ := EMetric.mem_closure_iff.1 ycs (ε / 2) ε0
  calc
    infEDist x s ≤ edist x z := infEDist_le_edist_of_mem zs
    _ ≤ edist x y + edist y z := edist_triangle _ _ _
    _ ≤ infEDist x (closure s) + ε / 2 + ε / 2 := add_le_add (le_of_lt hy) (le_of_lt dyz)
    _ = infEDist x (closure s) + ↑ε := by rw [add_assoc, ENNReal.add_halves]

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
theorem mem_closure_iff_infEDist_zero : x ∈ closure s ↔ infEDist x s = 0 :=
  ⟨fun h => by
    rw [← infEDist_closure]
    exact infEDist_zero_of_mem h,
   fun h =>
    EMetric.mem_closure_iff.2 fun ε εpos => infEDist_lt_iff.mp <| by rwa [h]⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
theorem mem_iff_infEDist_zero_of_closed (h : IsClosed s) : x ∈ s ↔ infEDist x s = 0 := by
  rw [← mem_closure_iff_infEDist_zero, h.closure_eq]

/-- The infimum edistance of a point to a set is positive if and only if the point is not in the
closure of the set. -/
theorem infEDist_pos_iff_notMem_closure {x : α} {E : Set α} :
    0 < infEDist x E ↔ x ∉ closure E := by
  rw [mem_closure_iff_infEDist_zero, pos_iff_ne_zero]

theorem infEDist_closure_pos_iff_notMem_closure {x : α} {E : Set α} :
    0 < infEDist x (closure E) ↔ x ∉ closure E := by
  rw [infEDist_closure, infEDist_pos_iff_notMem_closure]

theorem exists_real_pos_lt_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉ closure E) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < infEDist x E := by
  rw [← infEDist_pos_iff_notMem_closure, ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ENNReal.ofReal_pos.mp ε_pos, ε_lt⟩⟩

theorem disjoint_closedEBall_of_lt_infEDist {r : ℝ≥0∞} (h : r < infEDist x s) :
    Disjoint (Metric.closedEBall x r) s := by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irrefl (infEDist x s)
  calc
    infEDist x s ≤ edist x y := infEDist_le_edist_of_mem h'y
    _ ≤ r := by rwa [Metric.mem_closedEBall, edist_comm] at hy
    _ < infEDist x s := h

/-- The infimum edistance is invariant under isometries -/
theorem infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x) (Φ '' t) = infEDist x t := by
  simp only [infEDist, iInf_image, hΦ.edist_eq]

@[to_additive (attr := simp)]
theorem infEDist_smul {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α) :
    infEDist (c • x) (c • s) = infEDist x s :=
  infEDist_image (isometry_smul _ _)

theorem _root_.IsOpen.exists_iUnion_isClosed {U : Set α} (hU : IsOpen U) :
    ∃ F : ℕ → Set α, (∀ n, IsClosed (F n)) ∧ (∀ n, F n ⊆ U) ∧ ⋃ n, F n = U ∧ Monotone F := by
  obtain ⟨a, a_pos, a_lt_one⟩ : ∃ a : ℝ≥0∞, 0 < a ∧ a < 1 := exists_between zero_lt_one
  let F := fun n : ℕ => (fun x => infEDist x Uᶜ) ⁻¹' Ici (a ^ n)
  have F_subset : ∀ n, F n ⊆ U := fun n x hx ↦ by
    by_contra h
    have : infEDist x Uᶜ ≠ 0 := ((ENNReal.pow_pos a_pos _).trans_le hx).ne'
    exact this (infEDist_zero_of_mem h)
  refine ⟨F, fun n => IsClosed.preimage continuous_infEDist isClosed_Ici, F_subset, ?_, ?_⟩
  · show ⋃ n, F n = U
    refine Subset.antisymm (by simp only [iUnion_subset_iff, F_subset, forall_const]) fun x hx => ?_
    have : x ∉ Uᶜ := by simpa using hx
    rw [mem_iff_infEDist_zero_of_closed hU.isClosed_compl] at this
    have B : 0 < infEDist x Uᶜ := by simpa [pos_iff_ne_zero] using this
    have : Filter.Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one a_lt_one
    rcases ((tendsto_order.1 this).2 _ B).exists with ⟨n, hn⟩
    simp only [mem_iUnion]
    exact ⟨n, hn.le⟩
  show Monotone F
  intro m n hmn x hx
  simp only [F, mem_Ici, mem_preimage] at hx ⊢
  apply le_trans (pow_le_pow_right_of_le_one' a_lt_one.le hmn) hx

theorem _root_.IsCompact.exists_infEDist_eq_edist (hs : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infEDist x s = edist x y := by
  have A : Continuous fun y => edist x y := by fun_prop
  obtain ⟨y, ys, hy⟩ := hs.exists_isMinOn hne A.continuousOn
  exact ⟨y, ys, le_antisymm (infEDist_le_edist_of_mem ys) (by rwa [le_infEDist])⟩

theorem exists_pos_forall_lt_edist (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ t, (r : ℝ≥0∞) < edist x y := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · use 1
    simp
  obtain ⟨x, hx, h⟩ := hs.exists_isMinOn hne continuous_infEDist.continuousOn
  have : 0 < infEDist x t :=
    pos_iff_ne_zero.2 fun H => hst.le_bot ⟨hx, (mem_iff_infEDist_zero_of_closed ht).mpr H⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 this with ⟨r, h₀, hr⟩
  exact ⟨r, ENNReal.coe_pos.mp h₀, fun y hy z hz => hr.trans_le <| le_infEDist.1 (h hy) z hz⟩

theorem infEDist_prod (x : α × β) (s : Set α) (t : Set β) :
    infEDist x (s ×ˢ t) = max (infEDist x.1 s) (infEDist x.2 t) := by
  simp_rw +singlePass [infEDist, Prod.edist_eq, iInf_prod, Set.mem_prod, iInf_and, iInf_sup_eq,
    sup_iInf_eq, iInf_sup_eq, sup_iInf_eq]

end InfEDist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/

/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
irreducible_def hausdorffEDist {α : Type u} [PseudoEMetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆ x ∈ s, infEDist x t) ⊔ ⨆ y ∈ t, infEDist y s

section HausdorffEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t u : Set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes. -/
@[simp]
theorem hausdorffEDist_self : hausdorffEDist s s = 0 := by
  simp only [hausdorffEDist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEDist_zero_of_mem hx

/-- The Hausdorff edistances of `s` to `t` and of `t` to `s` coincide. -/
theorem hausdorffEDist_comm : hausdorffEDist s t = hausdorffEDist t s := by
  simp only [hausdorffEDist_def]; apply sup_comm

/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
theorem hausdorffEDist_le_of_infEDist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, infEDist x t ≤ r)
    (H2 : ∀ x ∈ t, infEDist x s ≤ r) : hausdorffEDist s t ≤ r := by
  simp only [hausdorffEDist_def, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem hausdorffEDist_le_of_mem_edist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, ∃ y ∈ t, edist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, edist x y ≤ r) : hausdorffEDist s t ≤ r := by
  refine hausdorffEDist_le_of_infEDist (fun x xs ↦ ?_) (fun x xt ↦ ?_)
  · rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infEDist_le_edist_of_mem yt) hy
  · rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infEDist_le_edist_of_mem ys) hy

/-- The distance to a set is controlled by the Hausdorff distance. -/
theorem infEDist_le_hausdorffEDist_of_mem (h : x ∈ s) : infEDist x t ≤ hausdorffEDist s t := by
  rw [hausdorffEDist_def]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂ (α := ℝ≥0∞) x h

/-- If the Hausdorff distance is `< r`, then any point in one of the sets has
a corresponding point at distance `< r` in the other set. -/
theorem exists_edist_lt_of_hausdorffEDist_lt {r : ℝ≥0∞} (h : x ∈ s) (H : hausdorffEDist s t < r) :
    ∃ y ∈ t, edist x y < r :=
  infEDist_lt_iff.mp <|
    calc
      infEDist x t ≤ hausdorffEDist s t := infEDist_le_hausdorffEDist_of_mem h
      _ < r := H

/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t`. -/
theorem infEDist_le_infEDist_add_hausdorffEDist :
    infEDist x t ≤ infEDist x s + hausdorffEDist s t :=
  ENNReal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : ℝ≥0∞) ≠ 0 := by simpa [pos_iff_ne_zero] using εpos
    have : infEDist x s < infEDist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.ne ε0
    obtain ⟨y : α, ys : y ∈ s, dxy : edist x y < infEDist x s + ↑ε / 2⟩ := infEDist_lt_iff.mp this
    have : hausdorffEDist s t < hausdorffEDist s t + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).2.ne ε0
    obtain ⟨z : α, zt : z ∈ t, dyz : edist y z < hausdorffEDist s t + ↑ε / 2⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt ys this
    calc
      infEDist x t ≤ edist x z := infEDist_le_edist_of_mem zt
      _ ≤ edist x y + edist y z := edist_triangle _ _ _
      _ ≤ infEDist x s + ε / 2 + (hausdorffEDist s t + ε / 2) := add_le_add dxy.le dyz.le
      _ = infEDist x s + hausdorffEDist s t + ε := by
        rw [add_add_add_comm, ENNReal.add_halves]

/-- The Hausdorff edistance is invariant under isometries. -/
theorem hausdorffEDist_image (h : Isometry Φ) :
    hausdorffEDist (Φ '' s) (Φ '' t) = hausdorffEDist s t := by
  simp only [hausdorffEDist_def, iSup_image, infEDist_image h]

/-- The Hausdorff distance is controlled by the diameter of the union. -/
theorem hausdorffEDist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) :
    hausdorffEDist s t ≤ Metric.ediam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro z hz
    exact ⟨y, yt, Metric.edist_le_ediam_of_mem (subset_union_left hz) (subset_union_right yt)⟩
  · intro z hz
    exact ⟨x, xs, Metric.edist_le_ediam_of_mem (subset_union_right hz) (subset_union_left xs)⟩

/-- The Hausdorff distance satisfies the triangle inequality. -/
theorem hausdorffEDist_triangle : hausdorffEDist s u ≤ hausdorffEDist s t + hausdorffEDist t u := by
  rw [hausdorffEDist_def]
  simp only [sup_le_iff, iSup_le_iff]
  constructor
  · change ∀ x ∈ s, infEDist x u ≤ hausdorffEDist s t + hausdorffEDist t u
    exact fun x xs =>
      calc
        infEDist x u ≤ infEDist x t + hausdorffEDist t u :=
          infEDist_le_infEDist_add_hausdorffEDist
        _ ≤ hausdorffEDist s t + hausdorffEDist t u := by grw [infEDist_le_hausdorffEDist_of_mem xs]
  · change ∀ x ∈ u, infEDist x s ≤ hausdorffEDist s t + hausdorffEDist t u
    exact fun x xu =>
      calc
        infEDist x s ≤ infEDist x t + hausdorffEDist t s :=
          infEDist_le_infEDist_add_hausdorffEDist
        _ ≤ hausdorffEDist u t + hausdorffEDist t s := by grw [infEDist_le_hausdorffEDist_of_mem xu]
        _ = hausdorffEDist s t + hausdorffEDist t u := by simp [hausdorffEDist_comm, add_comm]

/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure. -/
theorem hausdorffEDist_zero_iff_closure_eq_closure :
    hausdorffEDist s t = 0 ↔ closure s = closure t := by
  simp only [hausdorffEDist_def, ENNReal.max_eq_zero_iff, ENNReal.iSup_eq_zero, ← subset_def,
    ← mem_closure_iff_infEDist_zero, subset_antisymm_iff, isClosed_closure.closure_subset_iff]

/-- The Hausdorff edistance between a set and its closure vanishes. -/
@[simp]
theorem hausdorffEDist_self_closure : hausdorffEDist s (closure s) = 0 := by
  rw [hausdorffEDist_zero_iff_closure_eq_closure, closure_closure]

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem hausdorffEDist_closure_left : hausdorffEDist (closure s) t = hausdorffEDist s t := by
  refine le_antisymm ?_ ?_
  · calc
      _ ≤ hausdorffEDist (closure s) s + hausdorffEDist s t := hausdorffEDist_triangle
      _ = hausdorffEDist s t := by simp [hausdorffEDist_comm]
  · calc
      _ ≤ hausdorffEDist s (closure s) + hausdorffEDist (closure s) t := hausdorffEDist_triangle
      _ = hausdorffEDist (closure s) t := by simp

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem hausdorffEDist_closure_right : hausdorffEDist s (closure t) = hausdorffEDist s t := by
  simp [@hausdorffEDist_comm _ _ s _]

/-- The Hausdorff edistance between sets or their closures is the same. -/
theorem hausdorffEDist_closure : hausdorffEDist (closure s) (closure t) = hausdorffEDist s t := by
  simp

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
theorem _root_.IsClosed.hausdorffEDist_zero_iff (hs : IsClosed s) (ht : IsClosed t) :
    hausdorffEDist s t = 0 ↔ s = t := by
  rw [hausdorffEDist_zero_iff_closure_eq_closure, hs.closure_eq, ht.closure_eq]

/-- The Hausdorff edistance to the empty set is infinite. -/
theorem hausdorffEDist_empty (ne : s.Nonempty) : hausdorffEDist s ∅ = ∞ := by
  rcases ne with ⟨x, xs⟩
  have : infEDist x ∅ ≤ hausdorffEDist s ∅ := infEDist_le_hausdorffEDist_of_mem xs
  simpa using this

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty. -/
theorem nonempty_of_hausdorffEDist_ne_top (hs : s.Nonempty) (fin : hausdorffEDist s t ≠ ⊤) :
    t.Nonempty :=
  t.eq_empty_or_nonempty.resolve_left fun ht ↦ fin (ht.symm ▸ hausdorffEDist_empty hs)

theorem empty_or_nonempty_of_hausdorffEDist_ne_top (fin : hausdorffEDist s t ≠ ⊤) :
    (s = ∅ ∧ t = ∅) ∨ (s.Nonempty ∧ t.Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rcases t.eq_empty_or_nonempty with rfl | ht
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hausdorffEDist_comm] at fin
      exact Or.inr ⟨nonempty_of_hausdorffEDist_ne_top ht fin, ht⟩
  · exact Or.inr ⟨hs, nonempty_of_hausdorffEDist_ne_top hs fin⟩

@[simp]
theorem hausdorffEDist_singleton : hausdorffEDist {x} {y} = edist x y := by
  simp_rw [hausdorffEDist, iSup_singleton, infEDist_singleton]
  nth_rw 2 [edist_comm]
  exact max_self _

theorem hausdorffEDist_iUnion_le {ι : Sort*} {s t : ι → Set α} :
    hausdorffEDist (⋃ i, s i) (⋃ i, t i) ≤ ⨆ i, hausdorffEDist (s i) (t i) := by
  simp_rw [hausdorffEDist, max_le_iff, iSup_iUnion, iSup_le_iff, infEDist_iUnion]
  constructor <;> refine fun i x hx => (iInf_le _ i).trans <| le_iSup_of_le i ?_
  · exact le_max_of_le_left <| le_iSup₂_of_le x hx le_rfl
  · exact le_max_of_le_right <| le_iSup₂_of_le x hx le_rfl

theorem hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : Set α} :
    hausdorffEDist (s₁ ∪ s₂) (t₁ ∪ t₂) ≤ max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂) := by
  simp_rw [union_eq_iUnion, sup_eq_iSup]
  convert hausdorffEDist_iUnion_le with (_ | _)

theorem hausdorffEDist_prod_le {s₁ t₁ : Set α} {s₂ t₂ : Set β} :
    hausdorffEDist (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) ≤ max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂) := by
  refine le_of_forall_ge fun _ _ => ?_
  simp_all only [hausdorffEDist, infEDist_prod, max_le_iff, iSup_le_iff, mem_prod, true_and,
    implies_true]

end HausdorffEDist -- section

end Metric -- namespace

namespace EMetric

open Metric

@[deprecated (since := "2026-01-08")]
noncomputable alias infEdist := infEDist

@[deprecated (since := "2026-01-08")]
alias infEdist_empty := infEDist_empty

@[deprecated (since := "2026-01-08")] alias le_infEdist := le_infEDist
@[deprecated (since := "2026-01-08")] alias infEdist_union := infEDist_union
@[deprecated (since := "2026-01-08")] alias infEdist_iUnion := infEDist_iUnion
@[deprecated (since := "2026-01-08")] alias infEdist_biUnion := infEDist_biUnion
@[deprecated (since := "2026-01-08")] alias infEdist_singleton := infEDist_singleton
@[deprecated (since := "2026-01-08")] alias infEdist_le_edist_of_mem := infEDist_le_edist_of_mem
@[deprecated (since := "2026-01-08")] alias infEdist_zero_of_mem := infEDist_zero_of_mem
@[deprecated (since := "2026-01-08")] alias infEdist_anti := infEDist_anti
@[deprecated (since := "2026-01-08")] alias infEdist_lt_iff := infEDist_lt_iff

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_add_edist := infEDist_le_infEDist_add_edist

@[deprecated (since := "2026-01-08")]
alias infEdist_le_edist_add_infEdist := infEDist_le_edist_add_infEDist

@[deprecated (since := "2026-01-08")]
alias edist_le_infEdist_add_ediam := edist_le_infEDist_add_ediam

@[deprecated (since := "2026-01-08")] alias continuous_infEdist := continuous_infEDist
@[deprecated (since := "2026-01-08")] alias infEdist_closure := infEDist_closure

@[deprecated (since := "2026-01-08")]
alias mem_closure_iff_infEdist_zero := mem_closure_iff_infEDist_zero

@[deprecated (since := "2026-01-08")]
alias mem_iff_infEdist_zero_of_closed := mem_iff_infEDist_zero_of_closed

@[deprecated (since := "2026-01-08")]
alias infEdist_pos_iff_notMem_closure := infEDist_pos_iff_notMem_closure

@[deprecated (since := "2026-01-08")]
alias infEdist_closure_pos_iff_notMem_closure := infEDist_closure_pos_iff_notMem_closure

@[deprecated (since := "2026-01-08")]
alias exists_real_pos_lt_infEdist_of_notMem_closure := exists_real_pos_lt_infEDist_of_notMem_closure

@[deprecated (since := "2026-01-08")]
alias disjoint_closedBall_of_lt_infEdist := disjoint_closedEBall_of_lt_infEDist

@[deprecated (since := "2026-01-08")] alias infEdist_image := infEDist_image
@[deprecated (since := "2026-01-08")] alias infEdist_vadd := infEDist_vadd
@[to_additive existing, deprecated (since := "2026-01-08")] alias infEdist_smul := infEDist_smul

@[deprecated (since := "2026-01-08")]
alias _root_.IsCompact.exists_infEdist_eq_edist := _root_.IsCompact.exists_infEDist_eq_edist

@[deprecated (since := "2026-01-08")] alias exists_pos_forall_lt_edist := exists_pos_forall_lt_edist
@[deprecated (since := "2026-01-08")] alias infEdist_prod := infEDist_prod

@[deprecated (since := "2026-01-08")] noncomputable alias hausdorffEdist := hausdorffEDist
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_def := hausdorffEDist_def
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_self := hausdorffEDist_self
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_comm := hausdorffEDist_comm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_infEdist := hausdorffEDist_le_of_infEDist

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_mem_edist := hausdorffEDist_le_of_mem_edist

@[deprecated (since := "2026-01-08")]
alias infEdist_le_hausdorffEdist_of_mem := infEDist_le_hausdorffEDist_of_mem

@[deprecated (since := "2026-01-08")]
alias exists_edist_lt_of_hausdorffEdist_lt := exists_edist_lt_of_hausdorffEDist_lt

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_add_hausdorffEdist := infEDist_le_infEDist_add_hausdorffEDist

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_image := hausdorffEDist_image
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_le_ediam := hausdorffEDist_le_ediam
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_triangle := hausdorffEDist_triangle

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_zero_iff_closure_eq_closure := hausdorffEDist_zero_iff_closure_eq_closure

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_self_closure := hausdorffEDist_self_closure

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure₁ := hausdorffEDist_closure_left
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure₂ := hausdorffEDist_closure_right
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure := hausdorffEDist_closure

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_zero_iff_eq_of_closed := IsClosed.hausdorffEDist_zero_iff

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_empty := hausdorffEDist_empty

@[deprecated (since := "2026-01-08")]
alias nonempty_of_hausdorffEdist_ne_top := nonempty_of_hausdorffEDist_ne_top

@[deprecated (since := "2026-01-08")]
alias empty_or_nonempty_of_hausdorffEdist_ne_top := empty_or_nonempty_of_hausdorffEDist_ne_top

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_singleton := hausdorffEDist_singleton
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_iUnion_le := hausdorffEDist_iUnion_le
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_union_le := hausdorffEDist_union_le
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_prod_le := hausdorffEDist_prod_le

end EMetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

namespace Metric

section

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ`. -/

/-- The minimal distance of a point to a set -/
def infDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (infEDist x s)

theorem infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y := by
  rw [infDist, infEDist, iInf_subtype', ENNReal.toReal_iInf]
  · simp only [dist_edist]
  · finiteness

/-- The minimal distance is always nonnegative -/
theorem infDist_nonneg : 0 ≤ infDist x s := toReal_nonneg

/-- The minimal distance to the empty set is 0 (if you want to have the more reasonable
value `∞` instead, use `Metric.infEDist`, which takes values in `ℝ≥0∞`) -/
@[simp]
theorem infDist_empty : infDist x ∅ = 0 := by simp [infDist]

lemma isGLB_infDist (hs : s.Nonempty) : IsGLB ((dist x ·) '' s) (infDist x s) := by
  simpa [infDist_eq_iInf, sInf_image']
    using isGLB_csInf (hs.image _) ⟨0, by simp [lowerBounds]⟩

/-- In a metric space, the minimal edistance to a nonempty set is finite. -/
theorem infEDist_ne_top (h : s.Nonempty) : infEDist x s ≠ ∞ := by
  rcases h with ⟨y, hy⟩
  exact ne_top_of_le_ne_top (edist_ne_top _ _) (infEDist_le_edist_of_mem hy)

@[deprecated (since := "2026-01-08")]
alias infEdist_ne_top := infEDist_ne_top

@[simp]
theorem infEDist_eq_top_iff : infEDist x s = ∞ ↔ s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [*, Nonempty.ne_empty, infEDist_ne_top]

@[deprecated (since := "2026-01-08")]
alias infEdist_eq_top_iff := infEDist_eq_top_iff

/-- The minimal distance of a point to a set containing it vanishes. -/
theorem infDist_zero_of_mem (h : x ∈ s) : infDist x s = 0 := by
  simp [infEDist_zero_of_mem h, infDist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton. -/
@[simp]
theorem infDist_singleton : infDist x {y} = dist x y := by simp [infDist, dist_edist]

/-- The minimal distance to a set is bounded by the distance to any point in this set. -/
theorem infDist_le_dist_of_mem (h : y ∈ s) : infDist x s ≤ dist x y := by
  rw [dist_edist, infDist]
  exact ENNReal.toReal_mono (edist_ne_top _ _) (infEDist_le_edist_of_mem h)

/-- The minimal distance is monotone with respect to inclusion. -/
theorem infDist_le_infDist_of_subset (h : s ⊆ t) (hs : s.Nonempty) : infDist x t ≤ infDist x s :=
  ENNReal.toReal_mono (infEDist_ne_top hs) (infEDist_anti h)

lemma le_infDist {r : ℝ} (hs : s.Nonempty) : r ≤ infDist x s ↔ ∀ ⦃y⦄, y ∈ s → r ≤ dist x y := by
  simp_rw [infDist, ← ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hs), le_infEDist,
    ENNReal.ofReal_le_iff_le_toReal (edist_ne_top _ _), ← dist_edist]

/-- The minimal distance to a set `s` is `< r` iff there exists a point in `s` at distance `< r`. -/
theorem infDist_lt_iff {r : ℝ} (hs : s.Nonempty) : infDist x s < r ↔ ∃ y ∈ s, dist x y < r := by
  simp [← not_le, le_infDist hs]

/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y`. -/
theorem infDist_le_infDist_add_dist : infDist x s ≤ infDist y s + dist x y := by
  rw [infDist, infDist, dist_edist]
  refine ENNReal.toReal_le_add' infEDist_le_infEDist_add_edist ?_ (flip absurd (edist_ne_top _ _))
  simp only [infEDist_eq_top_iff, imp_self]

theorem notMem_of_dist_lt_infDist (h : dist x y < infDist x s) : y ∉ s := fun hy =>
  h.not_ge <| infDist_le_dist_of_mem hy

theorem disjoint_ball_infDist : Disjoint (ball x (infDist x s)) s :=
  disjoint_left.2 fun _y hy => notMem_of_dist_lt_infDist <| mem_ball'.1 hy

theorem ball_infDist_subset_compl : ball x (infDist x s) ⊆ sᶜ :=
  (disjoint_ball_infDist (s := s)).subset_compl_right

theorem ball_infDist_compl_subset : ball x (infDist x sᶜ) ⊆ s :=
  ball_infDist_subset_compl.trans_eq (compl_compl s)

theorem disjoint_closedBall_of_lt_infDist {r : ℝ} (h : r < infDist x s) :
    Disjoint (closedBall x r) s :=
  disjoint_ball_infDist.mono_left <| closedBall_subset_ball h

theorem dist_le_infDist_add_diam (hs : IsBounded s) (hy : y ∈ s) :
    dist x y ≤ infDist x s + diam s := by
  rw [infDist, diam, dist_edist]
  exact toReal_le_add (edist_le_infEDist_add_ediam hy) (infEDist_ne_top ⟨y, hy⟩) hs.ediam_ne_top

variable (s)

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
theorem lipschitz_infDist_pt : LipschitzWith 1 (infDist · s) :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/-- The minimal distance to a set is uniformly continuous in point -/
theorem uniformContinuous_infDist_pt : UniformContinuous (infDist · s) :=
  (lipschitz_infDist_pt s).uniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[continuity, fun_prop]
theorem continuous_infDist_pt : Continuous (infDist · s) :=
  (uniformContinuous_infDist_pt s).continuous

variable {s}

/-- The minimal distances to a set and its closure coincide. -/
theorem infDist_closure : infDist x (closure s) = infDist x s := by
  simp [infDist, infEDist_closure]

/-- If a point belongs to the closure of `s`, then its infimum distance to `s` equals zero.
The converse is true provided that `s` is nonempty, see `Metric.mem_closure_iff_infDist_zero`. -/
theorem infDist_zero_of_mem_closure (hx : x ∈ closure s) : infDist x s = 0 := by
  rw [← infDist_closure]
  exact infDist_zero_of_mem hx

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes. -/
theorem mem_closure_iff_infDist_zero (h : s.Nonempty) : x ∈ closure s ↔ infDist x s = 0 := by
  simp [mem_closure_iff_infEDist_zero, infDist, ENNReal.toReal_eq_zero_iff, infEDist_ne_top h]

theorem infDist_pos_iff_notMem_closure (hs : s.Nonempty) :
    x ∉ closure s ↔ 0 < infDist x s :=
  (mem_closure_iff_infDist_zero hs).not.trans infDist_nonneg.lt_iff_ne'.symm

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem _root_.IsClosed.mem_iff_infDist_zero (h : IsClosed s) (hs : s.Nonempty) :
    x ∈ s ↔ infDist x s = 0 := by rw [← mem_closure_iff_infDist_zero hs, h.closure_eq]

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes. -/
theorem _root_.IsClosed.notMem_iff_infDist_pos (h : IsClosed s) (hs : s.Nonempty) :
    x ∉ s ↔ 0 < infDist x s := by
  simp [h.mem_iff_infDist_zero hs, infDist_nonneg.lt_iff_ne']

theorem continuousAt_inv_infDist_pt (h : x ∉ closure s) :
    ContinuousAt (fun x ↦ (infDist x s)⁻¹) x := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp only [infDist_empty, continuousAt_const]
  · refine (continuous_infDist_pt s).continuousAt.inv₀ ?_
    rwa [Ne, ← mem_closure_iff_infDist_zero hs]

/-- The infimum distance is invariant under isometries. -/
theorem infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t := by
  simp [infDist, infEDist_image hΦ]

theorem infDist_inter_closedBall_of_mem (h : y ∈ s) :
    infDist x (s ∩ closedBall x (dist y x)) = infDist x s := by
  replace h : y ∈ s ∩ closedBall x (dist y x) := ⟨h, mem_closedBall.2 le_rfl⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset inter_subset_left ⟨y, h⟩)
  refine not_lt.1 fun hlt => ?_
  rcases (infDist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  rcases le_or_gt (dist z x) (dist y x) with hle | hlt
  · exact hz.not_ge (infDist_le_dist_of_mem ⟨hzs, hle⟩)
  · rw [dist_comm z, dist_comm y] at hlt
    exact (hlt.trans hz).not_ge (infDist_le_dist_of_mem h)

theorem _root_.IsCompact.exists_infDist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infDist x s = dist x y :=
  let ⟨y, hys, hy⟩ := h.exists_infEDist_eq_edist hne x
  ⟨y, hys, by rw [infDist, dist_edist, hy]⟩

theorem _root_.IsClosed.exists_infDist_eq_dist [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty)
    (x : α) : ∃ y ∈ s, infDist x s = dist x y := by
  rcases hne with ⟨z, hz⟩
  rw [← infDist_inter_closedBall_of_mem hz]
  set t := s ∩ closedBall x (dist z x)
  have htc : IsCompact t := (isCompact_closedBall x (dist z x)).inter_left h
  have htne : t.Nonempty := ⟨z, hz, mem_closedBall.2 le_rfl⟩
  obtain ⟨y, ⟨hys, -⟩, hyd⟩ : ∃ y ∈ t, infDist x t = dist x y := htc.exists_infDist_eq_dist htne x
  exact ⟨y, hys, hyd⟩

theorem exists_mem_closure_infDist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x : α) :
    ∃ y ∈ closure s, infDist x s = dist x y := by
  simpa only [infDist_closure] using isClosed_closure.exists_infDist_eq_dist hne.closure x

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/

/-- The minimal distance of a point to a set as a `ℝ≥0` -/
def infNndist (x : α) (s : Set α) : ℝ≥0 :=
  ENNReal.toNNReal (infEDist x s)

@[simp]
theorem coe_infNndist : (infNndist x s : ℝ) = infDist x s :=
  rfl

/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
theorem lipschitz_infNndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x s :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
theorem uniformContinuous_infNndist_pt (s : Set α) : UniformContinuous fun x => infNndist x s :=
  (lipschitz_infNndist_pt s).uniformContinuous

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
@[continuity, fun_prop]
theorem continuous_infNndist_pt (s : Set α) : Continuous fun x => infNndist x s :=
  (uniformContinuous_infNndist_pt s).continuous

/-! ### The Hausdorff distance as a function into `ℝ`. -/

/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily. -/
def hausdorffDist (s t : Set α) : ℝ :=
  ENNReal.toReal (hausdorffEDist s t)

/-- The Hausdorff distance is nonnegative. -/
theorem hausdorffDist_nonneg : 0 ≤ hausdorffDist s t := by simp [hausdorffDist]

/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
theorem hausdorffEDist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty)
    (bs : IsBounded s) (bt : IsBounded t) : hausdorffEDist s t ≠ ⊤ := by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases bs.subset_closedBall ct with ⟨rs, hrs⟩
  rcases bt.subset_closedBall cs with ⟨rt, hrt⟩
  have : hausdorffEDist s t ≤ ENNReal.ofReal (max rs rt) := by
    apply hausdorffEDist_le_of_mem_edist
    · intro x xs
      exists ct, hct
      have : dist x ct ≤ max rs rt := le_trans (hrs xs) (le_max_left _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
    · intro x xt
      exists cs, hcs
      have : dist x cs ≤ max rs rt := le_trans (hrt xt) (le_max_right _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top_of_nonempty_of_bounded := hausdorffEDist_ne_top_of_nonempty_of_bounded

/-- The Hausdorff distance between a set and itself is zero. -/
@[simp]
theorem hausdorffDist_self_zero : hausdorffDist s s = 0 := by simp [hausdorffDist]

/-- The Hausdorff distances from `s` to `t` and from `t` to `s` coincide. -/
theorem hausdorffDist_comm : hausdorffDist s t = hausdorffDist t s := by
  simp [hausdorffDist, hausdorffEDist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`). -/
@[simp]
theorem hausdorffDist_empty : hausdorffDist s ∅ = 0 := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [hausdorffDist, hausdorffEDist_empty h]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`). -/
@[simp]
theorem hausdorffDist_empty' : hausdorffDist ∅ s = 0 := by simp [hausdorffDist_comm]

/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
theorem hausdorffDist_le_of_infDist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, infDist x t ≤ r)
    (H2 : ∀ x ∈ t, infDist x s ≤ r) : hausdorffDist s t ≤ r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rwa [hausdorffDist_empty']
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rwa [hausdorffDist_empty]
  have : hausdorffEDist s t ≤ ENNReal.ofReal r := by
    apply hausdorffEDist_le_of_infEDist _ _
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top ht) hr] using H1
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hs) hr] using H2
  exact ENNReal.toReal_le_of_le_ofReal hr this

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem hausdorffDist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, dist x y ≤ r) : hausdorffDist s t ≤ r := by
  apply hausdorffDist_le_of_infDist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infDist_le_dist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infDist_le_dist_of_mem ys) hy

/-- The Hausdorff distance is controlled by the diameter of the union. -/
theorem hausdorffDist_le_diam (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempty)
    (bt : IsBounded t) : hausdorffDist s t ≤ diam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffDist_le_of_mem_dist diam_nonneg ?_ ?_
  · exact fun z hz => ⟨y, yt, dist_le_diam_of_mem (bs.union bt) (subset_union_left hz)
      (subset_union_right yt)⟩
  · exact fun z hz => ⟨x, xs, dist_le_diam_of_mem (bs.union bt) (subset_union_right hz)
      (subset_union_left xs)⟩

/-- The distance to a set is controlled by the Hausdorff distance. -/
theorem infDist_le_hausdorffDist_of_mem (hx : x ∈ s) (fin : hausdorffEDist s t ≠ ⊤) :
    infDist x t ≤ hausdorffDist s t :=
  toReal_mono fin (infEDist_le_hausdorffEDist_of_mem hx)

/-- If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set. -/
theorem exists_dist_lt_of_hausdorffDist_lt {r : ℝ} (h : x ∈ s) (H : hausdorffDist s t < r)
    (fin : hausdorffEDist s t ≠ ⊤) : ∃ y ∈ t, dist x y < r := by
  have r0 : 0 < r := lt_of_le_of_lt hausdorffDist_nonneg H
  have : hausdorffEDist s t < ENNReal.ofReal r := by
    rwa [hausdorffDist, ← ENNReal.toReal_ofReal (le_of_lt r0),
      ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top] at H
  rcases exists_edist_lt_of_hausdorffEDist_lt h this with ⟨y, hy, yr⟩
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff r0] at yr
  exact ⟨y, hy, yr⟩

/-- If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set. -/
theorem exists_dist_lt_of_hausdorffDist_lt' {r : ℝ} (h : y ∈ t) (H : hausdorffDist s t < r)
    (fin : hausdorffEDist s t ≠ ⊤) : ∃ x ∈ s, dist x y < r := by
  rw [hausdorffDist_comm] at H
  rw [hausdorffEDist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_hausdorffDist_lt h H fin

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
theorem infDist_le_infDist_add_hausdorffDist (fin : hausdorffEDist s t ≠ ⊤) :
    infDist x t ≤ infDist x s + hausdorffDist s t := by
  refine toReal_le_add' infEDist_le_infEDist_add_hausdorffEDist (fun h ↦ ?_) (flip absurd fin)
  rw [infEDist_eq_top_iff, ← not_nonempty_iff_eq_empty] at h ⊢
  rw [hausdorffEDist_comm] at fin
  exact mt (nonempty_of_hausdorffEDist_ne_top · fin) h

/-- The Hausdorff distance is invariant under isometries. -/
theorem hausdorffDist_image (h : Isometry Φ) :
    hausdorffDist (Φ '' s) (Φ '' t) = hausdorffDist s t := by
  simp [hausdorffDist, hausdorffEDist_image h]

/-- The Hausdorff distance satisfies the triangle inequality. -/
theorem hausdorffDist_triangle (fin : hausdorffEDist s t ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  refine toReal_le_add' hausdorffEDist_triangle (flip absurd fin) (not_imp_not.1 fun h ↦ ?_)
  rw [hausdorffEDist_comm] at fin
  exact ne_top_of_le_ne_top (add_ne_top.2 ⟨fin, h⟩) hausdorffEDist_triangle

/-- The Hausdorff distance satisfies the triangle inequality. -/
theorem hausdorffDist_triangle' (fin : hausdorffEDist t u ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  rw [hausdorffEDist_comm] at fin
  have I : hausdorffDist u s ≤ hausdorffDist u t + hausdorffDist t s :=
    hausdorffDist_triangle fin
  simpa [add_comm, hausdorffDist_comm] using I

/-- The Hausdorff distance between a set and its closure vanishes. -/
@[simp]
theorem hausdorffDist_self_closure : hausdorffDist s (closure s) = 0 := by simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem hausdorffDist_closure₁ : hausdorffDist (closure s) t = hausdorffDist s t := by
  simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem hausdorffDist_closure₂ : hausdorffDist s (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/-- The Hausdorff distances between two sets and their closures coincide. -/
theorem hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/-- Two sets are at zero Hausdorff distance if and only if they have the same closures. -/
theorem hausdorffDist_zero_iff_closure_eq_closure (fin : hausdorffEDist s t ≠ ⊤) :
    hausdorffDist s t = 0 ↔ closure s = closure t := by
  simp [← hausdorffEDist_zero_iff_closure_eq_closure, hausdorffDist,
    ENNReal.toReal_eq_zero_iff, fin]

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide. -/
theorem _root_.IsClosed.hausdorffDist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t)
    (fin : hausdorffEDist s t ≠ ⊤) : hausdorffDist s t = 0 ↔ s = t := by
  simp [← _root_.IsClosed.hausdorffEDist_zero_iff hs ht, hausdorffDist, ENNReal.toReal_eq_zero_iff,
    fin]

@[simp]
theorem hausdorffDist_singleton : hausdorffDist {x} {y} = dist x y := by
  rw [hausdorffDist, hausdorffEDist_singleton, dist_edist]

end

end Metric

/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.

## Main definitions

* `ContractingWith K f` : a Lipschitz continuous self-map with `K < 1`;
* `efixedPoint` : given a contracting map `f` on a complete emetric space and a point `x`
  such that `edist x (f x) ≠ ∞`, `efixedPoint f hf x hx` is the unique fixed point of `f`
  in `EMetric.ball x ∞`;
* `fixedPoint` : the unique fixed point of a contracting map on a complete nonempty metric space.

## Tags

contracting map, fixed point, Banach fixed point theorem
-/

open NNReal Topology ENNReal Filter Function

variable {α : Type*}

/-- A map is said to be `ContractingWith K`, if `K < 1` and `f` is `LipschitzWith K`. -/
def ContractingWith [EMetricSpace α] (K : ℝ≥0) (f : α → α) :=
  K < 1 ∧ LipschitzWith K f

namespace ContractingWith

variable [EMetricSpace α] {K : ℝ≥0} {f : α → α}

open EMetric Set

theorem toLipschitzWith (hf : ContractingWith K f) : LipschitzWith K f := hf.2

theorem one_sub_K_pos' (hf : ContractingWith K f) : (0 : ℝ≥0∞) < 1 - K := by simp [hf.1]

theorem one_sub_K_ne_zero (hf : ContractingWith K f) : (1 : ℝ≥0∞) - K ≠ 0 :=
  ne_of_gt hf.one_sub_K_pos'

theorem one_sub_K_ne_top : (1 : ℝ≥0∞) - K ≠ ∞ := by
  norm_cast
  exact ENNReal.coe_ne_top

theorem edist_inequality (hf : ContractingWith K f) {x y} (h : edist x y ≠ ∞) :
    edist x y ≤ (edist x (f x) + edist y (f y)) / (1 - K) :=
  suffices edist x y ≤ edist x (f x) + edist y (f y) + K * edist x y by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hf.one_sub_K_ne_zero) (Or.inl one_sub_K_ne_top),
      mul_comm, ENNReal.sub_mul fun _ _ ↦ h, one_mul, tsub_le_iff_right]
  calc
    edist x y ≤ edist x (f x) + edist (f x) (f y) + edist (f y) y := edist_triangle4 _ _ _ _
    _ = edist x (f x) + edist y (f y) + edist (f x) (f y) := by rw [edist_comm y, add_right_comm]
    _ ≤ edist x (f x) + edist y (f y) + K * edist x y := add_le_add le_rfl (hf.2 _ _)

theorem edist_le_of_fixedPoint (hf : ContractingWith K f) {x y} (h : edist x y ≠ ∞)
    (hy : IsFixedPt f y) : edist x y ≤ edist x (f x) / (1 - K) := by
  simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h

theorem eq_or_edist_eq_top_of_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt f y) : x = y ∨ edist x y = ∞ := by
  refine or_iff_not_imp_right.2 fun h ↦ edist_le_zero.1 ?_
  simpa only [hx.eq, edist_self, add_zero, ENNReal.zero_div] using hf.edist_le_of_fixedPoint h hy

/-- If a map `f` is `ContractingWith K`, and `s` is a forward-invariant set, then
restriction of `f` to `s` is `ContractingWith K` as well. -/
theorem restrict (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s) :
    ContractingWith K (hs.restrict f s s) :=
  ⟨hf.1, fun x y ↦ hf.2 x y⟩

section
variable [CompleteSpace α]

/-- Banach fixed-point theorem, contraction mapping theorem, `EMetricSpace` version.
A contracting map on a complete metric space has a fixed point.
We include more conclusions in this theorem to avoid proving them again later.

The main API for this theorem are the functions `efixedPoint` and `fixedPoint`,
and lemmas about these functions. -/
theorem exists_fixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) :
    ∃ y, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  have : CauchySeq fun n ↦ f^[n] x :=
    cauchySeq_of_edist_le_geometric K (edist x (f x)) (ENNReal.coe_lt_one_iff.2 hf.1) hx
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x)
  let ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  ⟨y, isFixedPt_of_tendsto_iterate hy hf.2.continuous.continuousAt, hy,
    edist_le_of_edist_le_geometric_of_tendsto K (edist x (f x))
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x) hy⟩

variable (f) in
-- avoid `efixedPoint _` in pretty printer
/-- Let `x` be a point of a complete emetric space. Suppose that `f` is a contracting map,
and `edist x (f x) ≠ ∞`. Then `efixedPoint` is the unique fixed point of `f`
in `EMetric.ball x ∞`. -/
noncomputable def efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) : α :=
  Classical.choose <| hf.exists_fixedPoint x hx

theorem efixedPoint_isFixedPt (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    IsFixedPt f (efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).1

theorem tendsto_iterate_efixedPoint (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.1

theorem apriori_edist_iterate_efixedPoint_le (hf : ContractingWith K f) {x : α}
    (hx : edist x (f x) ≠ ∞) (n : ℕ) :
    edist (f^[n] x) (efixedPoint f hf x hx) ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.2 n

theorem edist_efixedPoint_le (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint f hf x hx) ≤ edist x (f x) / (1 - K) := by
  convert hf.apriori_edist_iterate_efixedPoint_le hx 0
  simp only [pow_zero, mul_one]

theorem edist_efixedPoint_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint f hf x hx) < ∞ :=
  (hf.edist_efixedPoint_le hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

theorem efixedPoint_eq_of_edist_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞)
    {y : α} (hy : edist y (f y) ≠ ∞) (h : edist x y ≠ ∞) :
    efixedPoint f hf x hx = efixedPoint f hf y hy := by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' ↦ False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt
  change edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    exact hf.edist_efixedPoint_lt_top hx
  trans y
  exacts [lt_top_iff_ne_top.2 h, hf.edist_efixedPoint_lt_top hy]

end

/-- Banach fixed-point theorem for maps contracting on a complete subset. -/
theorem exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    ∃ y ∈ s, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) := by
  haveI := hsc.completeSpace_coe
  rcases hf.exists_fixedPoint ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩
  refine ⟨y, y.2, Subtype.ext_iff.1 hfy, ?_, fun n ↦ ?_⟩
  · convert (continuous_subtype_val.tendsto _).comp h_tendsto
    simp only [(· ∘ ·), MapsTo.iterate_restrict, MapsTo.val_restrict_apply]
  · convert hle n
    rw [MapsTo.iterate_restrict]
    rfl

variable (f) in
-- avoid `efixedPoint _` in pretty printer
/-- Let `s` be a complete forward-invariant set of a self-map `f`. If `f` contracts on `s`
and `x ∈ s` satisfies `edist x (f x) ≠ ∞`, then `efixedPoint'` is the unique fixed point
of the restriction of `f` to `s ∩ EMetric.ball x ∞`. -/
noncomputable def efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) (x : α) (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    α :=
  Classical.choose <| hf.exists_fixedPoint' hsc hsf hxs hx

theorem efixedPoint_mem' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    efixedPoint' f hsc hsf hf x hxs hx ∈ s :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).1

theorem efixedPoint_isFixedPt' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    IsFixedPt f (efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.1

theorem tendsto_iterate_efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.1

theorem apriori_edist_iterate_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞)
    (n : ℕ) :
    edist (f^[n] x) (efixedPoint' f hsc hsf hf x hxs hx) ≤
      edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.2 n

theorem edist_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) ≤ edist x (f x) / (1 - K) := by
  convert hf.apriori_edist_iterate_efixedPoint_le' hsc hsf hxs hx 0
  rw [pow_zero, mul_one]

theorem edist_efixedPoint_lt_top' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) < ∞ :=
  (hf.edist_efixedPoint_le' hsc hsf hxs hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

/-- If a globally contracting map `f` has two complete forward-invariant sets `s`, `t`,
and `x ∈ s` is at a finite distance from `y ∈ t`, then the `efixedPoint'` constructed by `x`
is the same as the `efixedPoint'` constructed by `y`.

This lemma takes additional arguments stating that `f` contracts on `s` and `t` because this way
it can be used to prove the desired equality with non-trivial proofs of these facts. -/
theorem efixedPoint_eq_of_edist_lt_top' (hf : ContractingWith K f) {s : Set α} (hsc : IsComplete s)
    (hsf : MapsTo f s s) (hfs : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) ≠ ∞) {t : Set α} (htc : IsComplete t) (htf : MapsTo f t t)
    (hft : ContractingWith K <| htf.restrict f t t) {y : α} (hyt : y ∈ t) (hy : edist y (f y) ≠ ∞)
    (hxy : edist x y ≠ ∞) :
    efixedPoint' f hsc hsf hfs x hxs hx = efixedPoint' f htc htf hft y hyt hy := by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' ↦ False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt'
  change edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    apply edist_efixedPoint_lt_top'
  trans y
  · exact lt_top_iff_ne_top.2 hxy
  · apply edist_efixedPoint_lt_top'

end ContractingWith

namespace ContractingWith

variable [MetricSpace α] {K : ℝ≥0} {f : α → α}

theorem one_sub_K_pos (hf : ContractingWith K f) : (0 : ℝ) < 1 - K :=
  sub_pos.2 hf.1

section
variable (hf : ContractingWith K f)
include hf

theorem dist_le_mul (x y : α) : dist (f x) (f y) ≤ K * dist x y :=
  hf.toLipschitzWith.dist_le_mul x y

theorem dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
  suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  calc
    dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ ≤ dist x (f x) + dist y (f y) + K * dist x y := add_le_add_left (hf.dist_le_mul _ _) _

theorem dist_le_of_fixedPoint (x) {y} (hy : IsFixedPt f y) : dist x y ≤ dist x (f x) / (1 - K) := by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y

theorem fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
  (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
theorem dist_fixedPoint_fixedPoint_of_dist_le' (g : α → α) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt g y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist x y ≤ C / (1 - K) :=
  calc
    dist x y = dist y x := dist_comm x y
    _ ≤ dist y (f y) / (1 - K) := hf.dist_le_of_fixedPoint y hx
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
    _ ≤ C / (1 - K) := (div_le_div_iff_of_pos_right hf.one_sub_K_pos).2 (hfg y)

variable [Nonempty α] [CompleteSpace α]

variable (f) in
/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
noncomputable def fixedPoint : α :=
  efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)

/-- The point provided by `ContractingWith.fixedPoint` is actually a fixed point. -/
theorem fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf) :=
  hf.efixedPoint_isFixedPt _

theorem fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf :=
  hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt

theorem dist_fixedPoint_le (x) : dist x (fixedPoint f hf) ≤ dist x (f x) / (1 - K) :=
  hf.dist_le_of_fixedPoint x hf.fixedPoint_isFixedPt

/-- A posteriori estimates on the convergence of iterates to the fixed point. -/
theorem aposteriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) ≤ dist (f^[n] x) (f^[n+1] x) / (1 - K) := by
  rw [iterate_succ']
  apply hf.dist_fixedPoint_le

theorem apriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) ≤ dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  calc
    _ ≤ dist (f^[n] x) (f^[n+1] x) / (1 - K) := hf.aposteriori_dist_iterate_fixedPoint_le x n
    _ ≤ _ := by
      gcongr; exacts [hf.one_sub_K_pos.le, hf.toLipschitzWith.dist_iterate_succ_le_geometric x n]

theorem tendsto_iterate_fixedPoint (x) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| fixedPoint f hf) := by
  convert tendsto_iterate_efixedPoint hf (edist_ne_top x _)
  refine (fixedPoint_unique _ ?_).symm
  apply efixedPoint_isFixedPt

theorem fixedPoint_lipschitz_in_map {g : α → α} (hg : ContractingWith K g) {C}
    (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist (fixedPoint f hf) (fixedPoint g hg) ≤ C / (1 - K) :=
  hf.dist_fixedPoint_fixedPoint_of_dist_le' g hf.fixedPoint_isFixedPt hg.fixedPoint_isFixedPt hfg

end

variable [Nonempty α] [CompleteSpace α]

/-- If a map `f` has a contracting iterate `f^[n]`, then the fixed point of `f^[n]` is also a fixed
point of `f`. -/
theorem isFixedPt_fixedPoint_iterate {n : ℕ} (hf : ContractingWith K f^[n]) :
    IsFixedPt f (hf.fixedPoint f^[n]) := by
  set x := hf.fixedPoint f^[n]
  have hx : f^[n] x = x := hf.fixedPoint_isFixedPt
  have := hf.toLipschitzWith.dist_le_mul x (f x)
  rw [← iterate_succ_apply, iterate_succ_apply', hx] at this
  contrapose! this
  have := dist_pos.2 (Ne.symm this)
  simpa only [NNReal.coe_one, one_mul, NNReal.val_eq_coe] using (mul_lt_mul_right this).mpr hf.left

end ContractingWith

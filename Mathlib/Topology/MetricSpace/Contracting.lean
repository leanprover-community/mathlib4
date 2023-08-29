/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Dynamics.FixedPoints.Topology

#align_import topology.metric_space.contracting from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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


open NNReal Topology Classical ENNReal Filter Function

variable {α : Type*}

/-- A map is said to be `ContractingWith K`, if `K < 1` and `f` is `LipschitzWith K`. -/
def ContractingWith [EMetricSpace α] (K : ℝ≥0) (f : α → α) :=
  K < 1 ∧ LipschitzWith K f
#align contracting_with ContractingWith

namespace ContractingWith

variable [EMetricSpace α] [cs : CompleteSpace α] {K : ℝ≥0} {f : α → α}

open EMetric Set

theorem toLipschitzWith (hf : ContractingWith K f) : LipschitzWith K f := hf.2
#align contracting_with.to_lipschitz_with ContractingWith.toLipschitzWith

theorem one_sub_K_pos' (hf : ContractingWith K f) : (0 : ℝ≥0∞) < 1 - K := by simp [hf.1]
                                                                             -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align contracting_with.one_sub_K_pos' ContractingWith.one_sub_K_pos'

theorem one_sub_K_ne_zero (hf : ContractingWith K f) : (1 : ℝ≥0∞) - K ≠ 0 :=
  ne_of_gt hf.one_sub_K_pos'
set_option linter.uppercaseLean3 false in
#align contracting_with.one_sub_K_ne_zero ContractingWith.one_sub_K_ne_zero

theorem one_sub_K_ne_top : (1 : ℝ≥0∞) - K ≠ ∞ := by
  norm_cast
  -- ⊢ ¬1 - ↑K = ⊤
  exact ENNReal.coe_ne_top
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align contracting_with.one_sub_K_ne_top ContractingWith.one_sub_K_ne_top

theorem edist_inequality (hf : ContractingWith K f) {x y} (h : edist x y ≠ ∞) :
    edist x y ≤ (edist x (f x) + edist y (f y)) / (1 - K) :=
  suffices edist x y ≤ edist x (f x) + edist y (f y) + K * edist x y by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hf.one_sub_K_ne_zero) (Or.inl one_sub_K_ne_top),
      mul_comm, ENNReal.sub_mul fun _ _ ↦ h, one_mul, tsub_le_iff_right]
  calc
    edist x y ≤ edist x (f x) + edist (f x) (f y) + edist (f y) y := edist_triangle4 _ _ _ _
    _ = edist x (f x) + edist y (f y) + edist (f x) (f y) := by rw [edist_comm y, add_right_comm]
                                                                -- 🎉 no goals
    _ ≤ edist x (f x) + edist y (f y) + K * edist x y := add_le_add le_rfl (hf.2 _ _)
#align contracting_with.edist_inequality ContractingWith.edist_inequality

theorem edist_le_of_fixedPoint (hf : ContractingWith K f) {x y} (h : edist x y ≠ ∞)
    (hy : IsFixedPt f y) : edist x y ≤ edist x (f x) / (1 - K) := by
  simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h
  -- 🎉 no goals
#align contracting_with.edist_le_of_fixed_point ContractingWith.edist_le_of_fixedPoint

theorem eq_or_edist_eq_top_of_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt f y) : x = y ∨ edist x y = ∞ := by
  refine' or_iff_not_imp_right.2 fun h ↦ edist_le_zero.1 _
  -- ⊢ edist x y ≤ 0
  simpa only [hx.eq, edist_self, add_zero, ENNReal.zero_div] using hf.edist_le_of_fixedPoint h hy
  -- 🎉 no goals
#align contracting_with.eq_or_edist_eq_top_of_fixed_points ContractingWith.eq_or_edist_eq_top_of_fixedPoints

/-- If a map `f` is `ContractingWith K`, and `s` is a forward-invariant set, then
restriction of `f` to `s` is `ContractingWith K` as well. -/
theorem restrict (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s) :
    ContractingWith K (hs.restrict f s s) :=
  ⟨hf.1, fun x y ↦ hf.2 x y⟩
#align contracting_with.restrict ContractingWith.restrict

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
#align contracting_with.exists_fixed_point ContractingWith.exists_fixedPoint

variable (f)

-- avoid `efixedPoint _` in pretty printer
/-- Let `x` be a point of a complete emetric space. Suppose that `f` is a contracting map,
and `edist x (f x) ≠ ∞`. Then `efixedPoint` is the unique fixed point of `f`
in `EMetric.ball x ∞`. -/
noncomputable def efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) : α :=
  Classical.choose <| hf.exists_fixedPoint x hx
#align contracting_with.efixed_point ContractingWith.efixedPoint

variable {f}

theorem efixedPoint_isFixedPt (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    IsFixedPt f (efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).1
#align contracting_with.efixed_point_is_fixed_pt ContractingWith.efixedPoint_isFixedPt

theorem tendsto_iterate_efixedPoint (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.1
#align contracting_with.tendsto_iterate_efixed_point ContractingWith.tendsto_iterate_efixedPoint

theorem apriori_edist_iterate_efixedPoint_le (hf : ContractingWith K f) {x : α}
    (hx : edist x (f x) ≠ ∞) (n : ℕ) :
    edist (f^[n] x) (efixedPoint f hf x hx) ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.2 n
#align contracting_with.apriori_edist_iterate_efixed_point_le ContractingWith.apriori_edist_iterate_efixedPoint_le

theorem edist_efixedPoint_le (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint f hf x hx) ≤ edist x (f x) / (1 - K) := by
  convert hf.apriori_edist_iterate_efixedPoint_le hx 0
  -- ⊢ edist x (f x) = edist x (f x) * ↑K ^ 0
  simp only [pow_zero, mul_one]
  -- 🎉 no goals
#align contracting_with.edist_efixed_point_le ContractingWith.edist_efixedPoint_le

theorem edist_efixedPoint_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint f hf x hx) < ∞ :=
  (hf.edist_efixedPoint_le hx).trans_lt
    (ENNReal.mul_lt_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero)
#align contracting_with.edist_efixed_point_lt_top ContractingWith.edist_efixedPoint_lt_top

theorem efixedPoint_eq_of_edist_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞)
    {y : α} (hy : edist y (f y) ≠ ∞) (h : edist x y ≠ ∞) :
    efixedPoint f hf x hx = efixedPoint f hf y hy := by
  refine' (hf.eq_or_edist_eq_top_of_fixedPoints _ _).elim id fun h' ↦ False.elim (ne_of_lt _ h')
    <;> try apply efixedPoint_isFixedPt
        -- 🎉 no goals
        -- 🎉 no goals
        -- ⊢ edist (efixedPoint f hf x hx) (efixedPoint f hf y hy) < ⊤
  change edistLtTopSetoid.Rel _ _
  -- ⊢ Setoid.Rel edistLtTopSetoid (efixedPoint f hf x hx) (efixedPoint f hf y hy)
  trans x
  -- ⊢ Setoid.Rel edistLtTopSetoid (efixedPoint f hf x hx) x
  · apply Setoid.symm' -- Porting note: Originally `symm`
    -- ⊢ Setoid.Rel edistLtTopSetoid x (efixedPoint f hf x hx)
    exact hf.edist_efixedPoint_lt_top hx
    -- 🎉 no goals
  trans y
  -- ⊢ Setoid.Rel edistLtTopSetoid x y
  exacts [lt_top_iff_ne_top.2 h, hf.edist_efixedPoint_lt_top hy]
  -- 🎉 no goals
#align contracting_with.efixed_point_eq_of_edist_lt_top ContractingWith.efixedPoint_eq_of_edist_lt_top

/-- Banach fixed-point theorem for maps contracting on a complete subset. -/
theorem exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    ∃ y ∈ s, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) := by
  haveI := hsc.completeSpace_coe
  -- ⊢ ∃ y, y ∈ s ∧ IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop (𝓝 y) ∧ ∀ (n : …
  rcases hf.exists_fixedPoint ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩
  -- ⊢ ∃ y, y ∈ s ∧ IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop (𝓝 y) ∧ ∀ (n : …
  refine' ⟨y, y.2, Subtype.ext_iff_val.1 hfy, _, fun n ↦ _⟩
  -- ⊢ Tendsto (fun n => f^[n] x) atTop (𝓝 ↑y)
  · convert (continuous_subtype_val.tendsto _).comp h_tendsto
    -- ⊢ f^[x✝] x = (Subtype.val ∘ fun n => (MapsTo.restrict f s s hsf)^[n] { val :=  …
    simp only [(· ∘ ·), MapsTo.iterate_restrict, MapsTo.val_restrict_apply]
    -- 🎉 no goals
  · convert hle n
    -- ⊢ edist (f^[n] x) ↑y = edist ((MapsTo.restrict f s s hsf)^[n] { val := x, prop …
    rw [MapsTo.iterate_restrict]
    -- ⊢ edist (f^[n] x) ↑y = edist (MapsTo.restrict f^[n] s s (_ : MapsTo f^[n] s s) …
    rfl
    -- 🎉 no goals
#align contracting_with.exists_fixed_point' ContractingWith.exists_fixedPoint'

variable (f)

-- avoid `efixedPoint _` in pretty printer
/-- Let `s` be a complete forward-invariant set of a self-map `f`. If `f` contracts on `s`
and `x ∈ s` satisfies `edist x (f x) ≠ ∞`, then `efixedPoint'` is the unique fixed point
of the restriction of `f` to `s ∩ EMetric.ball x ∞`. -/
noncomputable def efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) (x : α) (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    α :=
  Classical.choose <| hf.exists_fixedPoint' hsc hsf hxs hx
#align contracting_with.efixed_point' ContractingWith.efixedPoint'

variable {f}

theorem efixedPoint_mem' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    efixedPoint' f hsc hsf hf x hxs hx ∈ s :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).1
#align contracting_with.efixed_point_mem' ContractingWith.efixedPoint_mem'

theorem efixedPoint_isFixedPt' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    IsFixedPt f (efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.1
#align contracting_with.efixed_point_is_fixed_pt' ContractingWith.efixedPoint_isFixedPt'

theorem tendsto_iterate_efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.1
#align contracting_with.tendsto_iterate_efixed_point' ContractingWith.tendsto_iterate_efixedPoint'

theorem apriori_edist_iterate_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞)
    (n : ℕ) :
    edist (f^[n] x) (efixedPoint' f hsc hsf hf x hxs hx) ≤
      edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.2 n
#align contracting_with.apriori_edist_iterate_efixed_point_le' ContractingWith.apriori_edist_iterate_efixedPoint_le'

theorem edist_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) ≤ edist x (f x) / (1 - K) := by
  convert hf.apriori_edist_iterate_efixedPoint_le' hsc hsf hxs hx 0
  -- ⊢ edist x (f x) = edist x (f x) * ↑K ^ 0
  rw [pow_zero, mul_one]
  -- 🎉 no goals
#align contracting_with.edist_efixed_point_le' ContractingWith.edist_efixedPoint_le'

theorem edist_efixedPoint_lt_top' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) < ∞ :=
  (hf.edist_efixedPoint_le' hsc hsf hxs hx).trans_lt
    (ENNReal.mul_lt_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero)
#align contracting_with.edist_efixed_point_lt_top' ContractingWith.edist_efixedPoint_lt_top'

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
  refine' (hf.eq_or_edist_eq_top_of_fixedPoints _ _).elim id fun h' ↦ False.elim (ne_of_lt _ h')
    <;> try apply efixedPoint_isFixedPt'
        -- 🎉 no goals
        -- 🎉 no goals
        -- ⊢ edist (efixedPoint' f hsc hsf hfs x hxs hx) (efixedPoint' f htc htf hft y hy …
  change edistLtTopSetoid.Rel _ _
  -- ⊢ Setoid.Rel edistLtTopSetoid (efixedPoint' f hsc hsf hfs x hxs hx) (efixedPoi …
  trans x
  -- ⊢ Setoid.Rel edistLtTopSetoid (efixedPoint' f hsc hsf hfs x hxs hx) x
  · apply Setoid.symm' -- Porting note: Originally `symm`
    -- ⊢ Setoid.Rel edistLtTopSetoid x (efixedPoint' f hsc hsf hfs x hxs hx)
    apply edist_efixedPoint_lt_top'
    -- 🎉 no goals
  trans y
  -- ⊢ Setoid.Rel edistLtTopSetoid x y
  exact lt_top_iff_ne_top.2 hxy
  -- ⊢ Setoid.Rel edistLtTopSetoid y (efixedPoint' f htc htf hft y hyt hy)
  apply edist_efixedPoint_lt_top'
  -- 🎉 no goals
#align contracting_with.efixed_point_eq_of_edist_lt_top' ContractingWith.efixedPoint_eq_of_edist_lt_top'

end ContractingWith

namespace ContractingWith

variable [MetricSpace α] {K : ℝ≥0} {f : α → α} (hf : ContractingWith K f)

theorem one_sub_K_pos (hf : ContractingWith K f) : (0 : ℝ) < 1 - K :=
  sub_pos.2 hf.1
set_option linter.uppercaseLean3 false in
#align contracting_with.one_sub_K_pos ContractingWith.one_sub_K_pos

theorem dist_le_mul (x y : α) : dist (f x) (f y) ≤ K * dist x y :=
  hf.toLipschitzWith.dist_le_mul x y
#align contracting_with.dist_le_mul ContractingWith.dist_le_mul

theorem dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
  suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
    -- 🎉 no goals
  calc
    dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ ≤ dist x (f x) + dist y (f y) + K * dist x y := add_le_add_left (hf.dist_le_mul _ _) _
#align contracting_with.dist_inequality ContractingWith.dist_inequality

theorem dist_le_of_fixedPoint (x) {y} (hy : IsFixedPt f y) : dist x y ≤ dist x (f x) / (1 - K) := by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y
  -- 🎉 no goals
#align contracting_with.dist_le_of_fixed_point ContractingWith.dist_le_of_fixedPoint

theorem fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
  (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)
#align contracting_with.fixed_point_unique' ContractingWith.fixedPoint_unique'

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
theorem dist_fixedPoint_fixedPoint_of_dist_le' (g : α → α) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt g y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist x y ≤ C / (1 - K) :=
  calc
    dist x y = dist y x := dist_comm x y
    _ ≤ dist y (f y) / (1 - K) := (hf.dist_le_of_fixedPoint y hx)
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
                                         -- 🎉 no goals
    _ ≤ C / (1 - K) := (div_le_div_right hf.one_sub_K_pos).2 (hfg y)
#align contracting_with.dist_fixed_point_fixed_point_of_dist_le' ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'

variable [Nonempty α] [CompleteSpace α]

variable (f)

/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
noncomputable def fixedPoint : α :=
  efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)
#align contracting_with.fixed_point ContractingWith.fixedPoint

variable {f}

/-- The point provided by `ContractingWith.fixedPoint` is actually a fixed point. -/
theorem fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf) :=
  hf.efixedPoint_isFixedPt _
#align contracting_with.fixed_point_is_fixed_pt ContractingWith.fixedPoint_isFixedPt

theorem fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf :=
  hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt
#align contracting_with.fixed_point_unique ContractingWith.fixedPoint_unique

theorem dist_fixedPoint_le (x) : dist x (fixedPoint f hf) ≤ dist x (f x) / (1 - K) :=
  hf.dist_le_of_fixedPoint x hf.fixedPoint_isFixedPt
#align contracting_with.dist_fixed_point_le ContractingWith.dist_fixedPoint_le

/-- Aposteriori estimates on the convergence of iterates to the fixed point. -/
theorem aposteriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) ≤ dist (f^[n] x) (f^[n + 1] x) / (1 - K) := by
  rw [iterate_succ']
  -- ⊢ dist (f^[n] x) (fixedPoint f hf) ≤ dist (f^[n] x) ((f ∘ f^[n]) x) / (1 - ↑K)
  apply hf.dist_fixedPoint_le
  -- 🎉 no goals
#align contracting_with.aposteriori_dist_iterate_fixed_point_le ContractingWith.aposteriori_dist_iterate_fixedPoint_le

theorem apriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) ≤ dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  le_trans (hf.aposteriori_dist_iterate_fixedPoint_le x n) <|
    (div_le_div_right hf.one_sub_K_pos).2 <| hf.toLipschitzWith.dist_iterate_succ_le_geometric x n
#align contracting_with.apriori_dist_iterate_fixed_point_le ContractingWith.apriori_dist_iterate_fixedPoint_le

theorem tendsto_iterate_fixedPoint (x) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| fixedPoint f hf) := by
  convert tendsto_iterate_efixedPoint hf (edist_ne_top x _)
  -- ⊢ fixedPoint f hf = efixedPoint f hf x (_ : edist x (f x) ≠ ⊤)
  refine' (fixedPoint_unique _ _).symm
  -- ⊢ IsFixedPt f (efixedPoint f hf x (_ : edist x (f x) ≠ ⊤))
  apply efixedPoint_isFixedPt
  -- 🎉 no goals
#align contracting_with.tendsto_iterate_fixed_point ContractingWith.tendsto_iterate_fixedPoint

theorem fixedPoint_lipschitz_in_map {g : α → α} (hg : ContractingWith K g) {C}
    (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist (fixedPoint f hf) (fixedPoint g hg) ≤ C / (1 - K) :=
  hf.dist_fixedPoint_fixedPoint_of_dist_le' g hf.fixedPoint_isFixedPt hg.fixedPoint_isFixedPt hfg
#align contracting_with.fixed_point_lipschitz_in_map ContractingWith.fixedPoint_lipschitz_in_map

/-- If a map `f` has a contracting iterate `f^[n]`, then the fixed point of `f^[n]` is also a fixed
point of `f`. -/
theorem isFixedPt_fixedPoint_iterate {n : ℕ} (hf : ContractingWith K f^[n]) :
    IsFixedPt f (hf.fixedPoint f^[n]) := by
  set x := hf.fixedPoint f^[n]
  -- ⊢ IsFixedPt f x
  have hx : f^[n] x = x := hf.fixedPoint_isFixedPt
  -- ⊢ IsFixedPt f x
  have := hf.toLipschitzWith.dist_le_mul x (f x)
  -- ⊢ IsFixedPt f x
  rw [← iterate_succ_apply, iterate_succ_apply', hx] at this
  -- ⊢ IsFixedPt f x
  -- Porting note: Originally `contrapose! this`
  revert this
  -- ⊢ dist x (f x) ≤ ↑K * dist x (f x) → IsFixedPt f x
  contrapose!
  -- ⊢ ¬IsFixedPt f (fixedPoint f^[n] hf) → ↑K * dist (fixedPoint f^[n] hf) (f (fix …
  intro this
  -- ⊢ ↑K * dist (fixedPoint f^[n] hf) (f (fixedPoint f^[n] hf)) < dist (fixedPoint …
  have := dist_pos.2 (Ne.symm this)
  -- ⊢ ↑K * dist (fixedPoint f^[n] hf) (f (fixedPoint f^[n] hf)) < dist (fixedPoint …
  simpa only [NNReal.coe_one, one_mul, NNReal.val_eq_coe] using (mul_lt_mul_right this).mpr hf.left
  -- 🎉 no goals
#align contracting_with.is_fixed_pt_fixed_point_iterate ContractingWith.isFixedPt_fixedPoint_iterate

end ContractingWith

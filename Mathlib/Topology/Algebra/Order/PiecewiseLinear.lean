/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Piecewise linear interpolation

Given a grid `x : ℤ → K`, values `y : ℤ → E`, and slopes `c : ℤ → E`, this file defines
`piecewiseLinear x y c : K → E`, equal to `y n + (t - x n) • c n` on the cell
`[x n, x (n + 1))` where `n = gridIdx x t`. It is continuous when the step condition
`y (n + 1) = y n + (x (n + 1) - x n) • c n` holds, and has right derivative `c n` on each
cell.

For the value-based interpolant (slopes derived from consecutive values), use
`continuous_piecewiseLinear_ofValues`.

## Main definitions

* `gridIdx (x : ℤ → K) (t : K) : ℤ`: the index `n` such that `t ∈ Ico (x n) (x (n + 1))`
  when `x` tends to `±∞`.
* `piecewiseLinear (x : ℤ → K) (y c : ℤ → E) (t : K) : E`: the piecewise linear function.

## Main results

* `continuous_piecewiseLinear`: continuity under the step condition.
* `continuous_piecewiseLinear_ofValues`: continuity of the value-based interpolant.
* `hasDerivWithinAt_piecewiseLinear`: the right derivative on each cell is `c (gridIdx x t)`.

-/

@[expose] public section

open Set Filter

/-! ### Cell index for a grid tending to `±∞` -/

section GridIdx

variable {K : Type*} [LinearOrder K]

/-- The index of the cell containing `t` on a grid `x : ℤ → K`, defined as
`sSup {n : ℤ | x n ≤ t}`. When `x` tends to `±∞` (and `K` has no maximum),
`t ∈ Ico (x (gridIdx x t)) (x (gridIdx x t + 1))`. -/
noncomputable def gridIdx (x : ℤ → K) (t : K) : ℤ := sSup {n : ℤ | x n ≤ t}

/-- On a strictly monotone grid, `gridIdx x t = n` whenever `t ∈ Ico (x n) (x (n + 1))`. -/
theorem gridIdx_eq_of_mem_Ico {x : ℤ → K} (hx : StrictMono x)
    {n : ℤ} {t : K} (ht : t ∈ Ico (x n) (x (n + 1))) :
    gridIdx x t = n := by
  have hub : ∀ m, x m ≤ t → m ≤ n := fun m hm =>
    Int.lt_add_one_iff.mp (hx.lt_iff_lt.mp (hm.trans_lt ht.2))
  exact le_antisymm (csSup_le ⟨n, ht.1⟩ hub) (le_csSup ⟨n, hub⟩ ht.1)

/-- If `x : ℤ → K` tends to `±∞` (and `K` has no maximum), then `t` lies in the half-open
cell indexed by `gridIdx x t`. -/
theorem gridIdx_mem_Ico [NoMaxOrder K] {x : ℤ → K}
    (h_atTop : Tendsto x atTop atTop) (h_atBot : Tendsto x atBot atBot) (t : K) :
    t ∈ Ico (x (gridIdx x t)) (x (gridIdx x t + 1)) := by
  have hne : {n : ℤ | x n ≤ t}.Nonempty :=
    (h_atBot.eventually (eventually_le_atBot t)).exists
  obtain ⟨t', ht'⟩ := exists_gt t
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h_atTop.eventually (eventually_ge_atTop t'))
  have hba : BddAbove {n : ℤ | x n ≤ t} :=
    ⟨N, fun n hn => not_lt.mp fun hlt => not_lt.mpr hn (ht'.trans_le (hN n hlt.le))⟩
  refine ⟨Int.csSup_mem hne hba, lt_of_not_ge fun h => ?_⟩
  have : gridIdx x t + 1 ≤ gridIdx x t := le_csSup hba h
  omega

end GridIdx

/-! ### Continuity on a grid -/

section Grid

variable {K : Type*} [LinearOrder K] [TopologicalSpace K] [OrderTopology K]

/-- A function continuous on each cell `Icc (x n) (x (n + 1))` of a grid `x : ℤ → K`
tending to `±∞` is continuous. -/
theorem continuous_of_grid {E : Type*} [NoMaxOrder K] [NoMinOrder K]
    [TopologicalSpace E] {x : ℤ → K} {f : K → E}
    (h_atTop : Tendsto x atTop atTop) (h_atBot : Tendsto x atBot atBot)
    (hf : ∀ n : ℤ, ContinuousOn f (Icc (x n) (x (n + 1)))) :
    Continuous f := by
  have hshift : Tendsto (fun n : ℤ => x (n + 1)) atBot atBot :=
    h_atBot.comp (Filter.tendsto_atBot_add_const_right atBot 1 tendsto_id)
  refine (locallyFinite_Icc_of_tendsto h_atTop hshift).continuous
    (eq_univ_of_forall fun t => ?_) (fun _ => isClosed_Icc) hf
  obtain ⟨h1, h2⟩ := gridIdx_mem_Ico h_atTop h_atBot t
  exact mem_iUnion.mpr ⟨gridIdx x t, h1, h2.le⟩

/-- A function continuous on each cell `Icc (x n) (x (n + 1))` of a grid `x : ℤ → K`
over `[a, b]` is continuous on `Icc (x a) (x b)`. -/
theorem continuousOn_Icc_of_grid {E : Type*} [TopologicalSpace E] {x : ℤ → K} {f : K → E}
    {a b : ℤ} (hab : a ≤ b)
    (hf : ∀ n ∈ Ico a b, ContinuousOn f (Icc (x n) (x (n + 1)))) :
    ContinuousOn f (Icc (x a) (x b)) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [continuousOn_singleton]
  haveI : Finite (Ico a b : Set ℤ) := (finite_Ico a b).to_subtype
  refine (LocallyFinite.continuousOn_iUnion (g := f) (locallyFinite_of_finite _)
    (fun _ => isClosed_Icc) fun n : Ico a b => hf n.val n.2).mono
    fun t ht => mem_iUnion.mpr ?_
  set S := {n : ℤ | a ≤ n ∧ n + 1 ≤ b ∧ x n ≤ t}
  have hbdd : BddAbove S := ⟨b - 1, fun _ hn => by have := hn.2.1; omega⟩
  obtain ⟨h1, h2, h3⟩ := Int.csSup_mem (s := S) ⟨a, le_rfl, hlt, ht.1⟩ hbdd
  refine ⟨⟨sSup S, h1, by omega⟩, h3, ?_⟩
  rcases h2.lt_or_eq with _ | heq
  · exact not_lt.mp fun hgt => by
      have := le_csSup hbdd (show sSup S + 1 ∈ S from ⟨by omega, by omega, hgt.le⟩); omega
  · rw [heq]; exact ht.2

end Grid

/-! ### Piecewise linear interpolation -/

section PiecewiseLinear

variable {K : Type*} [Field K] [LinearOrder K]
  {E : Type*} [AddCommGroup E] [Module K E]
  {x : ℤ → K} {y c : ℤ → E}

/-- The piecewise linear function: on the cell `[x n, x (n + 1))`,
`piecewiseLinear x y c t = y n + (t - x n) • c n` where `n = gridIdx x t`. -/
noncomputable def piecewiseLinear (x : ℤ → K) (y c : ℤ → E) (t : K) : E :=
  letI n := gridIdx x t
  y n + (t - x n) • c n

/-- Closed form for `piecewiseLinear` on the `n`-th cell. -/
theorem piecewiseLinear_eq_on_Ico (hx : StrictMono x) {n : ℤ} {t : K}
    (ht : t ∈ Ico (x n) (x (n + 1))) :
    piecewiseLinear x y c t = y n + (t - x n) • c n := by
  simp [piecewiseLinear, gridIdx_eq_of_mem_Ico hx ht]

/-- `piecewiseLinear` at a grid point equals `y n`. -/
@[simp]
theorem piecewiseLinear_apply_grid (hx : StrictMono x) (n : ℤ) :
    piecewiseLinear x y c (x n) = y n := by
  rw [piecewiseLinear_eq_on_Ico hx ⟨le_rfl, hx (lt_add_one n)⟩, sub_self, zero_smul, add_zero]

section Continuity

variable [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E]

/-- Under the step condition `y (n + 1) = y n + (x (n + 1) - x n) • c n`, the piecewise
linear function is continuous. -/
theorem continuous_piecewiseLinear (hx : StrictMono x)
    (h_atTop : Tendsto x atTop atTop) (h_atBot : Tendsto x atBot atBot)
    (hstep : ∀ n : ℤ, y (n + 1) = y n + (x (n + 1) - x n) • c n) :
    Continuous (piecewiseLinear x y c) :=
  continuous_of_grid h_atTop h_atBot fun n => by
    refine (show ContinuousOn (fun t => y n + (t - x n) • c n) _ from by fun_prop).congr ?_
    rintro t ht
    rcases eq_or_lt_of_le ht.2 with rfl | h_lt
    · rw [piecewiseLinear_apply_grid hx (n + 1), hstep n]
    · exact piecewiseLinear_eq_on_Ico hx ⟨ht.1, h_lt⟩

/-- The piecewise linear interpolant of values `y` on a grid `x`, with slopes computed
from consecutive values, is continuous. -/
theorem continuous_piecewiseLinear_ofValues (hx : StrictMono x)
    (h_atTop : Tendsto x atTop atTop) (h_atBot : Tendsto x atBot atBot) :
    Continuous (piecewiseLinear x y
      (fun n => (x (n + 1) - x n)⁻¹ • (y (n + 1) - y n))) := by
  refine continuous_piecewiseLinear hx h_atTop h_atBot fun n => ?_
  have hne : x (n + 1) - x n ≠ 0 := sub_ne_zero.mpr (hx (lt_add_one n)).ne'
  rw [smul_inv_smul₀ hne]; abel

end Continuity

end PiecewiseLinear

/-! ### Derivative of piecewise linear functions -/

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {x : ℤ → ℝ} {y c : ℤ → E}

/-- The right derivative of the piecewise linear function at `t` is the slope
`c (gridIdx x t)` of the cell containing `t`. -/
theorem hasDerivWithinAt_piecewiseLinear (hx : StrictMono x)
    (h_atTop : Tendsto x atTop atTop) (h_atBot : Tendsto x atBot atBot) {t : ℝ} :
    HasDerivWithinAt (piecewiseLinear x y c) (c (gridIdx x t)) (Ici t) t := by
  obtain ⟨h1, h2⟩ := gridIdx_mem_Ico h_atTop h_atBot t
  set n := gridIdx x t
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t).sub_const (x n) |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT h2] with s hs
        exact piecewiseLinear_eq_on_Ico hx ⟨h1.trans hs.1.le, hs.2⟩)
      (by simp [piecewiseLinear, n]) |>.congr_deriv (one_smul _ _))

end Deriv

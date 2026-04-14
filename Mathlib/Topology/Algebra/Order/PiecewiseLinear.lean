/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Piecewise linear interpolation on regular grids

Given a sequence of values `y : ℤ → E` and slopes `c : ℤ → E` on a regular grid with
step size `h > 0` starting at `a`, this file defines piecewise linear interpolation
using `toIcoDiv` from `Mathlib.Algebra.Order.ToIntervalMod` to assign each point to its
grid cell.

## Main definitions

* `piecewiseLinear y c hh a t`: the piecewise linear interpolation, equal to
  `y n + (t - (a + n • h)) • c n` on cell `n = toIcoDiv hh a t`.

## Main results

* `piecewiseLinear_eq_on_Ico`: evaluation on the `n`-th cell.
* `piecewiseLinear_apply_grid`: evaluation at grid points.
* `piecewiseLinear_continuous`: continuity (given the step condition).
* `piecewiseLinear_hasDerivWithinAt`: the right derivative is `c (toIcoDiv hh a t)`.

-/

@[expose] public section

open Set Filter

/-! ### Locally finite regular grid -/

section RegularGrid

variable {K : Type*} [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K] [Archimedean K]
  [TopologicalSpace K] [OrderTopology K]

/-- The regular grid `[a + n • h, a + (n + 1) • h]` is locally finite when `h > 0`. -/
theorem locallyFinite_Icc_regularGrid {h : K} (hh : 0 < h) (a : K) :
    LocallyFinite fun n : ℤ => Icc (a + n • h) (a + (n + 1) • h) := by
  intro x
  set n := toIcoDiv hh a x
  obtain ⟨ha1, ha2⟩ := sub_toIcoDiv_zsmul_mem_Ico hh a x
  refine ⟨Ioo (x - h) (x + h), Ioo_mem_nhds (sub_lt_self x hh) (lt_add_of_pos_right x hh),
    (Set.finite_Icc (n - 1) (n + 1)).subset fun m ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩ => ⟨?_, ?_⟩⟩
  · suffices n - 1 < m + 1 by omega
    simp only [← zsmul_lt_zsmul_iff_left hh, sub_one_zsmul, add_one_zsmul] at hz2 ⊢
    grind
  · suffices m < n + 2 by omega
    simp only [← zsmul_lt_zsmul_iff_left hh, add_one_zsmul, (by ring : (n + 2 : ℤ) = n + 1 + 1)]
    grind

/-- A function continuous on each cell of a regular grid is continuous. -/
theorem continuous_of_regularGrid {E : Type*} [TopologicalSpace E]
    {f : K → E} {h : K} (hh : 0 < h) {a : K}
    (hf : ∀ n : ℤ, ContinuousOn f (Icc (a + n • h) (a + (n + 1) • h))) :
    Continuous f :=
  (locallyFinite_Icc_regularGrid hh a).continuous
    (iUnion_Icc_add_zsmul hh a) (fun _ => isClosed_Icc) hf

end RegularGrid

/-! ### Piecewise linear interpolation -/

section PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {y : ℤ → E} {c : ℤ → E} {h : ℝ} {a : ℝ}

/-- The piecewise linear interpolation of a sequence `y` with slopes `c` on a regular grid
with step size `h > 0` starting at `a`. On the `n`-th cell `[a + n • h, a + (n + 1) • h)`,
the value is `y n + (t - (a + n • h)) • c n`, where `n = toIcoDiv hh a t`. -/
noncomputable def piecewiseLinear (y : ℤ → E) (c : ℤ → E) {h : ℝ} (hh : 0 < h)
    (a : ℝ) (t : ℝ) : E :=
  let n := toIcoDiv hh a t
  y n + (t - (a + n • h)) • c n

/-- The piecewise linear interpolation at a regular grid point equals `y n`. -/
@[simp]
theorem piecewiseLinear_apply_grid (hh : 0 < h) (a : ℝ) (n : ℤ) :
    piecewiseLinear y c hh a (a + n * h) = y n := by
  simp [piecewiseLinear, zsmul_eq_mul]

/-- The piecewise linear interpolation equals `y n + (t - (a + n • h)) • c n`
on `[a + n • h, a + (n + 1) • h)`. -/
theorem piecewiseLinear_eq_on_Ico (hh : 0 < h) {n : ℤ} {t : ℝ}
    (ht : t ∈ Ico (a + n • h) (a + (n + 1) • h)) :
    piecewiseLinear y c hh a t = y n + (t - (a + n • h)) • c n := by
  have hmem : t - n • h ∈ Ico a (a + h) := by grind
  simp [piecewiseLinear, (toIcoDiv_eq_iff hh).mpr hmem]

/-- A piecewise linear function whose grid values satisfy `y (n + 1) = y n + h • c n`
is continuous. -/
theorem continuous_piecewiseLinear (hh : 0 < h)
    (hstep : ∀ n : ℤ, y (n + 1) = y n + h • c n) :
    Continuous (piecewiseLinear y c hh a) :=
  continuous_of_regularGrid hh fun n => by
    refine (show ContinuousOn (fun t => y n + (t - (a + n • h)) • c n) _ by fun_prop).congr ?_
    rintro t ht
    rcases eq_or_lt_of_le ht.2 with rfl | h_lt
    · simp only [zsmul_eq_mul]
      rw [piecewiseLinear_apply_grid hh a (n + 1), hstep n]
      push_cast; module
    · exact piecewiseLinear_eq_on_Ico hh ⟨ht.1, h_lt⟩

/-- The right derivative of the piecewise linear function is the piecewise constant slope
`c (toIcoDiv hh a t)`. -/
theorem piecewiseLinear_hasDerivWithinAt (hh : 0 < h) {t : ℝ} :
    HasDerivWithinAt (piecewiseLinear y c hh a)
      (c (toIcoDiv hh a t)) (Ici t) t := by
  obtain ⟨h1, h2⟩ := sub_toIcoDiv_zsmul_mem_Ico hh a t
  set n := toIcoDiv hh a t
  simp only [zsmul_eq_mul] at h1 h2
  have hlt : t < a + (n + 1) • h := by
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]; linarith
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t).sub_const (a + n • h) |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT hlt] with x hx
        exact piecewiseLinear_eq_on_Ico hh ⟨by simp only [zsmul_eq_mul]; linarith [hx.1], hx.2⟩)
      (by simp [piecewiseLinear, n]) |>.congr_deriv (one_smul _ _))

end PiecewiseLinear

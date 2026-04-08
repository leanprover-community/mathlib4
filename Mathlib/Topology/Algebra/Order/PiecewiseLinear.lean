/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Topology.Algebra.Order.Floor
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
* `piecewiseLinear_continuousOn`: continuity on `[a, ∞)`.
* `piecewiseLinear_hasDerivWithinAt`: the right derivative is `c (toIcoDiv hh a t)`.

-/

@[expose] public section

open Set Filter

/-! ### Locally finite regular grid -/

section RegularGrid

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [OrderTopology K]

/-- The regular grid `[a + n * h, a + (n + 1) * h]` is locally finite when `h > 0`. -/
theorem locallyFinite_Icc_regularGrid {h : K} (hh : 0 < h) (a : K) :
    LocallyFinite fun n : ℕ => Icc (a + n * h) (a + (↑n + 1) * h) := by
  intro x
  refine ⟨Ioo (x - h) (x + h), Ioo_mem_nhds (by linarith) (by linarith),
    (finite_Icc (⌊(x - h - a) / h⌋₊) (⌈(x + h - a) / h⌉₊)).subset ?_⟩
  rintro n ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩
  refine ⟨Nat.lt_add_one_iff.mp ((Nat.floor_lt' (by linarith)).mpr ?_),
    Nat.cast_le.mp ((?_ : (n : K) ≤ _).trans (Nat.le_ceil _))⟩ <;>
    (first | rw [div_lt_iff₀ hh] | rw [le_div_iff₀ hh]) <;> push_cast <;> nlinarith

/-- A function continuous on each regular grid cell is continuous on `[a, ∞)`. -/
theorem ContinuousOn.of_regularGrid {E : Type*} [TopologicalSpace E]
    {f : K → E} {h : K} (hh : 0 < h) {a : K}
    (hf : ∀ n : ℕ, ContinuousOn f (Icc (a + n * h) (a + (n + 1) * h))) :
    ContinuousOn f (Ici a) := by
  apply ((locallyFinite_Icc_regularGrid hh a).continuousOn_iUnion
    (fun _ => isClosed_Icc) (hf ·)).mono
  intro t (hat : a ≤ t)
  refine mem_iUnion.mpr ⟨⌊(t - a) / h⌋₊, Ico_subset_Icc_self ⟨?_, ?_⟩⟩
  · nlinarith [Nat.floor_le (div_nonneg (sub_nonneg.mpr hat) hh.le),
      mul_div_cancel₀ (t - a) hh.ne']
  · nlinarith [Nat.lt_floor_add_one ((t - a) / h), mul_div_cancel₀ (t - a) hh.ne']

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
theorem piecewiseLinear_apply_grid (hh : 0 < h) (a : ℝ) (n : ℤ) :
    piecewiseLinear y c hh a (a + n • h) = y n := by
  have : toIcoDiv hh a (a + n • h) = n := by
    rw [toIcoDiv_eq_iff hh]; simp [hh]
  simp [piecewiseLinear, zsmul_eq_mul]

/-- The piecewise linear interpolation equals `y n + (t - (a + n • h)) • c n`
on `[a + n • h, a + (n + 1) • h)`. -/
theorem piecewiseLinear_eq_on_Ico (hh : 0 < h) {n : ℤ} {t : ℝ}
    (ht : t ∈ Ico (a + n • h) (a + (n + 1) • h)) :
    piecewiseLinear y c hh a t = y n + (t - (a + n • h)) • c n := by
  have hmem : t - n • h ∈ Ico a (a + h) := by grind
  simp [piecewiseLinear, (toIcoDiv_eq_iff hh).mpr hmem]

/-- A piecewise linear function whose grid values satisfy `y (n + 1) = y n + h • c n`
is continuous on `[a, ∞)`. -/
theorem piecewiseLinear_continuousOn (hh : 0 < h)
    (hstep : ∀ n : ℤ, y (n + 1) = y n + h • c n) :
    ContinuousOn (piecewiseLinear y c hh a) (Ici a) := by
  apply ContinuousOn.of_regularGrid hh; intro n
  apply (show ContinuousOn (fun t => y (↑n : ℤ) + (t - (a + (↑n : ℤ) • h)) • c ↑n) _ by
    fun_prop).congr
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | h_lt
  · have : a + (↑n + 1) * h = a + ((↑n : ℤ) + 1) • h := by simp [zsmul_eq_mul]
    rw [this, piecewiseLinear_apply_grid hh a ((↑n : ℤ) + 1), hstep ↑n]
    simp [zsmul_eq_mul]; ring_nf
  · exact piecewiseLinear_eq_on_Ico hh
      (show t ∈ Ico (a + (↑n : ℤ) • h) (a + ((↑n : ℤ) + 1) • h) by
        simp only [zsmul_eq_mul, Int.cast_natCast, mem_Ico] at ht h_lt ⊢
        exact ⟨ht.1, by push_cast at h_lt ⊢; linarith⟩)

/-- The right derivative of the piecewise linear function is the piecewise constant slope
`c (toIcoDiv hh a t)`. -/
theorem piecewiseLinear_hasDerivWithinAt (hh : 0 < h) {t : ℝ} (_hat : a ≤ t) :
    HasDerivWithinAt (piecewiseLinear y c hh a)
      (c (toIcoDiv hh a t)) (Ici t) t := by
  set n := toIcoDiv hh a t
  set tn := a + n • h with htn_def
  obtain ⟨h1, h2⟩ := sub_toIcoDiv_zsmul_mem_Ico hh a t
  simp only [zsmul_eq_mul] at h1 h2
  have htn : tn ≤ t := by simp only [htn_def, zsmul_eq_mul]; linarith
  have hlt : t < a + (n + 1) • h := by
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]; linarith
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t |>.sub_const tn |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT hlt] with x hx
        exact piecewiseLinear_eq_on_Ico hh ⟨by linarith [hx.1], hx.2⟩)
      (by simp [piecewiseLinear, n, tn])).congr_deriv (one_smul _ _))

end PiecewiseLinear

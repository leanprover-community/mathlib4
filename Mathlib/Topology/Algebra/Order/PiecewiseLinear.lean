/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Piecewise linear and constant interpolation on regular grids

Given a sequence of values `y` and slopes `c` on a regular grid with step size `h > 0`
starting at `a`, this file defines:

* `piecewiseLinear y c h a t`: the piecewise linear interpolation, equal to
  `y n + (t - (a + n * h)) • c n` on `[a + n * h, a + (n + 1) * h)`.
* `piecewiseConst c h a t`: the piecewise constant function taking value `c n` on
  `[a + n * h, a + (n + 1) * h)`.

## Main results

* `piecewiseConst_eq_on_Ico`: `piecewiseConst c h a t = c n` on the `n`-th cell.
* `piecewiseLinear_apply_grid`: `piecewiseLinear y c h a (a + n * h) = y n`.
* `piecewiseLinear_eq_on_Ico`: evaluation on the `n`-th cell.
* `piecewiseLinear_continuousOn`: continuity on `[a, ∞)` when `y (n+1) = y n + h • c n`.
* `piecewiseLinear_hasDerivWithinAt`: the right derivative of the piecewise linear function
  is the piecewise constant slope.

-/

@[expose] public section

open Set

variable {α : Type*} [Field α] [LinearOrder α] [FloorSemiring α] [IsStrictOrderedRing α]

/-- The piecewise linear interpolation of a sequence `y` with slopes `c` on a regular grid
with step size `h` starting at `a`. On `[a + n * h, a + (n + 1) * h)`, the value is
`y n + (t - (a + n * h)) • c n`. -/
def piecewiseLinear {E : Type*} [AddCommGroup E] [Module α E]
    (y : ℕ → E) (c : ℕ → E) (h : α) (a : α) (t : α) : E :=
  let n := ⌊(t - a) / h⌋₊
  y n + (t - (a + n * h)) • c n

/-- The piecewise constant function taking value `c n` on `[a + n * h, a + (n + 1) * h)`. -/
def piecewiseConst {E : Type*} (c : ℕ → E) (h : α) (a : α) (t : α) : E :=
  c ⌊(t - a) / h⌋₊

/-- The piecewise constant function equals `c n` on `[a + n * h, a + (n + 1) * h)`. -/
theorem piecewiseConst_eq_on_Ico {E : Type*} {c : ℕ → E} {h : α} {a : α}
    (hh : 0 < h) {n : ℕ} {t : α}
    (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    piecewiseConst c h a t = c n := by
  simp [piecewiseConst, Nat.floor_div_eq_of_mem_Ico hh ht]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {y : ℕ → E} {c : ℕ → E} {h : ℝ} {a : ℝ}

/-- The piecewise linear interpolation at a grid point `a + n * h` equals `y n`. -/
theorem piecewiseLinear_apply_grid (hh : 0 < h) (a : ℝ) (n : ℕ) :
    piecewiseLinear y c h a (a + n * h) = y n := by
  simp [piecewiseLinear, hh.ne']

/-- The piecewise linear interpolation equals `y n + (t - (a + n * h)) • c n`
on `[a + n * h, a + (n + 1) * h)`. -/
theorem piecewiseLinear_eq_on_Ico (hh : 0 < h) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    piecewiseLinear y c h a t = y n + (t - (a + n * h)) • c n := by
  simp [piecewiseLinear, Nat.floor_div_eq_of_mem_Ico hh ht]

/-- A piecewise linear function whose grid values satisfy `y (n + 1) = y n + h • c n`
is continuous on `[a, ∞)`. -/
theorem piecewiseLinear_continuousOn (hh : 0 < h)
    (hstep : ∀ n, y (n + 1) = y n + h • c n) :
    ContinuousOn (piecewiseLinear y c h a) (Ici a) := by
  apply ContinuousOn.of_Icc_grid hh; intro n
  apply (show ContinuousOn (fun t => y n + (t - (a + n * h)) • c n) _ by fun_prop).congr
  intro t ht; rcases eq_or_lt_of_le ht.2 with rfl | h_lt
  · norm_cast
    rw [piecewiseLinear_apply_grid hh a (n + 1), hstep]
    module
  · exact piecewiseLinear_eq_on_Ico hh ⟨ht.1, h_lt⟩

/-- The right derivative of a piecewise linear function is the piecewise constant slope. -/
theorem piecewiseLinear_hasDerivWithinAt (hh : 0 < h) {t : ℝ} (hat : a ≤ t) :
    HasDerivWithinAt (piecewiseLinear y c h a)
      (piecewiseConst c h a t) (Ici t) t := by
  set n := ⌊(t - a) / h⌋₊; set tn := a + n * h
  obtain ⟨h1, h2⟩ := mem_Ico_Nat_floor_div hh hat
  simp only [piecewiseConst]
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t |>.sub_const tn |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT h2] with x hx
        exact piecewiseLinear_eq_on_Ico hh ⟨h1.trans hx.1.le, hx.2⟩)
      (by simp [piecewiseLinear, n, tn])).congr_deriv (one_smul _ _))

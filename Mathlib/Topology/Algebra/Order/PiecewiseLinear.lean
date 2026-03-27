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
# Piecewise linear and constant interpolation

Given grid points `grid : ℕ → α`, a cell index function `cellOf : α → ℕ`, a sequence of
values `y : ℕ → E`, and slopes `c : ℕ → E`, this file defines:

* `piecewiseConst c cellOf t`: the piecewise constant function, equal to `c (cellOf t)`.
* `piecewiseLinear y c grid cellOf t`: the piecewise linear interpolation, equal to
  `y n + (t - grid n) • c n` where `n = cellOf t`.

## Grid covers

* `locallyFinite_Icc_of_strictMono_tendsto`: cells `[g n, g (n+1)]` of a strictly monotone
  sequence tending to `+∞` form a locally finite family.
* `ContinuousOn.of_Icc_cover`: a function continuous on each cell of a locally finite grid
  cover is continuous on any covered subset.

## Regular grids

For a regular grid with step `h > 0` starting at `a`, where `grid n = a + n * h` and
`cellOf t = ⌊(t - a) / h⌋₊`:

* `piecewiseConst_regularGrid_eq_on_Ico`: value on the `n`-th cell.
* `piecewiseLinear_regularGrid_apply_grid`: evaluation at grid points.
* `piecewiseLinear_regularGrid_eq_on_Ico`: evaluation on the `n`-th cell.
* `piecewiseLinear_regularGrid_continuousOn`: continuity on `[a, ∞)`.
* `piecewiseLinear_regularGrid_hasDerivWithinAt`: right derivative is the piecewise constant slope.
-/

@[expose] public section

open Set Filter

/-! ### Definitions -/

/-- The piecewise constant function with cell index `cellOf`: returns `c (cellOf t)`. -/
def piecewiseConst {α E : Type*} (c : ℕ → E) (cellOf : α → ℕ) (t : α) : E :=
  c (cellOf t)

/-- The piecewise linear interpolation on a grid. On the cell determined by `cellOf t = n`,
returns `y n + (t - grid n) • c n`. -/
def piecewiseLinear {α E : Type*} [Ring α] [AddCommGroup E] [Module α E]
    (y : ℕ → E) (c : ℕ → E) (grid : ℕ → α) (cellOf : α → ℕ) (t : α) : E :=
  let n := cellOf t
  y n + (t - grid n) • c n

/-! ### Basic evaluation -/

@[simp]
theorem piecewiseConst_apply {α E : Type*} {c : ℕ → E} {cellOf : α → ℕ} {t : α} :
    piecewiseConst c cellOf t = c (cellOf t) := rfl

theorem piecewiseConst_of_cellOf_eq {α E : Type*} {c : ℕ → E} {cellOf : α → ℕ}
    {n : ℕ} {t : α} (h : cellOf t = n) :
    piecewiseConst c cellOf t = c n := by
  simp [h]

theorem piecewiseLinear_of_cellOf_eq {α E : Type*} [Ring α] [AddCommGroup E] [Module α E]
    {y c : ℕ → E} {grid : ℕ → α} {cellOf : α → ℕ}
    {n : ℕ} {t : α} (h : cellOf t = n) :
    piecewiseLinear y c grid cellOf t = y n + (t - grid n) • c n := by
  simp [piecewiseLinear, h]

/-! ### Locally finite grid covers -/

section GridCovers

variable {K : Type*} [LinearOrder K] [TopologicalSpace K] [OrderTopology K]

/-- Cells `[g n, g (n+1)]` of a strictly monotone sequence tending to `+∞` form a locally
finite family. -/
theorem locallyFinite_Icc_of_strictMono_tendsto {g : ℕ → K}
    (hg : StrictMono g) (hg_top : Tendsto g atTop atTop) :
    LocallyFinite fun n => Icc (g n) (g (n + 1)) := by
  intro x
  obtain ⟨M, hM⟩ := (hg_top.eventually (Ici_mem_atTop x)).exists
  refine ⟨Iio (g (M + 1)), Iio_mem_nhds (lt_of_le_of_lt hM (hg (Nat.lt_succ_self M))),
    (Finset.range (M + 1)).finite_toSet.subset fun n hn => ?_⟩
  simp only [Finset.coe_range, mem_Iio]
  obtain ⟨z, hz_cell, hz_nbhd⟩ := hn
  exact hg.lt_iff_lt.mp (lt_of_le_of_lt hz_cell.1 hz_nbhd)

/-- A function continuous on each cell `[g n, g (n+1)]` of a locally finite grid cover is
continuous on any subset covered by the cells. -/
theorem ContinuousOn.of_Icc_cover {E : Type*} [TopologicalSpace E]
    {f : K → E} {g : ℕ → K} {S : Set K}
    (hlf : LocallyFinite fun n => Icc (g n) (g (n + 1)))
    (hcover : S ⊆ ⋃ n, Icc (g n) (g (n + 1)))
    (hf : ∀ n, ContinuousOn f (Icc (g n) (g (n + 1)))) :
    ContinuousOn f S :=
  (hlf.continuousOn_iUnion (fun _ => isClosed_Icc) hf).mono hcover

end GridCovers

/-! ### General piecewise linear continuity and derivative -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {y : ℕ → E} {c : ℕ → E} {grid : ℕ → ℝ} {cellOf : ℝ → ℕ}

/-- A piecewise linear function is continuous on a set covered by a locally finite grid,
provided that `cellOf` correctly identifies the cell on each half-open interval, that
`cellOf` agrees at grid points, and that the grid values satisfy the step condition
`y (n + 1) = y n + (grid (n + 1) - grid n) • c n`. -/
theorem piecewiseLinear_continuousOn {S : Set ℝ}
    (hlf : LocallyFinite fun n => Icc (grid n) (grid (n + 1)))
    (hcover : S ⊆ ⋃ n, Icc (grid n) (grid (n + 1)))
    (hcellOf : ∀ n t, t ∈ Ico (grid n) (grid (n + 1)) → cellOf t = n)
    (hcellOf_grid : ∀ n, cellOf (grid n) = n)
    (hstep : ∀ n, y (n + 1) = y n + (grid (n + 1) - grid n) • c n) :
    ContinuousOn (piecewiseLinear y c grid cellOf) S := by
  apply ContinuousOn.of_Icc_cover hlf hcover
  intro n
  apply (show ContinuousOn (fun t => y n + (t - grid n) • c n) _ by fun_prop).congr
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | h_lt
  · rw [piecewiseLinear_of_cellOf_eq (hcellOf_grid (n + 1)), sub_self, zero_smul, add_zero]
    exact hstep n
  · exact piecewiseLinear_of_cellOf_eq (hcellOf n t ⟨ht.1, h_lt⟩)

/-- The right derivative of a piecewise linear function is the piecewise constant slope,
provided that `cellOf` correctly identifies the cell containing `t`. -/
theorem piecewiseLinear_hasDerivWithinAt {t : ℝ}
    (ht : t ∈ Ico (grid (cellOf t)) (grid (cellOf t + 1)))
    (hcellOf : ∀ s, s ∈ Ico (grid (cellOf t)) (grid (cellOf t + 1)) → cellOf s = cellOf t) :
    HasDerivWithinAt (piecewiseLinear y c grid cellOf)
      (piecewiseConst c cellOf t) (Ici t) t := by
  set n := cellOf t
  set gn := grid n
  simp only [piecewiseConst_apply]
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t |>.sub_const gn |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT ht.2] with x hx
        exact piecewiseLinear_of_cellOf_eq (hcellOf x ⟨ht.1.trans hx.1.le, hx.2⟩))
      (by rfl)).congr_deriv (one_smul _ _))

end General

/-! ### Regular grid -/

section RegularGrid

variable {K : Type*} [Field K] [LinearOrder K] [FloorSemiring K] [IsStrictOrderedRing K]
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
    ContinuousOn f (Ici a) :=
  ((locallyFinite_Icc_regularGrid hh a).continuousOn_iUnion
    (fun _ => isClosed_Icc) (hf ·)).mono
    fun t (hat : a ≤ t) =>
      mem_iUnion.mpr ⟨_, Ico_subset_Icc_self ((Nat.floor_div_eq_iff_mem_Ico hh hat).mp rfl)⟩

end RegularGrid

/-! ### Regular grid piecewise evaluation -/

section RegularGridPiecewise

variable {α : Type*} [Field α] [LinearOrder α] [FloorSemiring α] [IsStrictOrderedRing α]

/-- The piecewise constant function on a regular grid equals `c n` on the `n`-th cell. -/
theorem piecewiseConst_regularGrid_eq_on_Ico {E : Type*} {c : ℕ → E} {h : α} {a : α}
    (hh : 0 < h) {n : ℕ} {t : α}
    (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    piecewiseConst c (fun t => ⌊(t - a) / h⌋₊) t = c n := by
  have hat : a ≤ t := le_trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hh.le)) ht.1
  simp [piecewiseConst, (Nat.floor_div_eq_iff_mem_Ico hh hat).mpr ht]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {y : ℕ → E} {c : ℕ → E} {h : ℝ} {a : ℝ}

/-- The piecewise linear interpolation at a regular grid point equals `y n`. -/
theorem piecewiseLinear_regularGrid_apply_grid (hh : 0 < h) (a : ℝ) (n : ℕ) :
    piecewiseLinear y c (fun k => a + ↑k * h) (fun t => ⌊(t - a) / h⌋₊) (a + ↑n * h) =
      y n := by
  simp [piecewiseLinear, hh.ne']

/-- The piecewise linear interpolation on a regular grid equals
`y n + (t - (a + n * h)) • c n` on `[a + n * h, a + (n + 1) * h)`. -/
theorem piecewiseLinear_regularGrid_eq_on_Ico (hh : 0 < h) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (a + ↑n * h) (a + (↑n + 1) * h)) :
    piecewiseLinear y c (fun k => a + ↑k * h) (fun t => ⌊(t - a) / h⌋₊) t =
      y n + (t - (a + ↑n * h)) • c n := by
  have hat : a ≤ t := le_trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hh.le)) ht.1
  simp [piecewiseLinear, (Nat.floor_div_eq_iff_mem_Ico hh hat).mpr ht]

/-- A piecewise linear function on a regular grid whose grid values satisfy
`y (n + 1) = y n + h • c n` is continuous on `[a, ∞)`. -/
theorem piecewiseLinear_regularGrid_continuousOn (hh : 0 < h)
    (hstep : ∀ n, y (n + 1) = y n + h • c n) :
    ContinuousOn (piecewiseLinear y c (fun k => a + ↑k * h) (fun t => ⌊(t - a) / h⌋₊))
      (Ici a) := by
  apply ContinuousOn.of_regularGrid hh; intro n
  apply (show ContinuousOn (fun t => y n + (t - (a + ↑n * h)) • c n) _ by fun_prop).congr
  intro t ht; rcases eq_or_lt_of_le ht.2 with rfl | h_lt
  · norm_cast
    rw [piecewiseLinear_regularGrid_apply_grid hh a (n + 1), hstep]
    module
  · exact piecewiseLinear_regularGrid_eq_on_Ico hh ⟨ht.1, h_lt⟩

/-- The right derivative of the piecewise linear function on a regular grid is the
piecewise constant slope. -/
theorem piecewiseLinear_regularGrid_hasDerivWithinAt (hh : 0 < h) {t : ℝ} (hat : a ≤ t) :
    HasDerivWithinAt (piecewiseLinear y c (fun k => a + ↑k * h) (fun t => ⌊(t - a) / h⌋₊))
      (piecewiseConst c (fun t => ⌊(t - a) / h⌋₊) t) (Ici t) t := by
  set n := ⌊(t - a) / h⌋₊; set tn := a + ↑n * h
  obtain ⟨h1, h2⟩ := (Nat.floor_div_eq_iff_mem_Ico hh hat).mp rfl
  simp only [piecewiseConst_apply]
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t |>.sub_const tn |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT h2] with x hx
        exact piecewiseLinear_regularGrid_eq_on_Ico hh ⟨h1.trans hx.1.le, hx.2⟩)
      (by simp [piecewiseLinear, n, tn])).congr_deriv (one_smul _ _))

end RegularGridPiecewise

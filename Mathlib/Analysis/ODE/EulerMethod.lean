/-
Copyright (c) 2025 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Algebra.Order.PiecewiseLinear

/-!
# Forward Euler Method

We define the explicit (forward) Euler method for ODEs and prove that it converges
to the true solution as the step size `h → 0⁺`.

Given an ODE `y'(t) = v(t, y(t))`, `y(t₀) = y₀`, where `v : ℝ → E → E` is a vector field
on a normed space `E`, the Euler method produces a piecewise linear approximation by:

1. Computing Euler points: `y₀, y₁ = y₀ + h • v(t₀, y₀), ...`
2. Interpolating linearly between consecutive points.

## Main definitions

* `ODE.EulerMethod.step`: A single Euler step `y + h • v(t, y)`.
* `ODE.EulerMethod.point`: The sequence of Euler points.
* `ODE.EulerMethod.slope`: The slope `v(tₙ, yₙ)` on the `n`-th cell.
* `ODE.EulerMethod.path`: The piecewise linear Euler path.
* `ODE.EulerMethod.deriv`: The piecewise constant right derivative.

## Main results

* `ODE.EulerMethod.dist_deriv_le`: The local truncation error is bounded by `h * (L + K * M)`.
* `ODE.EulerMethod.dist_path_le`: The global error is bounded by
  `gronwallBound 0 K (h*(L+K*M)) (t-t₀)`.
* `ODE.EulerMethod.tendsto_path`: The Euler path converges to the true solution as `h → 0⁺`.

## Assumptions

The convergence proof assumes:
- `v` is `K`-Lipschitz in `y` (space) and `L`-Lipschitz in `t` (time)
- `‖v(t, y)‖ ≤ M` for all `t, y` (bounded vector field)
- The true solution `sol` is continuous on `[t₀, T]` with the correct initial condition
  and right derivative

-/

@[expose] public section

open Set Filter

namespace ODE.EulerMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single step of the explicit Euler method: `y + h • v(t, y)`. -/
def step {𝕜 : Type*} {E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : 𝕜 → E → E) (h : 𝕜) (t : 𝕜) (y : E) : E :=
  y + h • v t y

/-- The sequence of Euler points, defined recursively:
`point v h t₀ y₀ 0 = y₀` and
`point v h t₀ y₀ (n+1) = step v h (t₀ + n*h) (point v h t₀ y₀ n)`. -/
def point {𝕜 : Type*} {E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : 𝕜 → E → E) (h : 𝕜) (t₀ : 𝕜) (y₀ : E) : ℕ → E
  | 0 => y₀
  | n + 1 => step v h (t₀ + n * h) (point v h t₀ y₀ n)

/-- The slope of the Euler method on the `n`-th cell: `v(t₀ + n * h, yₙ)`. -/
noncomputable def slope (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) (n : ℕ) : E :=
  v (t₀ + n * h) (point v h t₀ y₀ n)

/-- The regular grid `t₀ + n • h` used by the Euler method. -/
def grid (h : ℝ) (t₀ : ℝ) (n : ℤ) : ℝ :=
  t₀ + n • h

/-- The Euler points, extended to `ℤ` by keeping the initial value on negative indices. -/
def pointInt (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) (n : ℤ) : E :=
  point v h t₀ y₀ n.toNat

/-- The Euler slopes, extended to `ℤ` by `0` on negative indices. -/
noncomputable def slopeInt (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) (n : ℤ) : E :=
  if 0 ≤ n then slope v h t₀ y₀ n.toNat else 0

/-- The piecewise linear Euler path, interpolating the Euler points with Euler slopes. -/
noncomputable def path (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseLinear (grid h t₀) (pointInt v h t₀ y₀) (slopeInt v h t₀ y₀)

/-- The piecewise constant right derivative of the Euler path. -/
noncomputable def deriv (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  fun t => slopeInt v h t₀ y₀ (gridIdx (grid h t₀) t)

theorem strictMono_grid {h t₀ : ℝ} (hh : 0 < h) : StrictMono (grid h t₀) := by
  refine strictMono_int_of_lt_succ fun n => ?_
  simp [grid]
  nlinarith

theorem tendsto_grid_atTop {h t₀ : ℝ} (hh : 0 < h) : Tendsto (grid h t₀) atTop atTop := by
  convert tendsto_atTop_add_const_left atTop t₀ (tendsto_id.atTop_zsmul_const hh) using 1

theorem tendsto_grid_atBot {h t₀ : ℝ} (hh : 0 < h) : Tendsto (grid h t₀) atBot atBot := by
  convert tendsto_atBot_add_const_left atBot t₀ (tendsto_id.atBot_zsmul_const hh) using 1

theorem continuous_path {v : ℝ → E → E} {h t₀ : ℝ} {y₀ : E} (hh : 0 < h) :
    Continuous (path v h t₀ y₀) := by
  refine continuous_piecewiseLinear
    (x := grid h t₀) (y := pointInt v h t₀ y₀) (c := slopeInt v h t₀ y₀)
    (strictMono_grid (t₀ := t₀) hh) (tendsto_grid_atTop (t₀ := t₀) hh)
    (tendsto_grid_atBot (t₀ := t₀) hh) ?_
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp [pointInt, slopeInt, point, step, slope, grid]
    congr 1
    ring
  · have hn0 : n ≤ 0 := by omega
    have hn1 : n + 1 ≤ 0 := by omega
    simp [pointInt, slopeInt, hn, point, grid, Int.toNat_of_nonpos hn0, Int.toNat_of_nonpos hn1]

theorem hasDerivWithinAt_path {v : ℝ → E → E} {h t₀ : ℝ} {y₀ : E} (hh : 0 < h) {t : ℝ} :
    HasDerivWithinAt (path v h t₀ y₀) (deriv v h t₀ y₀ t) (Ici t) t := by
  simpa [path, deriv] using
    (hasDerivWithinAt_piecewiseLinear
      (x := grid h t₀) (y := pointInt v h t₀ y₀) (c := slopeInt v h t₀ y₀)
      (strictMono_grid (t₀ := t₀) hh) (tendsto_grid_atTop (t₀ := t₀) hh)
      (tendsto_grid_atBot (t₀ := t₀) hh) (t := t))

@[simp] theorem path_apply_start {v : ℝ → E → E} {h t₀ : ℝ} {y₀ : E} (hh : 0 < h) :
    path v h t₀ y₀ t₀ = y₀ := by
  simpa [path, grid, pointInt] using
    (piecewiseLinear_apply_grid
      (x := grid h t₀) (y := pointInt v h t₀ y₀) (c := slopeInt v h t₀ y₀)
      (strictMono_grid (t₀ := t₀) hh) (0 : ℤ))

variable {v : ℝ → E → E} {h t₀ : ℝ} {y₀ : E} {K L : NNReal} {M : ℝ}
  (hv : ∀ t, LipschitzWith K (v t))
  (hvt : ∀ y, LipschitzWith L (fun t => v t y))
  (hM : ∀ t y, ‖v t y‖ ≤ M)
include hv hvt hM

/-- Global bound on the difference between the Euler derivative and the vector field
along the Euler path. -/
theorem dist_deriv_le (hh : 0 < h) {t : ℝ} (ht₀ : t₀ ≤ t) :
    dist (deriv v h t₀ y₀ t) (v t (path v h t₀ y₀ t)) ≤ h * (L + K * M) := by
  set n : ℤ := gridIdx (grid h t₀) t with hn_def
  have htcell : t ∈ Ico (grid h t₀ n) (grid h t₀ (n + 1)) := by
    simpa [hn_def] using
      (gridIdx_mem_Ico (x := grid h t₀) (tendsto_grid_atTop hh) (tendsto_grid_atBot hh) t)
  have hn : 0 ≤ n := by
    by_contra hn
    have hn1 : n + 1 ≤ 0 := by omega
    have hmono : Monotone (grid h t₀) := (strictMono_grid (t₀ := t₀) hh).monotone
    have hle : grid h t₀ (n + 1) ≤ t₀ := by
      simpa [grid] using hmono hn1
    linarith [htcell.2, hle, ht₀]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
  have hidx : gridIdx (grid h t₀) t = (m : ℤ) := by
    calc
      gridIdx (grid h t₀) t = n := by simp [hn_def]
      _ = m := hm
  have hmcell : t ∈ Ico (grid h t₀ (m : ℤ)) (grid h t₀ ((m : ℤ) + 1)) := by
    simpa [hm] using htcell
  have ht1 : t₀ + m * h ≤ t := by
    simpa [grid] using hmcell.1
  have ht2 : t < t₀ + (m + 1) * h := by
    simpa [grid, add_zsmul, add_assoc] using hmcell.2
  have htstep : t - (t₀ + m * h) ≤ h := by
    nlinarith
  have hpath :
      path v h t₀ y₀ t = point v h t₀ y₀ m + (t - (t₀ + m * h)) • slope v h t₀ y₀ m := by
    simpa [path, pointInt, slopeInt, slope, grid] using
      (piecewiseLinear_eq_on_Ico
        (x := grid h t₀) (y := pointInt v h t₀ y₀) (c := slopeInt v h t₀ y₀)
        (strictMono_grid (t₀ := t₀) hh) (n := (m : ℤ)) hmcell)
  have h1 : dist (v (t₀ + m * h) (point v h t₀ y₀ m)) (v t (point v h t₀ y₀ m)) ≤
      L * (t - (t₀ + m * h)) :=
    ((hvt _).dist_le_mul _ _).trans
      (by rw [dist_eq_norm, Real.norm_of_nonpos (by linarith)]; linarith)
  have h2 : dist (point v h t₀ y₀ m) (path v h t₀ y₀ t) ≤ h * M := by
    rw [hpath, dist_eq_norm]
    simpa only [sub_add_cancel_left, norm_neg, norm_smul, slope,
      Real.norm_of_nonneg (sub_nonneg.2 ht1)] using
      (mul_le_mul htstep (hM (t₀ + m * h) (point v h t₀ y₀ m)) (norm_nonneg _) hh.le)
  calc dist (deriv v h t₀ y₀ t) (v t (path v h t₀ y₀ t))
      = dist (v (t₀ + m * h) (point v h t₀ y₀ m)) (v t (path v h t₀ y₀ t)) := by
          rw [deriv, hidx]
          simp [slopeInt, slope]
    _ ≤ L * (t - (t₀ + m * h)) + K * (h * M) :=
          (dist_triangle _ _ _).trans
            (add_le_add h1 (((hv t).dist_le_mul _ _).trans (by gcongr)))
    _ ≤ h * (L + K * M) := by
          nlinarith [NNReal.coe_nonneg K, NNReal.coe_nonneg L, hM t₀ y₀]

/-- Error bound for the Euler method via Gronwall's inequality. -/
theorem dist_path_le (hh : 0 < h) {T : ℝ}
    {sol : ℝ → E} (hsol : ContinuousOn sol (Icc t₀ T))
    (hsol' : ∀ t ∈ Ico t₀ T, HasDerivWithinAt sol (v t (sol t)) (Ici t) t)
    (hsol₀ : sol t₀ = y₀) :
    ∀ t ∈ Icc t₀ T,
      dist (path v h t₀ y₀ t) (sol t) ≤ gronwallBound 0 K (h * (L + K * M)) (t - t₀) := by
  intro t ht
  have := dist_le_of_approx_trajectories_ODE (δ := 0) (εg := 0)
    (f' := deriv v h t₀ y₀) (g' := fun t => v t (sol t)) hv
    (continuous_path (v := v) (t₀ := t₀) (y₀ := y₀) hh).continuousOn
    (fun t ht => hasDerivWithinAt_path (v := v) (t₀ := t₀) (y₀ := y₀) hh)
    (fun t ht => dist_deriv_le hv hvt hM hh ht.1)
    hsol hsol' (fun _ _ => (dist_self _).le)
    (by simp [path_apply_start (v := v) (t₀ := t₀) (y₀ := y₀) hh, hsol₀]) t ht
  simpa using this

/-- The Euler method converges to the true solution as `h → 0⁺`. -/
theorem tendsto_path {T : ℝ}
    {sol : ℝ → E} (hsol : ContinuousOn sol (Icc t₀ T))
    (hsol' : ∀ t ∈ Ico t₀ T, HasDerivWithinAt sol (v t (sol t)) (Ici t) t)
    (hsol₀ : sol t₀ = y₀) :
    ∀ t ∈ Icc t₀ T, Filter.Tendsto (fun δ => path v δ t₀ y₀ t)
      (nhdsWithin 0 (Ioi 0)) (nhds (sol t)) := fun t ht =>
  tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero_norm'
    (by have := fun x (hx : (0 : ℝ) < x) =>
          dist_path_le hv hvt hM hx hsol hsol' hsol₀ t ht
        simpa using Filter.eventually_of_mem self_mem_nhdsWithin this)
    (tendsto_nhdsWithin_of_tendsto_nhds <|
      Continuous.tendsto' ((gronwallBound_continuous_ε 0 K (t - t₀)).comp
        (continuous_id.mul continuous_const)) 0 0
        (by simp [gronwallBound_ε0_δ0])))

end ODE.EulerMethod

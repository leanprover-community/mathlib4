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

open Set

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

/-- The piecewise linear Euler path, interpolating the Euler points with Euler slopes. -/
noncomputable def path (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseLinear (point v h t₀ y₀) (slope v h t₀ y₀) h t₀

/-- The piecewise constant right derivative of the Euler path. -/
noncomputable def deriv (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseConst (slope v h t₀ y₀) h t₀

variable {v : ℝ → E → E} {h t₀ : ℝ} {y₀ : E} {K L : NNReal} {M : ℝ}
  (hv : ∀ t, LipschitzWith K (v t))
  (hvt : ∀ y, LipschitzWith L (fun t => v t y))
  (hM : ∀ t y, ‖v t y‖ ≤ M)
include hv hvt hM

/-- Global bound on the difference between the Euler derivative and the vector field
along the Euler path. -/
theorem dist_deriv_le (hh : 0 < h) {t : ℝ} (ht₀ : t₀ ≤ t) :
    dist (deriv v h t₀ y₀ t) (v t (path v h t₀ y₀ t)) ≤ h * (L + K * M) := by
  obtain ⟨ht1, ht2⟩ := mem_Ico_Nat_floor_div hh ht₀; set n := ⌊(t - t₀) / h⌋₊
  have h1 : dist (v (t₀ + n * h) (point v h t₀ y₀ n)) (v t (point v h t₀ y₀ n)) ≤
      L * (t - (t₀ + n * h)) :=
    ((hvt _).dist_le_mul _ _).trans
      (by rw [dist_eq_norm, Real.norm_of_nonpos (by linarith)]; linarith)
  have h2 : dist (point v h t₀ y₀ n) (path v h t₀ y₀ t) ≤ h * M := by
    rw [show path v h t₀ y₀ t = _ from
      piecewiseLinear_eq_on_Ico hh ⟨ht1, ht2⟩, dist_eq_norm]
    simp +decide only [sub_add_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 ht1)]
    exact mul_le_mul (by linarith) (hM _ _) (norm_nonneg _) (by linarith)
  calc dist (deriv v h t₀ y₀ t) (v t (path v h t₀ y₀ t))
      = dist (v (t₀ + n * h) (point v h t₀ y₀ n)) (v t (path v h t₀ y₀ t)) := by
          simp only [deriv, piecewiseConst_eq_on_Ico hh ⟨ht1, ht2⟩, slope]
    _ ≤ L * (t - (t₀ + n * h)) + K * (h * M) :=
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
    ((piecewiseLinear_continuousOn hh fun n => by simp [point, step, slope]).mono
      Icc_subset_Ici_self)
    (fun t ht => piecewiseLinear_hasDerivWithinAt hh ht.1)
    (fun t ht => dist_deriv_le hv hvt hM hh ht.1)
    hsol hsol' (fun _ _ => (dist_self _).le)
    (by simp [piecewiseLinear, point, hsol₀]) t ht
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

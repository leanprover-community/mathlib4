/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Energy Dissipation and Stability of Evolution Schemes in Hilbert Spaces

This file formalizes energy dissipation, solenoidal subspace invariance, and Lipschitz
stability estimates for explicit Euler and semi-implicit Crank–Nicolson time-stepping schemes
associated with dissipative operators and skew-symmetric nonlinearities in real Hilbert spaces.

## Main definitions

* `EvolutionOperators`: a bundle of linear and nonlinear operators on a real Hilbert space `X`
  equipped with a dissipative linear operator `laplace` (`⟪u, laplace u⟫ ≤ 0`), skew-symmetric
  nonlinear advection (`⟪u, advection u⟫ = 0`), divergence constraint `div`, and Lipschitz
  constants.
* `EvolutionOperators.explicitStep`: one explicit time step of size `dt`.
* `EvolutionOperators.IsCrankNicolsonStep`: the implicit midpoint / Crank–Nicolson relation
  `u_next - u = -dt • advection ((1 / 2) • (u_next + u)) + (dt * ν / 2) • laplace (u_next + u)`.

## Main results

* `EvolutionOperators.div_explicitStep_eq_zero`: preservation of the divergence-free subspace
  `ker div` under an explicit evolution step.
* `EvolutionOperators.norm_sq_explicitStep_le`: energy dissipation on an explicit step under a
  CFL-type stability condition.
* `EvolutionOperators.norm_sq_crankNicolson_le`: unconditional energy dissipation of the
  semi-implicit Crank–Nicolson step for any `ν > 0` and `dt > 0`.
* `EvolutionOperators.norm_explicitStep_sub_le`: Lipschitz continuity of the explicit evolution
  operator with respect to initial states.
-/

@[expose] public section

open scoped InnerProductSpace

section EvolutionStability

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Operator bundle for dissipative evolution equations with skew-symmetric nonlinear advection
and divergence constraint in a real Hilbert space `X`. -/
structure EvolutionOperators (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  /-- Linear divergence operator defining the solenoidal subspace. -/
  div : X →ₗ[ℝ] X
  /-- Linear dissipative diffusion / Laplacian operator. -/
  laplace : X →ₗ[ℝ] X
  /-- Nonlinear advection / convection operator. -/
  advection : X → X
  /-- Secondary dissipative closure operator (e.g., eddy viscosity / Reynolds stress). -/
  closure : X → X
  /-- External solenoidal forcing field. -/
  force : X
  /-- Negative semi-definiteness of the diffusion operator (`⟪u, Δu⟫ ≤ 0`). -/
  laplace_dissipative : ∀ u : X, ⟪u, laplace u⟫_ℝ ≤ 0
  /-- Skew-symmetry of nonlinear advection (`⟪u, B(u)⟫ = 0`). -/
  advection_skew : ∀ u : X, ⟪u, advection u⟫_ℝ = 0
  /-- Negative semi-definiteness of the closure operator. -/
  closure_dissipative : ∀ u : X, ⟪u, closure u⟫_ℝ ≤ 0
  /-- Invariance of `ker div` under diffusion. -/
  laplace_solenoidal : ∀ u : X, div u = 0 → div (laplace u) = 0
  /-- Invariance of `ker div` under advection. -/
  advection_solenoidal : ∀ u : X, div u = 0 → div (advection u) = 0
  /-- Invariance of `ker div` under the closure operator. -/
  closure_solenoidal : ∀ u : X, div u = 0 → div (closure u) = 0
  /-- Divergence-free condition for the forcing term. -/
  force_solenoidal : div force = 0
  /-- Lipschitz constant for `laplace`. -/
  lipLaplace : ℝ
  /-- Lipschitz bound for `laplace`. -/
  laplace_lipschitz : ∀ u v : X, ‖laplace u - laplace v‖ ≤ lipLaplace * ‖u - v‖
  /-- Lipschitz constant for `advection`. -/
  lipAdvection : ℝ
  /-- Lipschitz bound for `advection`. -/
  advection_lipschitz : ∀ u v : X, ‖advection u - advection v‖ ≤ lipAdvection * ‖u - v‖
  /-- Lipschitz constant for `closure`. -/
  lipClosure : ℝ
  /-- Lipschitz bound for `closure`. -/
  closure_lipschitz : ∀ u v : X, ‖closure u - closure v‖ ≤ lipClosure * ‖u - v‖

namespace EvolutionOperators

/-- One explicit forward Euler step of size `dt` with viscosity `ν`. -/
def explicitStep (ops : EvolutionOperators X) (ν dt : ℝ) (u : X) : X :=
  u - dt • ops.advection u + (dt * ν) • ops.laplace u + dt • ops.force + dt • ops.closure u

/-- Semi-implicit Crank–Nicolson / midpoint step of size `dt` with viscosity `ν`. -/
def IsCrankNicolsonStep (ops : EvolutionOperators X) (ν dt : ℝ) (u u_next : X) : Prop :=
  u_next - u = -dt • ops.advection ((1 / 2 : ℝ) • (u_next + u)) +
    (dt * ν / 2) • ops.laplace (u_next + u)

/-- **Solenoidal preservation:** if `u ∈ ker div`, then `explicitStep ops ν dt u ∈ ker div`. -/
theorem div_explicitStep_eq_zero (ops : EvolutionOperators X) (ν dt : ℝ) {u : X}
    (hu : ops.div u = 0) :
    ops.div (ops.explicitStep ν dt u) = 0 := by
  dsimp [explicitStep]
  simp only [map_add, map_sub, map_smul, hu, ops.advection_solenoidal u hu,
    ops.laplace_solenoidal u hu, ops.force_solenoidal, ops.closure_solenoidal u hu,
    smul_zero, sub_zero, add_zero]

/-- **Explicit step energy dissipation:** if the increment `δu = u_next - u` satisfies the
quadratic CFL bound `‖δu‖² ≤ -2 ⟪u, δu⟫`, then `‖u_next‖² ≤ ‖u‖²`. -/
theorem norm_sq_explicitStep_le (ops : EvolutionOperators X) (ν dt : ℝ) (u : X)
    (h_cfl : ‖ops.explicitStep ν dt u - u‖ ^ 2 ≤ -2 * ⟪u, ops.explicitStep ν dt u - u⟫_ℝ) :
    ‖ops.explicitStep ν dt u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  set du := ops.explicitStep ν dt u - u
  have h_eq : ops.explicitStep ν dt u = u + du := by simp [du]
  rw [h_eq, norm_add_sq_real]
  linarith

/-- **Unconditional Crank–Nicolson energy dissipation:** for any `ν > 0` and `dt > 0`, every
solution `u_next` of the Crank–Nicolson midpoint step satisfies `‖u_next‖² ≤ ‖u‖²` without any
CFL time-step restriction. -/
theorem norm_sq_crankNicolson_le (ops : EvolutionOperators X) {ν dt : ℝ}
    (hν : 0 < ν) (hdt : 0 < dt) {u u_next : X}
    (h_step : ops.IsCrankNicolsonStep ν dt u u_next) :
    ‖u_next‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  set w : X := u_next + u
  have h_diff_inner : ⟪w, u_next - u⟫_ℝ = ⟪u_next, u_next⟫_ℝ - ⟪u, u⟫_ℝ := by
    dsimp [w]
    rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_comm u u_next]
    ring
  have h_rhs_inner : ⟪w, u_next - u⟫_ℝ =
      (dt * ν / 2) * ⟪w, ops.laplace w⟫_ℝ := by
    rw [h_step, inner_add_right, inner_smul_right, inner_smul_right]
    have h_adv : ⟪w, ops.advection ((1 / 2 : ℝ) • w)⟫_ℝ = 0 := by
      have hw : w = (2 : ℝ) • ((1 / 2 : ℝ) • w) := by
        rw [smul_smul]
        norm_num
      conv_lhs => rw [hw]
      rw [inner_smul_left]
      simp [ops.advection_skew]
    rw [h_adv, mul_zero, zero_add]
  have h_lapl_nonpos : (dt * ν / 2) * ⟪w, ops.laplace w⟫_ℝ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (ops.laplace_dissipative w)
  linarith

/-- **Lipschitz stability of the explicit step:** for `dt > 0` and `ν > 0`, the explicit
evolution operator satisfies
`‖explicitStep ops ν dt u - explicitStep ops ν dt v‖ ≤
(1 + dt * L_adv + dt * ν * L_lap + L_clos * dt) * ‖u - v‖`. -/
theorem norm_explicitStep_sub_le (ops : EvolutionOperators X) {ν dt : ℝ}
    (hν : 0 < ν) (hdt : 0 < dt) (u v : X) :
    ‖ops.explicitStep ν dt u - ops.explicitStep ν dt v‖ ≤
      (1 + dt * ops.lipAdvection + dt * ν * ops.lipLaplace + ops.lipClosure * dt) * ‖u - v‖ := by
  dsimp [explicitStep]
  have h_rearrange :
      (u - dt • ops.advection u + (dt * ν) • ops.laplace u +
        dt • ops.force + dt • ops.closure u) -
      (v - dt • ops.advection v + (dt * ν) • ops.laplace v +
        dt • ops.force + dt • ops.closure v) =
      (u - v) - dt • (ops.advection u - ops.advection v) +
      (dt * ν) • (ops.laplace u - ops.laplace v) + dt • (ops.closure u - ops.closure v) := by
    simp only [smul_sub]
    abel
  rw [h_rearrange]
  have h_tri1 := norm_add_le
    ((u - v) - dt • (ops.advection u - ops.advection v) +
      (dt * ν) • (ops.laplace u - ops.laplace v))
    (dt • (ops.closure u - ops.closure v))
  have h_tri2 := norm_add_le
    ((u - v) - dt • (ops.advection u - ops.advection v))
    ((dt * ν) • (ops.laplace u - ops.laplace v))
  have h_tri3 := norm_sub_le (u - v) (dt • (ops.advection u - ops.advection v))
  have h_adv : ‖dt • (ops.advection u - ops.advection v)‖ ≤ (dt * ops.lipAdvection) * ‖u - v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdt, mul_assoc]
    exact mul_le_mul_of_nonneg_left (ops.advection_lipschitz u v) hdt.le
  have h_lap : ‖(dt * ν) • (ops.laplace u - ops.laplace v)‖ ≤
      (dt * ν * ops.lipLaplace) * ‖u - v‖ := by
    have hdtν : 0 < dt * ν := mul_pos hdt hν
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdtν]
    calc (dt * ν) * ‖ops.laplace u - ops.laplace v‖
      _ ≤ (dt * ν) * (ops.lipLaplace * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (ops.laplace_lipschitz u v) hdtν.le
      _ = (dt * ν * ops.lipLaplace) * ‖u - v‖ := by ring
  have h_clo : ‖dt • (ops.closure u - ops.closure v)‖ ≤ (ops.lipClosure * dt) * ‖u - v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdt]
    calc dt * ‖ops.closure u - ops.closure v‖
      _ ≤ dt * (ops.lipClosure * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (ops.closure_lipschitz u v) hdt.le
      _ = (ops.lipClosure * dt) * ‖u - v‖ := by ring
  linarith

end EvolutionOperators

end EvolutionStability

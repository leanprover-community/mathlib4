/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Stationary distributions for stochastic matrices

This file proves that every row-stochastic matrix on a finite nonempty state space has a
stationary distribution in the standard simplex, via Cesàro averaging.

## Main definitions

* `IsStationary`: a distribution `μ` is stationary for `P` if `μ ᵥ* P = μ`.
* `cesaroAverage`: the Cesàro average of the iterates of a vector under a matrix.

## Main results

* `Matrix.rowStochastic.exists_stationary_distribution`: every row-stochastic matrix on a finite
  nonempty state space has a stationary distribution in the standard simplex.

## Tags

stochastic matrix, Markov chain, stationary distribution, Cesàro average
-/

@[expose] public section

open Finset Matrix ENNReal Filter

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Stationary distributions -/

section Stationary

variable {R : Type*} [Semiring R]

/-- A distribution `μ` is stationary for a matrix `P` if `μ ᵥ* P = μ`. -/
def IsStationary (μ : n → R) (P : Matrix n n R) : Prop := μ ᵥ* P = μ

/-- A stationary distribution for `P` is stationary for every power `P ^ k`. -/
lemma IsStationary.pow {μ : n → R} {P : Matrix n n R} (h : IsStationary μ P) (k : ℕ) :
    IsStationary μ (P ^ k) := by
  change μ ᵥ* P ^ k = μ
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, h]

end Stationary

/-! ### Cesàro averages -/

section CesaroAverage

variable {R : Type*} [DivisionRing R]

/-- The Cesàro average of the iterates of a vector under a matrix. -/
def cesaroAverage (x₀ : n → R) (P : Matrix n n R) (k : ℕ) : n → R :=
  (k + 1 : R)⁻¹ • ∑ i ∈ Finset.range (k + 1), x₀ ᵥ* (P ^ i)

end CesaroAverage

/-! ### L¹ non-expansiveness for row-stochastic matrices -/

section L1Norm

variable {M : Matrix n n ℝ}

namespace Matrix.rowStochastic

/-- Row-stochastic matrices are non-expansive on `ℝⁿ` in the L¹ norm. -/
theorem nnnorm_vecMul_le (hM : M ∈ rowStochastic ℝ n) (z : n → ℝ) :
    ‖WithLp.toLp 1 (z ᵥ* M)‖₊ ≤ ‖WithLp.toLp 1 z‖₊ := by
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, PiLp.norm_eq_of_L1, Real.norm_eq_abs]
  calc ∑ j, |(WithLp.toLp 1 (z ᵥ* M)) j|
      = ∑ j, |∑ i, z i * M i j| := by simp [vecMul, dotProduct]
    _ ≤ ∑ j, ∑ i, |z i| * M i j := sum_le_sum fun j _ ↦
        (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun i _ ↦ by
          rw [abs_mul, abs_of_nonneg (hM.1 i j)]
    _ = ∑ i, |(WithLp.toLp 1 z) i| := by
        simp [sum_comm, ← mul_sum, sum_row_of_mem_rowStochastic hM]

end Matrix.rowStochastic

end L1Norm

/-! ### Existence of stationary distributions -/

section Existence

variable {M : Matrix n n ℝ}

/-- The Cesàro average of a probability vector under a row-stochastic matrix
belongs to the standard simplex. -/
lemma cesaroAverage_mem_stdSimplex (hM : M ∈ Matrix.rowStochastic ℝ n)
    {x₀ : n → ℝ} (hx₀ : x₀ ∈ stdSimplex ℝ n) (k : ℕ) :
    cesaroAverage x₀ M k ∈ stdSimplex ℝ n := by
  rw [cesaroAverage, Finset.smul_sum]
  refine (convex_stdSimplex ℝ n).sum_mem (fun _ _ ↦ by positivity)
    (by simp [mul_inv_cancel₀ (by positivity : (k + 1 : ℝ) ≠ 0)])
    (fun i _ ↦ vecMul_mem_stdSimplex (Submonoid.pow_mem _ hM i) hx₀)

/-- The Cesàro average is almost invariant: applying the matrix changes it by at most `2/(k+1)`. -/
lemma norm_cesaroAverage_vecMul_sub_le (hM : M ∈ Matrix.rowStochastic ℝ n)
    {x₀ : n → ℝ} (hx₀ : x₀ ∈ stdSimplex ℝ n) (k : ℕ) :
    ‖WithLp.toLp 1 (cesaroAverage x₀ M k ᵥ* M - cesaroAverage x₀ M k)‖ ≤ 2 / (k + 1) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hsimp : cesaroAverage x₀ M k ᵥ* M - cesaroAverage x₀ M k =
      (k + 1 : ℝ)⁻¹ • (x₀ ᵥ* M ^ (k + 1) - x₀) := by
    unfold cesaroAverage
    rw [Matrix.smul_vecMul, ← smul_sub, Matrix.sum_vecMul, ← Finset.sum_sub_distrib]
    simp_rw [Matrix.vecMul_vecMul, ← pow_succ]
    rw [Finset.sum_range_sub (fun i ↦ x₀ ᵥ* M ^ i), pow_zero, Matrix.vecMul_one]
  have nn1 : ∀ {x : n → ℝ}, x ∈ stdSimplex ℝ n → ‖WithLp.toLp 1 x‖₊ = 1 := fun hx ↦ by
    rw [← NNReal.coe_inj, NNReal.coe_one, coe_nnnorm, PiLp.norm_eq_of_L1]
    simp [Real.norm_eq_abs, Finset.sum_congr rfl fun i _ ↦ abs_of_nonneg (hx.1 i), hx.2]
  have hb : ‖WithLp.toLp 1 (x₀ ᵥ* M ^ (k + 1) - x₀)‖₊ ≤ 2 := by
    rw [WithLp.toLp_sub]; refine (nnnorm_sub_le _ _).trans_eq ?_
    rw [nn1 (vecMul_mem_stdSimplex (Submonoid.pow_mem _ hM (k + 1)) hx₀), nn1 hx₀]; norm_num
  rw [hsimp, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk),
    div_eq_inv_mul]
  gcongr; exact_mod_cast hb

variable [Nonempty n]

namespace Matrix.rowStochastic

/-- Every row-stochastic matrix on a finite nonempty state space has a stationary distribution. -/
theorem exists_stationary_distribution (hM : M ∈ rowStochastic ℝ n) :
    ∃ μ : n → ℝ, μ ∈ stdSimplex ℝ n ∧ IsStationary μ M := by
  let x₀ : n → ℝ := fun _ ↦ (Fintype.card n : ℝ)⁻¹
  have hx₀ : x₀ ∈ stdSimplex ℝ n :=
    ⟨fun _ ↦ by positivity, by simp [x₀, Finset.card_univ, nsmul_eq_mul]⟩
  obtain ⟨μ, hμ, nₖ, hmono, hlim⟩ := (isCompact_stdSimplex ℝ n).tendsto_subseq
    fun k ↦ cesaroAverage_mem_stdSimplex hM hx₀ k
  have hcont : Continuous fun y : n → ℝ ↦ ‖WithLp.toLp 1 (y ᵥ* M - y)‖ := by fun_prop
  refine ⟨μ, hμ, sub_eq_zero.mp <| (WithLp.toLp_injective 1).eq_iff.mp <| norm_eq_zero.mp <|
    tendsto_nhds_unique ((hcont.tendsto μ).comp hlim)
      (squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun k ↦ norm_cesaroAverage_vecMul_sub_le hM hx₀ (nₖ k))
        ((tendsto_const_nhds.div_atTop tendsto_id).comp
          ((tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop).atTop_add tendsto_const_nhds)))⟩

end Matrix.rowStochastic

end Existence

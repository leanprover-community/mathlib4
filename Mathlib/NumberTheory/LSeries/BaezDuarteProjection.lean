/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Affine Harmonic Lagrange Projection on the Báez-Duarte Constraint Subspace

This file formalizes the closed-form Euclidean Lagrange multiplier projection onto the 2-constraint
Báez-Duarte affine manifold `A_N = {c : D1 c N = 0 ∧ D0 c N = 2}`:

* `D0`, `D1`: finite Dirichlet evaluations `∑_{k=1}^N c_k` and `∑_{k=1}^N c_k / k`.
* `HSum`, `S2Sum`, `DeltaDet`: harmonic sum `H_N`, truncated `∑_{k=1}^N 1/k^2`, and the
  2-constraint Gram determinant `Δ(N) = N * S2Sum N - (HSum N)^2`.
* `DeltaDet_double_sum_eq`, `DeltaDet_pos`, `DeltaDet_ne_zero`: Cauchy–Schwarz Lagrange identity
  `2 * Δ(N) = ∑_{j,k=1}^N (1/j - 1/k)^2`, proving `0 < Δ(N)` for all `N ≥ 2`.
* `lambda1`, `lambda0`, `projectAffine`: explicit orthogonal projection onto `A_N`.
* `projectAffine_D1`, `projectAffine_D0`, `projectAffine_mem_A_N_uncond`: unconditional proof that
  `projectAffine u N ∈ A_N` for all `N ≥ 2` and any vector `u : ℕ → ℝ`.
* `HSum_four`, `S2Sum_four`, `DeltaDet_four`: exact rational benchmarks at `N = 4`.

## References

* L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*,
  Rend. Mat. Acc. Lincei 14 (2003), 5–11.
-/

@[expose] public section

open scoped BigOperators

/-- Finite Dirichlet evaluation at `s = 0`: `D0 c N = ∑ k ∈ Finset.Icc 1 N, c k`. -/
def D0 (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, c k

/-- Finite Dirichlet evaluation at `s = 1`: `D1 c N = ∑ k ∈ Finset.Icc 1 N, c k / k`. -/
noncomputable def D1 (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, c k / (k : ℝ)

/-- Harmonic sum `HSum N = ∑ k ∈ Finset.Icc 1 N, 1 / k`. -/
noncomputable def HSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ)

/-- Truncated Basel sum `S2Sum N = ∑ k ∈ Finset.Icc 1 N, 1 / k^2`. -/
noncomputable def S2Sum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / ((k : ℝ) ^ 2)

/-- 2-constraint Gram determinant `DeltaDet N = N * S2Sum N - (HSum N)^2`. -/
noncomputable def DeltaDet (N : ℕ) : ℝ :=
  (N : ℝ) * S2Sum N - (HSum N) ^ 2

/-- First Lagrange multiplier projecting `u` onto `D1 = 0, D0 = 2`. -/
noncomputable def lambda1 (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) * (∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ)) -
    HSum N * ((∑ k ∈ Finset.Icc 1 N, u k) - 2)) / DeltaDet N

/-- Second Lagrange multiplier projecting `u` onto `D1 = 0, D0 = 2`. -/
noncomputable def lambda0 (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (S2Sum N * ((∑ k ∈ Finset.Icc 1 N, u k) - 2) -
    HSum N * (∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ))) / DeltaDet N

/-- Closed-form Euclidean projection of `u` onto the affine manifold `D1 = 0, D0 = 2`. -/
noncomputable def projectAffine (u : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  u k - lambda1 u N / (k : ℝ) - lambda0 u N

/-- Exact vanishing of `D1 (projectAffine u N) N` whenever `DeltaDet N ≠ 0`. -/
theorem projectAffine_D1 (u : ℕ → ℝ) (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D1 (projectAffine u N) N = 0 := by
  unfold D1 projectAffine
  have h_split :
      (∑ k ∈ Finset.Icc 1 N, (u k - lambda1 u N / (k : ℝ) - lambda0 u N) / (k : ℝ)) =
        (∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ)) -
          lambda1 u N * S2Sum N - lambda0 u N * HSum N := by
    have h1 : ∀ k ∈ Finset.Icc 1 N,
        (u k - lambda1 u N / (k : ℝ) - lambda0 u N) / (k : ℝ) =
          u k / (k : ℝ) - (lambda1 u N * (1 / (k : ℝ) ^ 2) + lambda0 u N * (1 / (k : ℝ))) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    dsimp [S2Sum, HSum]
    ring
  rw [h_split]
  unfold lambda1 lambda0 DeltaDet
  have hD : (N : ℝ) * S2Sum N - HSum N ^ 2 ≠ 0 := hΔ
  field_simp [hD]
  ring

/-- Exact constraint `D0 (projectAffine u N) N = 2` whenever `DeltaDet N ≠ 0`. -/
theorem projectAffine_D0 (u : ℕ → ℝ) (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D0 (projectAffine u N) N = 2 := by
  unfold D0 projectAffine
  have h_split :
      (∑ k ∈ Finset.Icc 1 N, (u k - lambda1 u N / (k : ℝ) - lambda0 u N)) =
        (∑ k ∈ Finset.Icc 1 N, u k) - lambda1 u N * HSum N - lambda0 u N * (N : ℝ) := by
    have h1 : ∀ k ∈ Finset.Icc 1 N,
        u k - lambda1 u N / (k : ℝ) - lambda0 u N =
          u k - (lambda1 u N * (1 / (k : ℝ)) + lambda0 u N) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
      show N + 1 - 1 = N by omega, nsmul_eq_mul]
    dsimp [HSum]
    ring
  rw [h_split]
  unfold lambda1 lambda0 DeltaDet
  have hD : (N : ℝ) * S2Sum N - HSum N ^ 2 ≠ 0 := hΔ
  field_simp [hD]
  ring

/-- Lagrange Cauchy–Schwarz identity `2 * DeltaDet N = ∑ j, ∑ k, (1/j - 1/k)^2`. -/
theorem DeltaDet_double_sum_eq (N : ℕ) :
    2 * DeltaDet N =
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2 := by
  have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by rw [show N + 1 - 1 = N by omega]
  have h_inner : ∀ j ∈ Finset.Icc 1 N,
      (∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2) =
        (N : ℝ) * ((1 : ℝ) / ((j : ℝ) ^ 2)) - 2 * ((1 : ℝ) / (j : ℝ)) * HSum N + S2Sum N := by
    intro j _
    have h_pt : ∀ k ∈ Finset.Icc 1 N,
        ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2 =
          (1 : ℝ) / ((j : ℝ) ^ 2) - 2 * (((1 : ℝ) / (j : ℝ)) * ((1 : ℝ) / (k : ℝ))) +
            (1 : ℝ) / ((k : ℝ) ^ 2) := fun _ _ => by ring
    rw [Finset.sum_congr rfl h_pt]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul, ← Finset.mul_sum, hcard]
    dsimp [HSum, S2Sum]
    ring
  rw [Finset.sum_congr rfl h_inner]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, hcard]
  dsimp [DeltaDet, S2Sum, HSum]
  ring

/-- Strict positivity of the 2-constraint Gram determinant `DeltaDet N > 0` for all `N ≥ 2`. -/
theorem DeltaDet_pos {N : ℕ} (hN : 2 ≤ N) : 0 < DeltaDet N := by
  have h_eq := DeltaDet_double_sum_eq N
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have h_in : ((1 : ℝ) / ((1 : ℕ) : ℝ) - (1 : ℝ) / ((2 : ℕ) : ℝ)) ^ 2 ≤
      ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / ((1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun k : ℕ => ((1 : ℝ) / ((1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2)
      (fun _ _ => sq_nonneg _) h2
  have h_out : (∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / ((1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2) ≤
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun j : ℕ => ∑ k ∈ Finset.Icc 1 N, ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / (k : ℝ)) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) h1
  have h_pos : (0 : ℝ) < ((1 : ℝ) / ((1 : ℕ) : ℝ) - (1 : ℝ) / ((2 : ℕ) : ℝ)) ^ 2 := by norm_num
  linarith

/-- Non-vanishing of `DeltaDet N` for all `N ≥ 2`. -/
theorem DeltaDet_ne_zero {N : ℕ} (hN : 2 ≤ N) : DeltaDet N ≠ 0 :=
  (DeltaDet_pos hN).ne'

/-- Unconditional Báez-Duarte affine manifold membership for `projectAffine u N` (`N ≥ 2`). -/
theorem projectAffine_mem_A_N_uncond (u : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    D1 (projectAffine u N) N = 0 ∧ D0 (projectAffine u N) N = 2 :=
  ⟨projectAffine_D1 u N (DeltaDet_ne_zero hN), projectAffine_D0 u N (DeltaDet_ne_zero hN)⟩

/-- Decomposition helper for `Finset.Icc 1 4`. -/
private lemma sum_Icc_one_four (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + f 2 + f 3 + f 4 := by
  have hI : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hI]
  norm_num [Finset.sum_insert, add_assoc]

/-- Exact rational value `HSum 4 = 25 / 12`. -/
theorem HSum_four : HSum 4 = 25 / 12 := by
  unfold HSum; rw [sum_Icc_one_four]; norm_num

/-- Exact rational value `S2Sum 4 = 205 / 144`. -/
theorem S2Sum_four : S2Sum 4 = 205 / 144 := by
  unfold S2Sum; rw [sum_Icc_one_four]; norm_num

/-- Exact rational value `DeltaDet 4 = 65 / 48`. -/
theorem DeltaDet_four : DeltaDet 4 = 65 / 48 := by
  unfold DeltaDet; rw [HSum_four, S2Sum_four]; norm_num

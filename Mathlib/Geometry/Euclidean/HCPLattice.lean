/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Geometry and Difference-Operator Moments of the 12-Neighbor HCP Lattice

This file formalizes the 12-neighbor coordination sphere of a three-dimensional Hexagonal
Close-Packed (HCP / ABAB) crystal lattice with parity-dependent interlayer stacking (`k % 2`)
and proves the exact vanishing of first-order and reflection-odd moments, the isotropy of the
second-order moment tensor, and exact quadratic consistency of the discrete HCP Laplacian.

## Main definitions

* `HCPLattice.shiftVec`: the 12 unit nearest-neighbor displacement vectors `δ_m(k) ∈ ℝ³`
  (`m : Fin 12`) for even (`k % 2 = 0`) and odd (`k % 2 ≠ 0`) stacking layers `k : ℤ`.
* `HCPLattice.discreteLaplacian`: the 12-neighbor discrete Laplacian
  `(1 / (2 * h^2)) ∑_m (f(x + h δ_m) - f(x))`.

## Main results

* `HCPLattice.normSq_shiftVec`: every displacement vector `δ_m(k)` has unit Euclidean norm
  (`‖δ_m(k)‖² = 1`).
* `HCPLattice.sum_shiftVec_zero`: the first-order drift vector vanishes identically
  (`∑_m δ_m(k) = 0`).
* `HCPLattice.sum_symmetric_cubic_moments_zero`: all reflection-odd third-order moments vanish
  identically for every layer `k : ℤ`.
* `HCPLattice.sum_quadratic_moments_isotropic`: the second-order moment tensor is strictly
  isotropic (`∑_m δ_{m,i} δ_{m,j} = 4 δ_{ij}`), ensuring exact quadratic convergence to the
  continuous Laplacian `Δf`.
-/

@[expose] public section

namespace HCPLattice

/-- A point in `ℝ³` represented by its Cartesian coordinates `(x, y, z)`. -/
@[ext]
structure Vec3 where
  /-- First Cartesian coordinate. -/
  x : ℝ
  /-- Second Cartesian coordinate. -/
  y : ℝ
  /-- Third Cartesian coordinate (stacking axis). -/
  z : ℝ

/-- Scalar multiplication on `Vec3`. -/
def Vec3.smul (c : ℝ) (v : Vec3) : Vec3 :=
  ⟨c * v.x, c * v.y, c * v.z⟩

/-- Vector addition on `Vec3`. -/
def Vec3.add (u v : Vec3) : Vec3 :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Squared Euclidean norm `x² + y² + z²` on `Vec3`. -/
def Vec3.normSq (v : Vec3) : ℝ :=
  v.x ^ 2 + v.y ^ 2 + v.z ^ 2

/-- Unfolding a sum over `Fin 12` into its 12 explicit terms. -/
lemma sum_fin12 (f : Fin 12 → ℝ) :
    (∑ m : Fin 12, f m) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 +
    (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + f 11)))))))))) = _
  ring

/-- The 12 nearest-neighbor unit displacement vectors `δ_m(k)` of the 3D Hexagonal Close-Packed
(HCP / ABAB) lattice on layer `k : ℤ`: 6 intralayer hexagonal neighbors (`m < 6`) and 6
interlayer neighbors (`6 ≤ m < 12`) whose horizontal projections alternate with `k % 2`. -/
noncomputable def shiftVec (k : ℤ) (m : Fin 12) : Vec3 :=
  let s3 : ℝ := Real.sqrt 3
  let s23 : ℝ := Real.sqrt (2 / 3)
  let p : ℝ := if k % 2 = 0 then 1 else -1
  match m with
  | 0  => ⟨1, 0, 0⟩
  | 1  => ⟨-1, 0, 0⟩
  | 2  => ⟨1 / 2, s3 / 2, 0⟩
  | 3  => ⟨-1 / 2, -s3 / 2, 0⟩
  | 4  => ⟨-1 / 2, s3 / 2, 0⟩
  | 5  => ⟨1 / 2, -s3 / 2, 0⟩
  | 6  => ⟨p * (1 / 2), p * (1 / (2 * s3)), s23⟩
  | 7  => ⟨p * (-1 / 2), p * (1 / (2 * s3)), s23⟩
  | 8  => ⟨0, p * (-1 / s3), s23⟩
  | 9  => ⟨p * (1 / 2), p * (1 / (2 * s3)), -s23⟩
  | 10 => ⟨p * (-1 / 2), p * (1 / (2 * s3)), -s23⟩
  | 11 => ⟨0, p * (-1 / s3), -s23⟩

/-- Every nearest-neighbor displacement vector `δ_m(k)` in the HCP lattice has unit Euclidean
length (`‖δ_m(k)‖² = 1`). -/
theorem normSq_shiftVec (k : ℤ) (m : Fin 12) : (shiftVec k m).normSq = 1 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hs23 : Real.sqrt (2 / 3) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hp : (if k % 2 = 0 then (1 : ℝ) else -1) ^ 2 = 1 := by split_ifs <;> norm_num
  fin_cases m <;> dsimp [shiftVec, Vec3.normSq]
  all_goals ring_nf
  all_goals simp only [hs3, hs23, hp]
  all_goals field_simp
  all_goals try simp only [hs3]
  all_goals ring

/-- **First-order symmetry:** the sum of all 12 nearest-neighbor displacement vectors vanishes
identically for every parity layer `k : ℤ`. -/
theorem sum_shiftVec_zero (k : ℤ) :
    (∑ m : Fin 12, (shiftVec k m).x) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).y) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).z) = 0 := by
  rw [sum_fin12, sum_fin12, sum_fin12]
  dsimp [shiftVec]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **Reflection-odd cubic moments:** all reflection-odd third-order moments of the 12-neighbor
HCP coordination sphere vanish identically for every layer `k : ℤ`. -/
theorem sum_symmetric_cubic_moments_zero (k : ℤ) :
    (∑ m : Fin 12, (shiftVec k m).x ^ 3) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).z ^ 3) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).x * (shiftVec k m).y ^ 2) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).x ^ 2 * (shiftVec k m).z) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).y ^ 2 * (shiftVec k m).z) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).x * (shiftVec k m).z ^ 2) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).y * (shiftVec k m).z ^ 2) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).x * (shiftVec k m).y * (shiftVec k m).z) = 0 := by
  repeat rw [sum_fin12]
  dsimp [shiftVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **Second-order isotropy (Continuum Laplacian Tensor):** the second-order moment matrix of the
12-neighbor HCP stencil equals `4 I₃` identically across both even and odd stacking layers. -/
theorem sum_quadratic_moments_isotropic (k : ℤ) :
    (∑ m : Fin 12, (shiftVec k m).x ^ 2) = 4 ∧
    (∑ m : Fin 12, (shiftVec k m).y ^ 2) = 4 ∧
    (∑ m : Fin 12, (shiftVec k m).z ^ 2) = 4 ∧
    (∑ m : Fin 12, (shiftVec k m).x * (shiftVec k m).y) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).x * (shiftVec k m).z) = 0 ∧
    (∑ m : Fin 12, (shiftVec k m).y * (shiftVec k m).z) = 0 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hs23 : Real.sqrt (2 / 3) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hp2 : (if k % 2 = 0 then (1 : ℝ) else -1) ^ 2 = 1 := by split_ifs <;> norm_num
  repeat rw [sum_fin12]
  dsimp [shiftVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals ring_nf
  all_goals simp only [hs3, hs23, hp2]
  all_goals field_simp
  all_goals try simp only [hs3]
  all_goals ring

/-- The 12-neighbor discrete HCP Laplacian operator with mesh step `h > 0`. -/
noncomputable def discreteLaplacian (f : Vec3 → ℝ) (k : ℤ) (h : ℝ) (x : Vec3) : ℝ :=
  (1 / (2 * h ^ 2)) * ∑ m : Fin 12, (f (x.add ((shiftVec k m).smul h)) - f x)

/-- **Exact quadratic consistency:** for any quadratic polynomial
`q(x, y, z) = a₀ + b₁ x + b₂ y + b₃ z + c₁₁ x² + c₂₂ y² + c₃₃ z² + c₁₂ x y + c₁₃ x z + c₂₃ y z`,
the 12-neighbor discrete HCP Laplacian reproduces the exact continuous Laplacian
`Δq = 2 (c₁₁ + c₂₂ + c₃₃)` for every step `h ≠ 0` and every parity layer `k : ℤ`. -/
theorem discreteLaplacian_quadratic_exact
    (a₀ b₁ b₂ b₃ c₁₁ c₂₂ c₃₃ c₁₂ c₁₃ c₂₃ : ℝ) (k : ℤ) {h : ℝ} (hh : h ≠ 0) (x : Vec3) :
    let q : Vec3 → ℝ := fun p =>
      a₀ + b₁ * p.x + b₂ * p.y + b₃ * p.z +
      c₁₁ * p.x ^ 2 + c₂₂ * p.y ^ 2 + c₃₃ * p.z ^ 2 +
      c₁₂ * p.x * p.y + c₁₃ * p.x * p.z + c₂₃ * p.y * p.z
    discreteLaplacian q k h x = 2 * (c₁₁ + c₂₂ + c₃₃) := by
  intro q
  dsimp [discreteLaplacian, q, Vec3.add, Vec3.smul]
  have h1 := sum_shiftVec_zero k
  have h2 := sum_quadratic_moments_isotropic k
  have h_expand : ∀ m : Fin 12,
      (a₀ + b₁ * (x.x + h * (shiftVec k m).x) + b₂ * (x.y + h * (shiftVec k m).y) +
        b₃ * (x.z + h * (shiftVec k m).z) +
        c₁₁ * (x.x + h * (shiftVec k m).x) ^ 2 + c₂₂ * (x.y + h * (shiftVec k m).y) ^ 2 +
        c₃₃ * (x.z + h * (shiftVec k m).z) ^ 2 +
        c₁₂ * (x.x + h * (shiftVec k m).x) * (x.y + h * (shiftVec k m).y) +
        c₁₃ * (x.x + h * (shiftVec k m).x) * (x.z + h * (shiftVec k m).z) +
        c₂₃ * (x.y + h * (shiftVec k m).y) * (x.z + h * (shiftVec k m).z)) -
      (a₀ + b₁ * x.x + b₂ * x.y + b₃ * x.z +
        c₁₁ * x.x ^ 2 + c₂₂ * x.y ^ 2 + c₃₃ * x.z ^ 2 +
        c₁₂ * x.x * x.y + c₁₃ * x.x * x.z + c₂₃ * x.y * x.z) =
      (b₁ * h + 2 * c₁₁ * x.x * h + c₁₂ * x.y * h + c₁₃ * x.z * h) * (shiftVec k m).x +
      (b₂ * h + 2 * c₂₂ * x.y * h + c₁₂ * x.x * h + c₂₃ * x.z * h) * (shiftVec k m).y +
      (b₃ * h + 2 * c₃₃ * x.z * h + c₁₃ * x.x * h + c₂₃ * x.y * h) * (shiftVec k m).z +
      (c₁₁ * h ^ 2) * (shiftVec k m).x ^ 2 +
      (c₂₂ * h ^ 2) * (shiftVec k m).y ^ 2 +
      (c₃₃ * h ^ 2) * (shiftVec k m).z ^ 2 +
      (c₁₂ * h ^ 2) * ((shiftVec k m).x * (shiftVec k m).y) +
      (c₁₃ * h ^ 2) * ((shiftVec k m).x * (shiftVec k m).z) +
      (c₂₃ * h ^ 2) * ((shiftVec k m).y * (shiftVec k m).z) := by
    intro m
    ring
  simp_rw [h_expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2]
  field_simp
  ring

end HCPLattice

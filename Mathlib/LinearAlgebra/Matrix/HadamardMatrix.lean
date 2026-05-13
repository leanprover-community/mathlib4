/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Star.Unitary

/-!
# Hadamard matrices

This file defines `Matrix.IsHadamard`, a unified notion that specializes to the classical real
Hadamard matrices over `ℝ`/`ℤ` (where `star` is trivial and entries are `±1`) and to the complex
Hadamard matrices over `ℂ` (where entries have unit norm). Basic results: conjugate-transpose
closure, square order from constant row sum, the Sylvester (Kronecker) construction, and the
divisibility obstruction `4 ∣ n`.

## References

* [W. de Launey and D. L. Flannery, *Algebraic Design Theory*][deLauneyFlannery2011]
-/

@[expose] public section


variable {m n R : Type*}

namespace Matrix

open scoped Kronecker


/-- A square matrix over a `*`-semiring whose entries are unitary and whose rows and columns are
both orthogonal with respect to the conjugate transpose: `A * Aᴴ = Aᴴ * A = n • 1`.

Over a ring with trivial star (e.g. `ℝ`, `ℤ`) this specializes to the classical Hadamard condition
of [Definition 2.3.1][deLauneyFlannery2011]: entries `±1` and `A * Aᵀ = n • 1`. Over `ℂ`, the entry
condition becomes `‖A i j‖ = 1`, recovering the complex Hadamard matrices of
[Definition 2.7.1][deLauneyFlannery2011]. -/
def IsHadamard [Fintype n] [DecidableEq n] [Semiring R] [StarRing R] (A : Matrix n n R) : Prop :=
  (∀ i j, A i j ∈ unitary R) ∧
    A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) ∧
    Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R)

/-- The Hadamard determinant identity: `det A * star (det A) = (card n)^(card n)`. -/
theorem IsHadamard.det_mul_star_det [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) :
    A.det * star A.det = (Fintype.card n : R) ^ Fintype.card n := by
  have := congr_arg det hA.2.1
  rwa [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this

/-- A Hadamard matrix over a reduced commutative ring has nonzero determinant, provided the order
is nonzero in `R`. -/
theorem IsHadamard.det_ne_zero [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] [IsReduced R]
    {A : Matrix n n R} (hA : A.IsHadamard) (hcard : (Fintype.card n : R) ≠ 0) :
    A.det ≠ 0 := fun h =>
  pow_ne_zero _ hcard <| by rw [← hA.det_mul_star_det, h, star_zero, zero_mul]

/-- Negating a Hadamard matrix gives a Hadamard matrix. -/
theorem IsHadamard.neg [Fintype n] [DecidableEq n] [Ring R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) : (-A).IsHadamard := by
  simpa [IsHadamard, Unitary.mem_iff] using hA

/-- A matrix is Hadamard iff its negation is. -/
@[simp]
theorem IsHadamard.neg_iff [Fintype n] [DecidableEq n] [Ring R] [StarRing R]
    {A : Matrix n n R} : (-A).IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.neg, (·.neg)⟩

/-- The conjugate transpose of a Hadamard matrix is Hadamard.

This is the matrix form of [Theorem 2.3.6][deLauneyFlannery2011]. -/
theorem IsHadamard.conjTranspose [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) : Aᴴ.IsHadamard :=
  ⟨fun i j => Unitary.star_mem (hA.1 j i),
    by rw [conjTranspose_conjTranspose]; exact hA.2.2,
    by rw [conjTranspose_conjTranspose]; exact hA.2.1⟩

/-- A Hadamard matrix with constant row sum `s` has order `s ^ 2`, provided the order is
nonzero in `R` and the star is trivial.

This is a slightly stronger form of [Theorem 2.3.7][deLauneyFlannery2011]: the constant
column sum hypothesis is unnecessary, since column orthogonality is part of `IsHadamard`. -/
theorem IsHadamard.card_eq_sq_of_const_row_sum [Fintype n] [DecidableEq n]
    [CommRing R] [StarRing R] [TrivialStar R] [IsCancelMulZero R] {A : Matrix n n R} {s : R}
    (hA : A.IsHadamard) (hcard : (Fintype.card n : R) ≠ 0)
    (hrow : ∀ i, ∑ j, A i j = s) : (Fintype.card n : R) = s ^ 2 := by
  have hv : A *ᵥ (1 : n → R) = s • 1 :=
    funext fun i => by simpa [Matrix.mulVec, dotProduct] using hrow i
  have hAtA : Aᵀ * A = (Fintype.card n : R) • (1 : Matrix n n R) := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hA.2.2
  have hL : (A *ᵥ (1 : n → R)) ⬝ᵥ (A *ᵥ (1 : n → R)) = (Fintype.card n : R) ^ 2 := by
    rw [dotProduct_mulVec, vecMul_mulVec, hAtA, vecMul_smul]
    simp [dotProduct, pow_two]
  exact mul_left_cancel₀ hcard <| by
    rw [← pow_two, ← hL, hv]
    simp [dotProduct, pow_two, mul_comm, mul_assoc]

/-- The Kronecker product of two Hadamard matrices is Hadamard. -/
theorem IsHadamard.kronecker [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [CommRing R] [StarRing R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHadamard) (hB : B.IsHadamard) : (A ⊗ₖ B).IsHadamard := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩
    exact (unitary R).mul_mem (hA.1 i j) (hB.1 i' j')
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hA.2.1, hB.2.1, kronecker_smul,
      smul_kronecker, one_kronecker_one, smul_smul]
    simp [Fintype.card_prod, mul_comm]
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hA.2.2, hB.2.2, kronecker_smul,
      smul_kronecker, one_kronecker_one, smul_smul]
    simp [Fintype.card_prod, mul_comm]

/-- A Hadamard matrix of order greater than two has order divisible by four.

This is the standard divisibility obstruction in [Section 2.3][deLauneyFlannery2011]. -/
theorem IsHadamard.four_dvd_card [Fintype n] [DecidableEq n] {A : Matrix n n ℤ}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  classical
  have hpm : ∀ i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    mul_self_eq_one_iff.mp <| by
      simpa using Unitary.mul_star_self_of_mem (hA.1 i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth : ∀ ⦃i k : n⦄, i ≠ k → ∑ j, A i j * A k j = 0 := fun i k hik => by
    simpa [Matrix.mul_apply, hik, mul_comm] using congr_fun (congr_fun hA.2.1 i) k
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : ℤ) := by
    simp_rw [show ∀ j, (1 + A s j * A r j) * (1 + A t j * A r j) =
        1 + A s j * A r j + A t j * A r j + A s j * A t j from fun j => by
      obtain hr | hr := hpm r j <;> simp [hr] <;> ring]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  refine Int.ofNat_dvd.mp (hsum ▸ Finset.dvd_sum fun j _ => ?_)
  obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
    obtain ht | ht := hpm t j <;> simp [hs, hr, ht]

end Matrix

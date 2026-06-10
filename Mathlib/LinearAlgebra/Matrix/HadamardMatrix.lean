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
orthogonal with respect to the conjugate transpose:
`A * Aᴴ = n • 1` and `Aᴴ * A = n • 1`.

Over a ring with trivial star (e.g. `ℝ`, `ℤ`), the one-sided condition from
[Definition 2.3.1][deLauneyFlannery2011] implies this predicate by
`IsHadamard.of_mul_conjTranspose`. Over `ℂ`, the entry condition becomes `‖A i j‖ = 1`,
generalizing the fourth-root complex Hadamard matrices of
[Definition 2.7.1][deLauneyFlannery2011]. -/
def IsHadamard [Fintype n] [DecidableEq n] [Semiring R] [StarRing R] (A : Matrix n n R) : Prop :=
  (∀ i j, A i j ∈ unitary R) ∧
    A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) ∧
      Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R)

theorem IsHadamard.apply [Fintype n] [DecidableEq n] [Semiring R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) (i j : n) : A i j ∈ unitary R :=
  hA.1 i j

theorem IsHadamard.mul_conjTranspose [Fintype n] [DecidableEq n] [Semiring R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) :
    A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) :=
  hA.2.1

theorem IsHadamard.conjTranspose_mul [Fintype n] [DecidableEq n] [Semiring R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) :
    Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R) :=
  hA.2.2

theorem IsHadamard.isStarNormal [Fintype n] [DecidableEq n] [Semiring R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) : IsStarNormal A where
  star_comm_self := by
    change Aᴴ * A = A * Aᴴ
    rw [hA.conjTranspose_mul, hA.mul_conjTranspose]

/-- The Hadamard determinant identity: `det A * star (det A) = (card n)^(card n)`. -/
theorem IsHadamard.det_mul_star_det [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) :
    A.det * star A.det = (Fintype.card n : R) ^ Fintype.card n := by
  have := congr_arg det hA.mul_conjTranspose
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

/-- Build a Hadamard matrix from the one-sided row-orthogonality condition, provided the order is
nonzero in a commutative ring with no zero divisors.

This is the matrix form of [Theorem 2.3.6][deLauneyFlannery2011]. -/
theorem IsHadamard.of_mul_conjTranspose [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    [NoZeroDivisors R] {A : Matrix n n R} (hentry : ∀ i j, A i j ∈ unitary R)
    (hmul : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R))
    (hcard : (Fintype.card n : R) ≠ 0) : A.IsHadamard := by
  refine ⟨hentry, hmul, ?_⟩
  have hdet : A.det ≠ 0 := fun h =>
    pow_ne_zero _ hcard <| by
      simpa [det_mul, det_conjTranspose, det_smul, det_one, h, star_zero] using
        (congr_arg det hmul).symm
  exact mul_eq_smul_one_symm
    (isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero hdet).left).left hmul

theorem isHadamard_iff_mul_conjTranspose [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    [NoZeroDivisors R] {A : Matrix n n R} (hcard : (Fintype.card n : R) ≠ 0) :
    A.IsHadamard ↔
      (∀ i j, A i j ∈ unitary R) ∧
        A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) :=
  ⟨fun hA => ⟨hA.1, hA.2.1⟩, fun hA => IsHadamard.of_mul_conjTranspose hA.1 hA.2 hcard⟩

/-- The conjugate transpose of a Hadamard matrix is Hadamard. -/
theorem IsHadamard.conjTranspose [Fintype n] [DecidableEq n] [Semiring R] [StarRing R]
    {A : Matrix n n R} (hA : A.IsHadamard) : Aᴴ.IsHadamard := by
  exact ⟨fun i j => Unitary.star_mem (hA.1 j i),
    by simpa [conjTranspose_conjTranspose] using hA.2.2,
    by simpa [conjTranspose_conjTranspose] using hA.2.1⟩

@[simp]
theorem isHadamard_conjTranspose_iff [Fintype n] [DecidableEq n] [Semiring R] [StarRing R]
    {A : Matrix n n R} : Aᴴ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.conjTranspose, (·.conjTranspose)⟩

/-- A Hadamard matrix with constant row sum `s` has order `s ^ 2`, provided the order is
nonzero in `R` and the star is trivial.

This is a slightly stronger form of [Theorem 2.3.7][deLauneyFlannery2011]:
only a constant row-sum hypothesis is needed under the two-sided orthogonality condition. -/
theorem IsHadamard.card_eq_sq_of_const_row_sum [Fintype n] [DecidableEq n]
    [CommSemiring R] [StarRing R] [TrivialStar R] [IsCancelMulZero R] {A : Matrix n n R} {s : R}
    (hA : A.IsHadamard) (hcard : (Fintype.card n : R) ≠ 0)
    (hrow : ∀ i, ∑ j, A i j = s) : (Fintype.card n : R) = s ^ 2 := by
  have hAtA : Aᵀ * A = (Fintype.card n : R) • (1 : Matrix n n R) := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hA.2.2
  have hL : (A *ᵥ 1) ⬝ᵥ (A *ᵥ 1) = (Fintype.card n : R) ^ 2 := by
    rw [dotProduct_mulVec, vecMul_mulVec, hAtA, vecMul_smul]
    simp [dotProduct, pow_two]
  exact mul_left_cancel₀ hcard <| by
    simpa [Matrix.mulVec, dotProduct, hrow, pow_two, mul_comm, mul_assoc] using hL.symm

/-- The Kronecker product of two Hadamard matrices is Hadamard. -/
theorem IsHadamard.kronecker [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [Semiring R] [StarRing R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHadamard) (hB : B.IsHadamard) : (A ⊗ₖ B).IsHadamard := by
  refine ⟨fun _ _ ↦ mul_mem (hA.apply _ _) (hB.apply _ _), ?_, ?_⟩ <;> ext ⟨i, i'⟩ ⟨j, j'⟩
  · calc
      _ = ∑ x₁, ∑ x₂, A i x₁ * (B i' x₂ * Bᴴ x₂ j') * Aᴴ x₁ j := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i' = j' then ∑ x, A i x * (Fintype.card n • Aᴴ) x j else 0 := by
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hB.mul_conjTranspose,
          one_apply, mul_assoc _ (Fintype.card n : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hA.mul_conjTranspose]
        simp [one_apply, ← Nat.cast_mul, mul_comm, ← ite_and, and_comm]
  · calc
      _ = ∑ x₁, ∑ x₂, Bᴴ i' x₂ * (Aᴴ i x₁ * A x₁ j) * B x₂ j' := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i = j then ∑ x, Bᴴ i' x * (Fintype.card m • B) x j' else 0 := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hA.conjTranspose_mul,
          one_apply, mul_assoc _ (Fintype.card m : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hB.conjTranspose_mul]
        simp [one_apply, ← Nat.cast_mul, ← ite_and]

/-- A integer Hadamard matrix of order greater than two has order divisible by four.

This is the standard divisibility obstruction in [Section 2.3][deLauneyFlannery2011]. -/
theorem IsHadamard.four_dvd_card [Fintype n] [DecidableEq n] {A : Matrix n n ℤ}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  have hpm : ∀ i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.1 (hA.1 i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth ⦃i k : n⦄ (hik : i ≠ k) : ∑ j, A i j * A k j = 0 := by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.2.1 i) k
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : ℤ) := by
    simp_rw [show ∀ j, (1 + A s j * A r j) * (1 + A t j * A r j) =
        1 + A s j * A r j + A t j * A r j + A s j * A t j from fun j => by
      obtain hr | hr := hpm r j <;> simp [hr] <;> ring]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  exact Int.ofNat_dvd.mp <| hsum ▸ Finset.dvd_sum fun j _ => by
    obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
      obtain ht | ht := hpm t j <;> simp [hs, hr, ht]

end Matrix

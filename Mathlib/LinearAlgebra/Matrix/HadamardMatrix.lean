/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Hadamard matrices

This file defines `Matrix.IsHadamard` and the complex variant `IsComplexHadamard`, with basic
results: transpose closure, square order from constant row sum, the Sylvester (Kronecker)
construction, and the divisibility obstruction `4 ∣ n`.

## References

* [W. de Launey and D. L. Flannery, *Algebraic Design Theory*][deLauneyFlannery2011]
-/

@[expose] public section


variable {m n R : Type*}

namespace Matrix

open scoped Kronecker

/-- A square matrix with entries `1` and `-1` whose rows are orthogonal.

This is Definition 2.3.1 of [deLauneyFlannery2011]. -/
def IsHadamard [Fintype n] [DecidableEq n] [Ring R] (A : Matrix n n R) : Prop :=
  (∀ i j, A i j = 1 ∨ A i j = -1) ∧
    A * Aᵀ = (Fintype.card n : R) • (1 : Matrix n n R)

/-- A complex Hadamard matrix: a square complex matrix with entries of norm one whose rows are
orthogonal with respect to conjugate transpose.

This is Definition 2.7.1 of [deLauneyFlannery2011]. -/
def IsComplexHadamard [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Prop :=
  (∀ i j, ‖A i j‖ = 1) ∧ A * Aᴴ = (Fintype.card n : ℂ) • (1 : Matrix n n ℂ)

/-- The Hadamard determinant identity: `(det A)² = (card n)^(card n)`. -/
theorem IsHadamard.det_sq [Fintype n] [DecidableEq n] [CommRing R] {A : Matrix n n R}
    (hA : A.IsHadamard) : A.det ^ 2 = (Fintype.card n : R) ^ Fintype.card n := by
  have := congr_arg det hA.2
  rwa [det_mul, det_transpose, ← sq, det_smul, det_one, mul_one] at this

/-- A Hadamard matrix over an integral domain has nonzero determinant, provided the order is
nonzero in `R`. -/
theorem IsHadamard.det_ne_zero [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]
    {A : Matrix n n R} (hA : A.IsHadamard) (hcard : (Fintype.card n : R) ≠ 0) :
    A.det ≠ 0 := fun h =>
  pow_ne_zero _ hcard <| by rw [← hA.det_sq, h]; simp

/-- A Hadamard matrix over an integral domain has Hadamard transpose, provided the order is
nonzero in `R`.

This is the matrix form of [deLauneyFlannery2011, Theorem 2.3.6]. -/
theorem IsHadamard.transpose [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]
    {A : Matrix n n R} (hA : A.IsHadamard) (hcard : (Fintype.card n : R) ≠ 0) :
    Aᵀ.IsHadamard := by
  refine ⟨fun i j => by simpa using hA.1 j i, ?_⟩
  simpa [transpose_transpose] using mul_eq_smul_one_symm hA.2 (hA.det_ne_zero hcard)

/-- A Hadamard matrix with constant row sum `s` has order `s ^ 2`, provided the order is
nonzero in `R`.

This is a slightly stronger form of [deLauneyFlannery2011, Theorem 2.3.7]:
the constant column sum hypothesis follows from orthogonality over a field. -/
theorem IsHadamard.card_eq_sq_of_const_row_sum [Fintype n] [DecidableEq n]
    [CommRing R] [IsDomain R] {A : Matrix n n R} {s : R}
    (hA : A.IsHadamard) (hcard : (Fintype.card n : R) ≠ 0)
    (hrow : ∀ i, ∑ j, A i j = s) : (Fintype.card n : R) = s ^ 2 := by
  have hv : A *ᵥ (1 : n → R) = s • 1 :=
    funext fun i => by simpa [Matrix.mulVec, dotProduct] using hrow i
  have hAtA : Aᵀ * A = (Fintype.card n : R) • (1 : Matrix n n R) := by
    simpa using (hA.transpose hcard).2
  have hL : (A *ᵥ (1 : n → R)) ⬝ᵥ (A *ᵥ (1 : n → R)) = (Fintype.card n : R) ^ 2 := by
    rw [dotProduct_mulVec, vecMul_mulVec, hAtA, vecMul_smul]
    simp [dotProduct, pow_two]
  have hR : (A *ᵥ (1 : n → R)) ⬝ᵥ (A *ᵥ (1 : n → R)) = (Fintype.card n : R) * s ^ 2 := by
    rw [hv]; simp [dotProduct, pow_two, mul_comm, mul_assoc]
  exact mul_left_cancel₀ hcard <| by rw [← pow_two]; exact hL.symm.trans hR

/-- The Kronecker product of two Hadamard matrices is Hadamard. -/
theorem IsHadamard.kronecker [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [CommRing R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHadamard) (hB : B.IsHadamard) : (A ⊗ₖ B).IsHadamard := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩
    rcases hA.1 i j with hij | hij <;> rcases hB.1 i' j' with hij' | hij' <;>
      simp [hij, hij']
  · calc
      (A ⊗ₖ B) * (A ⊗ₖ B)ᵀ = (A ⊗ₖ B) * (Aᵀ ⊗ₖ Bᵀ) := by
        rw [← kroneckerMap_transpose]
      _ = (A * Aᵀ) ⊗ₖ (B * Bᵀ) := by rw [← mul_kronecker_mul]
      _ = ((Fintype.card m : R) • (1 : Matrix m m R)) ⊗ₖ
            ((Fintype.card n : R) • (1 : Matrix n n R)) := by rw [hA.2, hB.2]
      _ = (Fintype.card (m × n) : R) • (1 : Matrix (m × n) (m × n) R) := by
        ext ⟨i, i'⟩ ⟨j, j'⟩
        by_cases hij : i = j <;> by_cases hij' : i' = j' <;>
          simp [hij, hij', Fintype.card_prod, Nat.cast_mul]

/-- A Hadamard matrix of order greater than two has order divisible by four.

This is the standard divisibility obstruction in [deLauneyFlannery2011, Section 2.3]. -/
theorem IsHadamard.four_dvd_card [Fintype n] [DecidableEq n] {A : Matrix n n ℤ}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  classical
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth : ∀ ⦃i k : n⦄, i ≠ k → ∑ j, A i j * A k j = 0 := fun i k hik => by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.2 i) k
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : ℤ) := by
    simp_rw [show ∀ j, (1 + A s j * A r j) * (1 + A t j * A r j) =
        1 + A s j * A r j + A t j * A r j + A s j * A t j from fun j => by
      rcases hA.1 r j with hr | hr <;> simp [hr] <;> ring]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  refine Int.ofNat_dvd.mp (hsum ▸ Finset.dvd_sum fun j _ => ?_)
  rcases hA.1 s j with hs | hs <;> rcases hA.1 r j with hr | hr <;>
    rcases hA.1 t j with ht | ht <;> simp [hs, hr, ht]

end Matrix

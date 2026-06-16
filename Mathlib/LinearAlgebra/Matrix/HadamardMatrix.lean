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
closure, the order identity `n = s * star s` from constant row or column sums, the Sylvester
(Kronecker) construction, and the divisibility obstruction `4 ∣ n`.

## References

* [W. de Launey and D. L. Flannery, *Algebraic Design Theory*][deLauneyFlannery2011]
-/

@[expose] public section


variable {m n R : Type*}

namespace Matrix

open scoped Kronecker

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Semiring
variable [Semiring R] [StarRing R]

/-- A square matrix over a `*`-semiring whose entries are unitary and whose rows and columns are
orthogonal with respect to the conjugate transpose:
`A * Aᴴ = n • 1` and `Aᴴ * A = n • 1`.

Over a commutative ring in which the order is regular, the one-sided condition from
[Definition 2.3.1][deLauneyFlannery2011] implies this predicate by
`IsHadamard.of_mul_conjTranspose`; over a ring with trivial star (e.g. `ℝ`, `ℤ`), the entry
condition becomes `A i j = 1 ∨ A i j = -1`. Over `ℂ`, the entry condition becomes `‖A i j‖ = 1`,
generalizing the fourth-root complex Hadamard matrices of
[Definition 2.7.1][deLauneyFlannery2011]. -/
@[mk_iff] structure IsHadamard (A : Matrix n n R) : Prop where
  apply_mem (i j : n) : A i j ∈ unitary R
  mul_conjTranspose : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R)
  conjTranspose_mul : Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R)

variable {A : Matrix n n R}

theorem IsHadamard.isStarNormal (hA : A.IsHadamard) : IsStarNormal A where
  star_comm_self := by
    rw [commute_iff_eq, star_eq_conjTranspose, hA.conjTranspose_mul, hA.mul_conjTranspose]

/-- The conjugate transpose of a Hadamard matrix is Hadamard. -/
theorem IsHadamard.conjTranspose (hA : A.IsHadamard) : Aᴴ.IsHadamard := by
  exact ⟨fun i j => Unitary.star_mem (hA.apply_mem j i),
    by simpa using hA.conjTranspose_mul,
    by simpa using hA.mul_conjTranspose⟩

@[simp]
theorem isHadamard_conjTranspose_iff : Aᴴ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.conjTranspose, (·.conjTranspose)⟩

/-- Permuting the rows and columns of a Hadamard matrix gives a Hadamard matrix. -/
theorem IsHadamard.reindex (e₁ e₂ : n ≃ m) (hA : A.IsHadamard) :
    (reindex e₁ e₂ A).IsHadamard := by
  refine ⟨fun i j => hA.apply_mem _ _, ?_, ?_⟩ <;>
    simp [reindex_apply, submatrix_mul_equiv, hA.mul_conjTranspose, hA.conjTranspose_mul,
      Fintype.card_congr e₁, submatrix_smul, Pi.smul_apply]

@[simp]
theorem isHadamard_submatrix_equiv_iff (e₁ e₂ : m ≃ n) :
    (A.submatrix e₁ e₂).IsHadamard ↔ A.IsHadamard :=
  ⟨fun h => by simpa using h.reindex e₁ e₂,
    fun h => by simpa [reindex_apply] using h.reindex e₁.symm e₂.symm⟩

/-- The Kronecker product of two Hadamard matrices is Hadamard. -/
theorem IsHadamard.kronecker {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHadamard) (hB : B.IsHadamard) : (A ⊗ₖ B).IsHadamard := by
  refine ⟨fun _ _ ↦ mul_mem (hA.apply_mem _ _) (hB.apply_mem _ _), ?_, ?_⟩ <;> ext ⟨i, i'⟩ ⟨j, j'⟩
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

/-- A Hadamard matrix with constant column sum `s` has order `s * star s`, provided the order
is regular in `R`.

The row-sum form is `IsHadamard.card_eq_star_mul_of_const_row_sum`; over a ring with trivial
star the conclusion becomes `(Fintype.card n : R) = s ^ 2`, a slightly stronger form of
[Theorem 2.3.7][deLauneyFlannery2011]: only a constant sum hypothesis on one side is needed
under the two-sided orthogonality condition. -/
theorem IsHadamard.card_eq_mul_star_of_const_col_sum {s : R}
    (hA : A.IsHadamard) (hcard : IsRegular (Fintype.card n : R))
    (hcol : ∀ j, ∑ i, A i j = s) : (Fintype.card n : R) = s * star s := by
  have hvcol : (1 : n → R) ᵥ* A = s • 1 := by
    ext j
    simpa [Matrix.vecMul, dotProduct] using hcol j
  have hconjcol : Aᴴ *ᵥ (1 : n → R) = star s • 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← star_sum, hcol i]
  have hleft : (1 : n → R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) ^ 2 := by
    rw [hA.mul_conjTranspose, Nat.cast_smul_eq_nsmul, vecMul_smul, smul_dotProduct]
    simp [dotProduct, pow_two]
  have hright : (1 : n → R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) * (s * star s) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, hvcol, hconjcol]
    simp [dotProduct]
  exact hcard.left <| show (Fintype.card n : R) * (Fintype.card n : R) =
      (Fintype.card n : R) * (s * star s) by
    simpa [pow_two] using hleft.symm.trans hright

/-- A Hadamard matrix with constant row sum `s` has order `star s * s`, provided the order
is regular in `R`. This generalizes [Theorem 2.3.7][deLauneyFlannery2011]. -/
theorem IsHadamard.card_eq_star_mul_of_const_row_sum {s : R}
    (hA : A.IsHadamard) (hcard : IsRegular (Fintype.card n : R))
    (hrow : ∀ i, ∑ j, A i j = s) : (Fintype.card n : R) = star s * s := by
  have hcol : ∀ j, ∑ i, Aᴴ i j = star s := fun j => by
    simp [conjTranspose_apply, ← star_sum, hrow j]
  simpa using hA.conjTranspose.card_eq_mul_star_of_const_col_sum hcard hcol

end Semiring

section CommSemiring
variable [CommSemiring R] [StarRing R] {A : Matrix n n R}

/-- The transpose of a Hadamard matrix is Hadamard.

Unlike `IsHadamard.conjTranspose` this requires commutativity: over a noncommutative ring the
transpose of a Hadamard matrix need not be Hadamard. -/
theorem IsHadamard.transpose (hA : A.IsHadamard) : Aᵀ.IsHadamard where
  apply_mem i j := hA.apply_mem j i
  mul_conjTranspose := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hA.conjTranspose_mul,
      transpose_smul, transpose_one]
  conjTranspose_mul := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hA.mul_conjTranspose,
      transpose_smul, transpose_one]

@[simp]
theorem isHadamard_transpose_iff : Aᵀ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.transpose, (·.transpose)⟩

end CommSemiring

section Ring
variable [Ring R] [StarRing R] {A : Matrix n n R}

/-- Negating a Hadamard matrix gives a Hadamard matrix. -/
theorem IsHadamard.neg (hA : A.IsHadamard) : (-A).IsHadamard := by
  simpa [isHadamard_iff, Unitary.mem_iff] using hA

/-- A matrix is Hadamard iff its negation is. -/
@[simp]
theorem IsHadamard.neg_iff : (-A).IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.neg, (·.neg)⟩

end Ring

section CommRing
variable [CommRing R] [StarRing R] {A : Matrix n n R}

/-- The Hadamard determinant identity: `det A * star (det A) = (card n)^(card n)`. -/
theorem IsHadamard.det_mul_star_det (hA : A.IsHadamard) :
    A.det * star A.det = (Fintype.card n : R) ^ Fintype.card n := by
  have := congr_arg det hA.mul_conjTranspose
  rwa [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this

/-- The Hadamard determinant identity: `star (det A) * det A = (card n)^(card n)`. -/
theorem IsHadamard.star_det_mul_det (hA : A.IsHadamard) :
    star A.det * A.det = (Fintype.card n : R) ^ Fintype.card n := by
  rw [mul_comm, hA.det_mul_star_det]

/-- A Hadamard matrix over a reduced commutative ring has nonzero determinant, provided the order
is nonzero in `R`. -/
theorem IsHadamard.det_ne_zero [IsReduced R] (hA : A.IsHadamard)
    (hcard : (Fintype.card n : R) ≠ 0) : A.det ≠ 0 := fun h =>
  pow_ne_zero _ hcard <| by rw [← hA.det_mul_star_det, h, star_zero, zero_mul]

/-- The determinant of a Hadamard matrix is regular, provided the order is regular in `R`. -/
theorem IsHadamard.isRegular_det (hA : A.IsHadamard)
    (hcard : IsRegular (Fintype.card n : R)) : IsRegular A.det := by
  have : IsRegular (A.det * star A.det) := by
    rw [hA.det_mul_star_det]
    exact hcard.pow _
  exact this.of_mul_left

/-- Build a Hadamard matrix from the one-sided row-orthogonality condition, provided the order is
regular in `R`.

This is the matrix form of [Theorem 2.3.6][deLauneyFlannery2011]. -/
theorem IsHadamard.of_mul_conjTranspose
    (hentry : ∀ i j, A i j ∈ unitary R)
    (hmul : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R))
    (hcard : IsRegular (Fintype.card n : R)) : A.IsHadamard := by
  refine ⟨hentry, hmul, ?_⟩
  have hdet : IsRegular (A.det * star A.det) := by
    have := congr_arg det hmul
    rw [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this
    rw [this]
    exact hcard.pow _
  have hreg : IsLeftRegular A :=
    (isRegular_of_isLeftRegular_det hdet.of_mul_left.left).left
  exact hreg <| show A * (Aᴴ * A) = A * ((Fintype.card n : R) • 1) by
    rw [← mul_assoc, hmul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem isHadamard_iff_mul_conjTranspose
    (hcard : IsRegular (Fintype.card n : R)) :
    A.IsHadamard ↔
      (∀ i j, A i j ∈ unitary R) ∧
        A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) :=
  ⟨fun hA => ⟨hA.apply_mem, hA.mul_conjTranspose⟩,
   fun hA => IsHadamard.of_mul_conjTranspose hA.1 hA.2 hcard⟩

/-- A matrix whose entries are unitary and whose distinct rows have conjugate dot product zero is
Hadamard, provided the order is regular in the ring. -/
theorem IsHadamard.of_unitary_of_pairwise_rows_of_isRegular
    (hentry : ∀ i j, A i j ∈ unitary R)
    (horth : ∀ ⦃i k : n⦄, i ≠ k → ∑ j, A i j * star (A k j) = 0)
    (hcard : IsRegular (Fintype.card n : R)) : A.IsHadamard := by
  refine IsHadamard.of_mul_conjTranspose hentry ?_ hcard
  ext i k
  by_cases hik : i = k
  · subst k
    simp [mul_apply, fun j => (Unitary.mem_iff.mp (hentry i j)).2]
  · simp [mul_apply, hik, horth hik]

/-- A matrix over a commutative ring with trivial star whose entries square to one and whose
distinct rows have dot product zero is Hadamard, provided the order is regular in the ring. -/
theorem IsHadamard.of_entry_sq_of_pairwise_rows_of_isRegular [TrivialStar R]
    (hentry_sq : ∀ i j, (A i j) ^ 2 = 1)
    (horth : ∀ ⦃i k : n⦄, i ≠ k → ∑ j, A i j * A k j = 0)
    (hcard : IsRegular (Fintype.card n : R)) : A.IsHadamard :=
  IsHadamard.of_unitary_of_pairwise_rows_of_isRegular
    (fun i j => by
      rw [Unitary.mem_iff]
      constructor <;> simpa [sq] using hentry_sq i j)
    (fun {i k} hik => by simpa using horth (i := i) (k := k) hik) hcard

section CharZeroNoZeroDivisors
variable [TrivialStar R] [CharZero R] [NoZeroDivisors R]

/-- A matrix over a commutative ring with trivial star, characteristic zero, and no zero divisors
whose entries square to one and whose distinct rows have dot product zero is Hadamard. -/
theorem IsHadamard.of_entry_sq_of_pairwise_rows
    (hentry_sq : ∀ i j, (A i j) ^ 2 = 1)
    (horth : ∀ ⦃i k : n⦄, i ≠ k → ∑ j, A i j * A k j = 0) : A.IsHadamard := by
  by_cases hempty : IsEmpty n
  · letI := hempty
    refine ⟨isEmptyElim, ?_, ?_⟩ <;> ext i <;> exact isEmptyElim i
  · haveI := not_isEmpty_iff.mp hempty
    exact IsHadamard.of_entry_sq_of_pairwise_rows_of_isRegular hentry_sq horth <|
      IsRegular.of_ne_zero <| by exact_mod_cast Fintype.card_ne_zero

end CharZeroNoZeroDivisors

end CommRing

/-- An integer Hadamard matrix of order greater than two has order divisible by four.

This is the standard divisibility obstruction in [Section 2.3][deLauneyFlannery2011]. -/
theorem IsHadamard.four_dvd_card {A : Matrix n n ℤ}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  have hpm : ∀ i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth ⦃i k : n⦄ (hik : i ≠ k) : ∑ j, A i j * A k j = 0 := by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.mul_conjTranspose i) k
  have hexpand : ∀ j, (1 + A s j * A r j) * (1 + A t j * A r j) =
      1 + A s j * A r j + A t j * A r j + A s j * A t j := fun j => by
    obtain hr | hr := hpm r j <;> simp [hr] <;> ring
  have hdvd : ∀ j, (4 : ℤ) ∣ (1 + A s j * A r j) * (1 + A t j * A r j) := fun j => by
    obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
      obtain ht | ht := hpm t j <;> simp [hs, hr, ht]
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : ℤ) := by
    simp_rw [hexpand]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  rw [← Int.ofNat_dvd, ← hsum]
  exact Finset.dvd_sum fun j _ => hdvd j

end Matrix

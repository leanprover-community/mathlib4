/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Hadamard

/-! # Vectorization of matrices

This file defines `Matrix.vec A`, the vectorization of a matrix `A`,
formed by stacking the columns of A into a single large column vector.

Since mathlib indices matrices by arbitrary types rather than `Fin n`,
the result of `Matrix.vec` on `A : Matrix m n R` is indexed by `n × m`.
The `Fin (n * m)` interpretation can be restored by composing with `finProdFinEquiv.symm`:
```lean
-- ![1, 2, 3, 4]
#eval vec !![1, 3; 2, 4] ∘ finProdFinEquiv.symm
```

While it may seem more natural to index by `m × n`, keeping the indices in the same order,
this would amount to stacking the rows into one long row, and goes against the literature.
If you want this function, you can write `Matrix.vec Aᵀ` instead.

### References

* [Wikipedia](https://en.wikipedia.org/wiki/Vectorization_(mathematics))
-/
namespace Matrix

variable {ι l m n p R S}

/-- All the matrix entries, arranged into one column. -/
@[simp]
def vec (A : Matrix m n R) : n × m → R :=
  fun ij => A ij.2 ij.1

@[simp]
theorem vec_of (f : m → n → R) : vec (of f) = Function.uncurry (flip f) := rfl

theorem vec_transpose (A : Matrix m n R) : vec Aᵀ = vec A ∘ Prod.swap := rfl

theorem vec_eq_uncurry (A : Matrix m n R) : vec A = Function.uncurry fun i j => A j i := rfl

theorem vec_inj {A B : Matrix m n R} : A.vec = B.vec ↔ A = B := by
  simp_rw [← Matrix.ext_iff, funext_iff, Prod.forall, @forall_comm m n, vec]

theorem vec_bijective : Function.Bijective (vec : Matrix m n R → _) :=
  Equiv.curry _ _ _ |>.symm.bijective.comp Function.swap_bijective

theorem vec_map (A : Matrix m n R) (f : R → S) : vec (A.map f) = f ∘ vec A := rfl

@[simp]
theorem vec_zero [Zero R] : vec (0 : Matrix m n R) = 0 :=
  rfl

@[simp]
theorem vec_add [Add R] (A B : Matrix m n R) : vec (A + B) = vec A + vec B :=
  rfl

theorem vec_neg [Neg R] (A : Matrix m n R) : vec (-A) = -vec A :=
  rfl

@[simp]
theorem vec_sub [Sub R] (A B : Matrix m n R) : vec (A - B) = vec A - vec B :=
  rfl

@[simp]
theorem vec_smul {α} [SMul α R] (r : α) (A : Matrix m n R) : vec (r • A) = r • vec A :=
  rfl

theorem vec_sum [AddCommMonoid R] (s : Finset ι) (A : ι → Matrix m n R) :
    vec (∑ i ∈ s, A i) = ∑ i ∈ s, vec (A i) := by
  ext
  simp_rw [vec, Finset.sum_apply, vec, Matrix.sum_apply]

theorem vec_dotProduct_vec [NonUnitalNonAssocSemiring R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    vec A ⬝ᵥ vec B = (Aᵀ * B).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

theorem star_vec_dotProduct_vec [NonUnitalNonAssocSemiring R] [StarRing R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    star (vec A) ⬝ᵥ vec B = (Aᴴ * B).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, conjTranspose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, Pi.star_apply, vec]

theorem vec_hadamard [Mul R] (A B : Matrix m n R) : vec (A ⊙ B) = vec A * vec B := rfl

section Kronecker
open scoped Kronecker

section NonUnitalSemiring
variable [NonUnitalSemiring R] [Fintype m] [Fintype n]

/-- Technical lemma shared with `kronecker_mulVec_vec` and `vec_mul_eq_mulVec`. -/
theorem kronecker_mulVec_vec_of_commute (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R)
    (hB : ∀ x i j, Commute x (B i j)) :
    (B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ) := by
  ext ⟨k, l⟩
  simp_rw [vec, mulVec, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hB ..).right_comm, vec, (hB ..).eq]

/-- Technical lemma shared with `vec_vecMul_kronecker` and `vec_mul_eq_vecMul`. -/
theorem vec_vecMul_kronecker_of_commute (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R)
    (hA : ∀ x i j, Commute (A i j) x) :
    vec X ᵥ* (B ⊗ₖ A) = vec (Aᵀ * X * B) := by
  ext ⟨k, l⟩
  simp_rw [vec, vecMul, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hA ..).eq, (hA ..).right_comm, mul_assoc, vec]

end NonUnitalSemiring

section NonUnitalCommSemiring
variable [NonUnitalCommSemiring R] [Fintype m] [Fintype n]

theorem kronecker_mulVec_vec (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) :
    (B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ) :=
  kronecker_mulVec_vec_of_commute _ _ _ fun _ _ _ => Commute.all _ _

theorem vec_vecMul_kronecker (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) :
    vec X ᵥ* (B ⊗ₖ A) = vec (Aᵀ * X * B) :=
  vec_vecMul_kronecker_of_commute _ _ _ fun _ _ _=> Commute.all _ _

end NonUnitalCommSemiring

section Semiring
variable [Semiring R] [Fintype m] [Fintype n]

theorem vec_mul_eq_mulVec [DecidableEq n] (A : Matrix l m R) (B : Matrix m n R) :
    vec (A * B) = (1 ⊗ₖ A) *ᵥ vec B := by
  rw [kronecker_mulVec_vec_of_commute, transpose_one, Matrix.mul_one]
  intros x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

theorem vec_mul_eq_vecMul [DecidableEq m] (A : Matrix m n R) (B : Matrix n p R) :
    vec (A * B) = A.vec ᵥ* (B ⊗ₖ 1) := by
  rw [vec_vecMul_kronecker_of_commute, transpose_one, Matrix.one_mul]
  intros x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

end Semiring

end Kronecker

end Matrix

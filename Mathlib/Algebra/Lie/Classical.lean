/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Classical Lie algebras

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `LieAlgebra.SpecialLinear.sl`
  * `LieAlgebra.Symplectic.sp`
  * `LieAlgebra.Orthogonal.so`
  * `LieAlgebra.Orthogonal.so'`
  * `LieAlgebra.Orthogonal.soIndefiniteEquiv`
  * `LieAlgebra.Orthogonal.typeD`
  * `LieAlgebra.Orthogonal.typeB`
  * `LieAlgebra.Orthogonal.typeDEquivSo'`
  * `LieAlgebra.Orthogonal.typeBEquivSo'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lieEquivMatrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
`2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `typeDEquivSo'`, `soIndefiniteEquiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/


universe u₁ u₂

namespace LieAlgebra

open Matrix

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)
variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]
variable [CommRing R]

@[simp]
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _

namespace SpecialLinear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }

theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val :=
  rfl

section ElementaryBasis

variable {n R} [Fintype n] (i j k : n)

/-- When `i ≠ j`, the single-element matrices are elements of `sl n R`.

Along with some elements produced by `singleSubSingle`, these form a natural basis of `sl n R`. -/
def single (h : i ≠ j) : R →ₗ[R] sl n R :=
  Matrix.singleLinearMap R i j |>.codRestrict _ fun r => Matrix.trace_single_eq_of_ne i j r h

@[deprecated (since := "2025-05-06")] alias Eb := single

@[simp]
theorem val_single (h : i ≠ j) (r : R) : (single i j h r).val = Matrix.single i j r :=
  rfl

@[deprecated (since := "2025-05-06")] alias eb_val := val_single

/-- The matrices with matching positive and negative elements on the diagonal are elements of
`sl n R`. Along with `single`, a subset of these form a basis for `sl n R`. -/
def singleSubSingle : R →ₗ[R] sl n R :=
  LinearMap.codRestrict _ (Matrix.singleLinearMap R i i - Matrix.singleLinearMap R j j) fun r =>
    LinearMap.sub_mem_ker_iff.mpr <| by simp

@[simp]
theorem val_singleSubSingle (r : R) :
    (singleSubSingle i j r).val = Matrix.single i i r - Matrix.single j j r :=
  rfl

@[simp]
theorem singleSubSingle_add_singleSubSingle (r : R) :
    singleSubSingle i j r + singleSubSingle j k r = singleSubSingle i k r := by
  ext : 1; simp [add_sub_add_comm]

@[simp]
theorem singleSubSingle_sub_singleSubSingle (r : R) :
    singleSubSingle i k r - singleSubSingle i j r = singleSubSingle j k r := by
  ext : 1; simp [add_sub_add_comm]

@[simp]
theorem singleSubSingle_sub_singleSubSingle' (r : R) :
    singleSubSingle i k r - singleSubSingle j k r = singleSubSingle i j r := by
  ext : 1; simp [add_sub_add_comm]

end ElementaryBasis

theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := single i j hij (1 : R)
  let B := single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero, ← sl_bracket, c.trivial, ZeroMemClass.coe_zero]
  simpa [A, B, Matrix.single, Matrix.mul_apply, hij.symm] using congr_fun (congr_fun c' i) i

end SpecialLinear

namespace Symplectic

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp [Fintype l] : LieSubalgebra R (Matrix (l ⊕ l) (l ⊕ l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)

end Symplectic

namespace Orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ Aᵀ = -A := by
  rw [so, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefiniteDiagonal : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => -1

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (p ⊕ q) (p ⊕ q) R) :=
  skewAdjointMatricesLieSubalgebra <| indefiniteDiagonal p q R

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (i : R) : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i

variable [Fintype p] [Fintype q]

theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩|⟨x⟩ <;> rcases y with ⟨y⟩|⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]

/-- There is a constructive inverse of `Pso p q R i`. -/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)

theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩|⟨x⟩ <;> rcases y with ⟨y⟩|⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
noncomputable def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl

theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (p ⊕ q) (p ⊕ q) R) =
      (Pso p q R i)⁻¹ * (A : Matrix (p ⊕ q) (p ⊕ q) R) * Pso p q R i := by
  rw [soIndefiniteEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [skewAdjointMatricesLieSubalgebraEquiv_apply]

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def JD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 1 1 0

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def PD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 1 (-1) 1 1

/-- The split-signature diagonal matrix. -/
def S :=
  indefiniteDiagonal l l R

theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl

theorem jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R := by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h, PD, s_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  simp [two_smul]

theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟ (2 : R) • (PD l R)ᵀ = 1 := by
  rw [PD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]
  simp

instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
noncomputable def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl

/-- A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 2 0 0 ]
   [ 0 0 1 ]
   [ 0 1 0 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def JB :=
  Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)

/-- A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 1 0  0 ]
   [ 0 1 -1 ]
   [ 0 1  1 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)

variable [Fintype l]

theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟ (PD l R)) = 1 := by
  rw [PB, Matrix.fromBlocks_multiply, mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]

instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)

theorem jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]

theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Unit ⊕ l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, eq_self_iff_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      DMatrix.zero_apply, Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr,
      Sum.elim_inr, Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, reduceCtorEq] <;>
    congr 1

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
noncomputable def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Unit ⊕ l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jb_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simp [indefiniteDiagonal_assoc, S]

end Orthogonal

end LieAlgebra

/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.classical
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Invertible
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Dmatrix
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

  * `lie_algebra.special_linear.sl`
  * `lie_algebra.symplectic.sp`
  * `lie_algebra.orthogonal.so`
  * `lie_algebra.orthogonal.so'`
  * `lie_algebra.orthogonal.so_indefinite_equiv`
  * `lie_algebra.orthogonal.type_D`
  * `lie_algebra.orthogonal.type_B`
  * `lie_algebra.orthogonal.type_D_equiv_so'`
  * `lie_algebra.orthogonal.type_B_equiv_so'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lie_equiv_matrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
the `2l × 2l` matrix:
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
We thus also provide equivalences `type_D_equiv_so'`, `so_indefinite_equiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/


universe u₁ u₂

namespace LieAlgebra

open Matrix

open scoped Matrix

variable (n p q l : Type _) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

@[simp]
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X ⬝ Y) - Matrix.trace (Y ⬝ X) := trace_sub _ _
    _ = Matrix.trace (X ⬝ Y) - Matrix.trace (X ⬝ Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _
    
#align lie_algebra.matrix_trace_commutator_zero LieAlgebra.matrix_trace_commutator_zero

namespace SpecialLinear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun X Y _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }
#align lie_algebra.special_linear.sl LieAlgebra.SpecialLinear.sl

theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val ⬝ B.val - B.val ⬝ A.val :=
  rfl
#align lie_algebra.special_linear.sl_bracket LieAlgebra.SpecialLinear.sl_bracket

section ElementaryBasis

variable {n} [Fintype n] (i j : n)

/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def eb (h : j ≠ i) : sl n R :=
  ⟨Matrix.stdBasisMatrix i j (1 : R),
    show Matrix.stdBasisMatrix i j (1 : R) ∈ LinearMap.ker (Matrix.traceLinearMap n R R) from
      Matrix.StdBasisMatrix.trace_zero i j (1 : R) h⟩
#align lie_algebra.special_linear.Eb LieAlgebra.SpecialLinear.eb

@[simp]
theorem eb_val (h : j ≠ i) : (eb R i j h).val = Matrix.stdBasisMatrix i j 1 :=
  rfl
#align lie_algebra.special_linear.Eb_val LieAlgebra.SpecialLinear.eb_val

end ElementaryBasis

theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian ↥(sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨j, i, hij⟩
  let A := Eb R i j hij
  let B := Eb R j i hij.symm
  intro c
  have c' : A.val ⬝ B.val = B.val ⬝ A.val := by rw [← sub_eq_zero, ← sl_bracket, c.trivial]; rfl
  simpa [std_basis_matrix, Matrix.mul_apply, hij] using congr_fun (congr_fun c' i) i
#align lie_algebra.special_linear.sl_non_abelian LieAlgebra.SpecialLinear.sl_non_abelian

end SpecialLinear

namespace Symplectic

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp [Fintype l] : LieSubalgebra R (Matrix (Sum l l) (Sum l l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)
#align lie_algebra.symplectic.sp LieAlgebra.Symplectic.sp

end Symplectic

namespace Orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)
#align lie_algebra.orthogonal.so LieAlgebra.Orthogonal.so

@[simp]
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ Aᵀ = -A := by
  erw [mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]
#align lie_algebra.orthogonal.mem_so LieAlgebra.Orthogonal.mem_so

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefiniteDiagonal : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => -1
#align lie_algebra.orthogonal.indefinite_diagonal LieAlgebra.Orthogonal.indefiniteDiagonal

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (Sum p q) (Sum p q) R) :=
  skewAdjointMatricesLieSubalgebra <| indefiniteDiagonal p q R
#align lie_algebra.orthogonal.so' LieAlgebra.Orthogonal.so'

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def pso (i : R) : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i
#align lie_algebra.orthogonal.Pso LieAlgebra.Orthogonal.pso

variable [Fintype p] [Fintype q]

theorem pso_inv {i : R} (hi : i * i = -1) : pso p q R i * pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨⟩ <;> rcases y with ⟨⟩
  ·-- x y : p
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h]
  ·-- x : p, y : q
    simp [Pso, indefinite_diagonal]
  ·-- x : q, y : p
    simp [Pso, indefinite_diagonal]
  ·-- x y : q
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h, hi]
#align lie_algebra.orthogonal.Pso_inv LieAlgebra.Orthogonal.pso_inv

/-- There is a constructive inverse of `Pso p q R i`. -/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)
#align lie_algebra.orthogonal.invertible_Pso LieAlgebra.Orthogonal.invertiblePso

theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (pso p q R i)ᵀ ⬝ indefiniteDiagonal p q R ⬝ pso p q R i = 1 := by
  ext (x y); rcases x with ⟨⟩ <;> rcases y with ⟨⟩
  ·-- x y : p
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h]
  ·-- x : p, y : q
    simp [Pso, indefinite_diagonal]
  ·-- x : q, y : p
    simp [Pso, indefinite_diagonal]
  ·-- x y : q
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h, hi]
#align lie_algebra.orthogonal.indefinite_diagonal_transform LieAlgebra.Orthogonal.indefiniteDiagonal_transform

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (Sum p q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefinite_diagonal p q R) (Pso p q R i)
        (invertible_Pso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefinite_diagonal_transform p q R hi]; rfl
#align lie_algebra.orthogonal.so_indefinite_equiv LieAlgebra.Orthogonal.soIndefiniteEquiv

theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (Sum p q) (Sum p q) R) =
      (pso p q R i)⁻¹ ⬝ (A : Matrix (Sum p q) (Sum p q) R) ⬝ pso p q R i :=
  by erw [LieEquiv.trans_apply, LieEquiv.ofEq_apply, skewAdjointMatricesLieSubalgebraEquiv_apply]
#align lie_algebra.orthogonal.so_indefinite_equiv_apply LieAlgebra.Orthogonal.soIndefiniteEquiv_apply

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def jD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 1 1 0
#align lie_algebra.orthogonal.JD LieAlgebra.Orthogonal.jD

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (jD l R)
#align lie_algebra.orthogonal.type_D LieAlgebra.Orthogonal.typeD

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def pD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 1 (-1) 1 1
#align lie_algebra.orthogonal.PD LieAlgebra.Orthogonal.pD

/-- The split-signature diagonal matrix. -/
def s :=
  indefiniteDiagonal l l R
#align lie_algebra.orthogonal.S LieAlgebra.Orthogonal.s

theorem s_as_blocks : s l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl
#align lie_algebra.orthogonal.S_as_blocks LieAlgebra.Orthogonal.s_as_blocks

theorem jD_transform [Fintype l] : (pD l R)ᵀ ⬝ jD l R ⬝ pD l R = (2 : R) • s l R := by
  have h : (PD l R)ᵀ ⬝ JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  erw [h, S_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  congr <;> simp [two_smul]
#align lie_algebra.orthogonal.JD_transform LieAlgebra.Orthogonal.jD_transform

theorem pD_inv [Fintype l] [Invertible (2 : R)] : pD l R * ⅟ (2 : R) • (pD l R)ᵀ = 1 := by
  have h : ⅟ (2 : R) • (1 : Matrix l l R) + ⅟ (2 : R) • 1 = 1 := by
    rw [← smul_add, ← two_smul R _, smul_smul, invOf_mul_self, one_smul]
  erw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, Matrix.mul_eq_mul,
    Matrix.fromBlocks_multiply]
  simp [h]
#align lie_algebra.orthogonal.PD_inv LieAlgebra.Orthogonal.pD_inv

instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (pD l R) :=
  invertibleOfRightInverse _ _ (pD_inv l R)
#align lie_algebra.orthogonal.invertible_PD LieAlgebra.Orthogonal.invertiblePD

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [JD_transform, ← coe_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl
#align lie_algebra.orthogonal.type_D_equiv_so' LieAlgebra.Orthogonal.typeDEquivSo'

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
def jB :=
  Matrix.fromBlocks ((2 : R) • 1 : Matrix Unit Unit R) 0 0 (jD l R)
#align lie_algebra.orthogonal.JB LieAlgebra.Orthogonal.jB

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (jB l R)
#align lie_algebra.orthogonal.type_B LieAlgebra.Orthogonal.typeB

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
def pB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (pD l R)
#align lie_algebra.orthogonal.PB LieAlgebra.Orthogonal.pB

variable [Fintype l]

theorem pB_inv [Invertible (2 : R)] : pB l R * Matrix.fromBlocks 1 0 0 (⅟ (pD l R)) = 1 := by
  rw [PB, Matrix.mul_eq_mul, Matrix.fromBlocks_multiply, Matrix.mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]
#align lie_algebra.orthogonal.PB_inv LieAlgebra.Orthogonal.pB_inv

instance invertiblePB [Invertible (2 : R)] : Invertible (pB l R) :=
  invertibleOfRightInverse _ _ (pB_inv l R)
#align lie_algebra.orthogonal.invertible_PB LieAlgebra.Orthogonal.invertiblePB

theorem jB_transform : (pB l R)ᵀ ⬝ jB l R ⬝ pB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (s l R) := by
  simp [PB, JB, JD_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
#align lie_algebra.orthogonal.JB_transform LieAlgebra.Orthogonal.jB_transform

theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Sum Unit l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext (i j)
  rcases i with ⟨⟨i₁ | i₂⟩ | i₃⟩ <;> rcases j with ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
      simp only [indefinite_diagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
        Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
        Sum.elim_inl, if_true, eq_self_iff_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
        DMatrix.zero_apply, Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr,
        Sum.elim_inr] <;>
    congr
#align lie_algebra.orthogonal.indefinite_diagonal_assoc LieAlgebra.Orthogonal.indefiniteDiagonal_assoc

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Sum Unit l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefinite_diagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ (Equiv.sumAssoc PUnit l l)) (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [JB_transform, ← coe_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simpa [indefinite_diagonal_assoc]
#align lie_algebra.orthogonal.type_B_equiv_so' LieAlgebra.Orthogonal.typeBEquivSo'

end Orthogonal

end LieAlgebra


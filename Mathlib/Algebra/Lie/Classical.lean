/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Invertible
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.SymplecticGroup

#align_import algebra.lie.classical from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

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

set_option linter.uppercaseLean3 false

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
#align lie_algebra.matrix_trace_commutator_zero LieAlgebra.matrix_trace_commutator_zero

namespace SpecialLinear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }
#align lie_algebra.special_linear.sl LieAlgebra.SpecialLinear.sl

theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val :=
  rfl
#align lie_algebra.special_linear.sl_bracket LieAlgebra.SpecialLinear.sl_bracket

section ElementaryBasis

variable {n} [Fintype n] (i j : n)

/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of `sl n R`. -/
def Eb (h : j ≠ i) : sl n R :=
  ⟨Matrix.stdBasisMatrix i j (1 : R),
    show Matrix.stdBasisMatrix i j (1 : R) ∈ LinearMap.ker (Matrix.traceLinearMap n R R) from
      Matrix.StdBasisMatrix.trace_zero i j (1 : R) h⟩
#align lie_algebra.special_linear.Eb LieAlgebra.SpecialLinear.Eb

@[simp]
theorem eb_val (h : j ≠ i) : (Eb R i j h).val = Matrix.stdBasisMatrix i j 1 :=
  rfl
#align lie_algebra.special_linear.Eb_val LieAlgebra.SpecialLinear.eb_val

end ElementaryBasis

theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨j, i, hij⟩
  -- ⊢ ¬IsLieAbelian { x // x ∈ sl n R }
  let A := Eb R i j hij
  -- ⊢ ¬IsLieAbelian { x // x ∈ sl n R }
  let B := Eb R j i hij.symm
  -- ⊢ ¬IsLieAbelian { x // x ∈ sl n R }
  intro c
  -- ⊢ False
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero, ← sl_bracket, c.trivial, ZeroMemClass.coe_zero]
  simpa [stdBasisMatrix, Matrix.mul_apply, hij] using congr_fun (congr_fun c' i) i
  -- 🎉 no goals
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
  rw [so, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  -- ⊢ IsSkewAdjoint 1 A ↔ Aᵀ = -A
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]
  -- 🎉 no goals
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
def Pso (i : R) : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i
#align lie_algebra.orthogonal.Pso LieAlgebra.Orthogonal.Pso

variable [Fintype p] [Fintype q]

theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩|⟨x⟩ <;> rcases y with ⟨y⟩|⟨y⟩
  -- ⊢ (Pso p q R i * Pso p q R (-i)) x y = OfNat.ofNat 1 x y
             -- ⊢ (Pso p q R i * Pso p q R (-i)) (Sum.inl x) y = OfNat.ofNat 1 (Sum.inl x) y
                                       -- ⊢ (Pso p q R i * Pso p q R (-i)) (Sum.inl x) (Sum.inl y) = OfNat.ofNat 1 (Sum. …
                                       -- ⊢ (Pso p q R i * Pso p q R (-i)) (Sum.inr x) (Sum.inl y) = OfNat.ofNat 1 (Sum. …
  · -- x y : p
    by_cases h : x = y <;>
    -- ⊢ (Pso p q R i * Pso p q R (-i)) (Sum.inl x) (Sum.inl y) = OfNat.ofNat 1 (Sum. …
    simp [Pso, indefiniteDiagonal, h]
    -- 🎉 no goals
    -- 🎉 no goals
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
    -- 🎉 no goals
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
    -- 🎉 no goals
  · -- x y : q
    by_cases h : x = y <;>
    -- ⊢ (Pso p q R i * Pso p q R (-i)) (Sum.inr x) (Sum.inr y) = OfNat.ofNat 1 (Sum. …
    simp [Pso, indefiniteDiagonal, h, hi]
    -- 🎉 no goals
    -- 🎉 no goals
#align lie_algebra.orthogonal.Pso_inv LieAlgebra.Orthogonal.pso_inv

/-- There is a constructive inverse of `Pso p q R i`. -/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)
#align lie_algebra.orthogonal.invertible_Pso LieAlgebra.Orthogonal.invertiblePso

theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩|⟨x⟩ <;> rcases y with ⟨y⟩|⟨y⟩
  -- ⊢ ((Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i) x y = OfNat.ofNat  …
             -- ⊢ ((Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i) (Sum.inl x) y = Of …
                                       -- ⊢ ((Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i) (Sum.inl x) (Sum.i …
                                       -- ⊢ ((Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i) (Sum.inr x) (Sum.i …
  · -- x y : p
    by_cases h : x = y <;>
    -- ⊢ ((Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i) (Sum.inl x) (Sum.i …
    simp [Pso, indefiniteDiagonal, h]
    -- 🎉 no goals
    -- 🎉 no goals
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
    -- 🎉 no goals
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
    -- 🎉 no goals
  · -- x y : q
    by_cases h : x = y <;>
    -- ⊢ ((Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i) (Sum.inr x) (Sum.i …
    simp [Pso, indefiniteDiagonal, h, hi]
    -- 🎉 no goals
    -- 🎉 no goals
#align lie_algebra.orthogonal.indefinite_diagonal_transform LieAlgebra.Orthogonal.indefiniteDiagonal_transform

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (Sum p q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  -- ⊢ ↑(skewAdjointMatricesLieSubalgebra ((Pso p q R i)ᵀ * indefiniteDiagonal p q  …
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl
  -- ⊢ A ∈ ↑(skewAdjointMatricesLieSubalgebra ((Pso p q R i)ᵀ * indefiniteDiagonal  …
         -- ⊢ A ∈ ↑(skewAdjointMatricesLieSubalgebra 1) ↔ A ∈ ↑(so (p ⊕ q) R)
                                                     -- 🎉 no goals
#align lie_algebra.orthogonal.so_indefinite_equiv LieAlgebra.Orthogonal.soIndefiniteEquiv

theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (Sum p q) (Sum p q) R) =
      (Pso p q R i)⁻¹ * (A : Matrix (Sum p q) (Sum p q) R) * Pso p q R i := by
  rw [soIndefiniteEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply,
    skewAdjointMatricesLieSubalgebraEquiv_apply]
#align lie_algebra.orthogonal.so_indefinite_equiv_apply LieAlgebra.Orthogonal.soIndefiniteEquiv_apply

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def JD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 1 1 0
#align lie_algebra.orthogonal.JD LieAlgebra.Orthogonal.JD

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)
#align lie_algebra.orthogonal.type_D LieAlgebra.Orthogonal.typeD

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def PD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 1 (-1) 1 1
#align lie_algebra.orthogonal.PD LieAlgebra.Orthogonal.PD

/-- The split-signature diagonal matrix. -/
def S :=
  indefiniteDiagonal l l R
#align lie_algebra.orthogonal.S LieAlgebra.Orthogonal.S

theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  -- ⊢ S l R = diagonal (Sum.elim (fun x => 1) fun i => -1)
  rfl
  -- 🎉 no goals
#align lie_algebra.orthogonal.S_as_blocks LieAlgebra.Orthogonal.s_as_blocks

theorem jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R := by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h, PD, s_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  -- ⊢ fromBlocks (1 * 1 + 1 * 1) (1 * -1 + 1 * 1) (1 * 1 + -1 * 1) (1 * -1 + -1 *  …
  congr
  -- ⊢ fromBlocks (1 * 1 + 1 * 1) (1 * -1 + 1 * 1) (1 * 1 + -1 * 1) (1 * -1 + -1 *  …
  simp [two_smul]
  -- 🎉 no goals
#align lie_algebra.orthogonal.JD_transform LieAlgebra.Orthogonal.jd_transform

theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟ (2 : R) • (PD l R)ᵀ = 1 := by
  rw [PD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]
  simp
  -- 🎉 no goals
#align lie_algebra.orthogonal.PD_inv LieAlgebra.Orthogonal.pd_inv

instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)
#align lie_algebra.orthogonal.invertible_PD LieAlgebra.Orthogonal.invertiblePD

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  -- ⊢ { x // x ∈ skewAdjointMatricesLieSubalgebra ((PD l R)ᵀ * JD l R * PD l R) }  …
  apply LieEquiv.ofEq
  -- ⊢ ↑(skewAdjointMatricesLieSubalgebra ((PD l R)ᵀ * JD l R * PD l R)) = ↑(so' l  …
  ext A
  -- ⊢ A ∈ ↑(skewAdjointMatricesLieSubalgebra ((PD l R)ᵀ * JD l R * PD l R)) ↔ A ∈  …
  rw [jd_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl
  -- 🎉 no goals
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
def JB :=
  Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)
#align lie_algebra.orthogonal.JB LieAlgebra.Orthogonal.JB

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)
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
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)
#align lie_algebra.orthogonal.PB LieAlgebra.Orthogonal.PB

variable [Fintype l]

theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟ (PD l R)) = 1 := by
  rw [PB, Matrix.fromBlocks_multiply, mul_invOf_self]
  -- ⊢ fromBlocks (1 * 1 + 0 * 0) (1 * 0 + 0 * ⅟(PD l R)) (0 * 1 + PD l R * 0) (0 * …
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]
#align lie_algebra.orthogonal.PB_inv LieAlgebra.Orthogonal.pb_inv

instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)
#align lie_algebra.orthogonal.invertible_PB LieAlgebra.Orthogonal.invertiblePB

theorem jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
#align lie_algebra.orthogonal.JB_transform LieAlgebra.Orthogonal.jb_transform

theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Sum Unit l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
  -- Porting note: added `Sum.inl_injective.eq_iff`, `Sum.inr_injective.eq_iff`
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, eq_self_iff_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      DMatrix.zero_apply, Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr,
      Sum.elim_inr, Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff] <;>
    congr 1
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align lie_algebra.orthogonal.indefinite_diagonal_assoc LieAlgebra.Orthogonal.indefiniteDiagonal_assoc

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Sum Unit l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  -- ⊢ { x // x ∈ skewAdjointMatricesLieSubalgebra ((PB l R)ᵀ * JB l R * PB l R) }  …
  symm
  -- ⊢ { x // x ∈ so' (Unit ⊕ l) l R } ≃ₗ⁅R⁆ { x // x ∈ skewAdjointMatricesLieSubal …
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ (Equiv.sumAssoc PUnit l l)) (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  -- ⊢ ↑(skewAdjointMatricesLieSubalgebra (↑(reindexAlgEquiv R (Equiv.sumAssoc PUni …
  ext A
  -- ⊢ A ∈ ↑(skewAdjointMatricesLieSubalgebra (↑(reindexAlgEquiv R (Equiv.sumAssoc  …
  rw [jb_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simp [indefiniteDiagonal_assoc, S]
  -- 🎉 no goals
#align lie_algebra.orthogonal.type_B_equiv_so' LieAlgebra.Orthogonal.typeBEquivSo'

end Orthogonal

end LieAlgebra

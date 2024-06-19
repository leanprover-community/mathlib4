/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Star
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

#align_import topology.instances.matrix from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

* `Matrix.topologicalRing`: square matrices form a topological ring

## Main results

* Continuity:
  * `Continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `Continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `Matrix.transpose_tsum`: transpose commutes with infinite sums
  * `Matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `Matrix.blockDiagonal_tsum`: block diagonal commutes with infinite sums
  * `Matrix.blockDiagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/


open Matrix

variable {X α l m n p S R : Type*} {m' n' : l → Type*}

instance [TopologicalSpace R] : TopologicalSpace (Matrix m n R) :=
  Pi.topologicalSpace

instance [TopologicalSpace R] [T2Space R] : T2Space (Matrix m n R) :=
  Pi.t2Space

/-! ### Lemmas about continuity of operations -/

section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

instance [SMul α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousConstSMul α (m → n → R))

instance [TopologicalSpace α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousSMul α (m → n → R))

instance [Add R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R) :=
  Pi.continuousAdd

instance [Neg R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R) :=
  Pi.continuousNeg

instance [AddGroup R] [TopologicalAddGroup R] : TopologicalAddGroup (Matrix m n R) :=
  Pi.topologicalAddGroup

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R}
    (h : ∀ i j, Continuous fun a => f a i j) : Continuous f :=
  continuous_pi fun _ => continuous_pi fun _ => h _ _
#align continuous_matrix continuous_matrix

theorem Continuous.matrix_elem {A : X → Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA
#align continuous.matrix_elem Continuous.matrix_elem

@[continuity]
theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R}
    (hA : Continuous A) (hf : Continuous f) : Continuous fun x => (A x).map f :=
  continuous_matrix fun _ _ => hf.comp <| hA.matrix_elem _ _
#align continuous.matrix_map Continuous.matrix_map

@[continuity]
theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i
#align continuous.matrix_transpose Continuous.matrix_transpose

theorem Continuous.matrix_conjTranspose [Star R] [ContinuousStar R] {A : X → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => (A x)ᴴ :=
  hA.matrix_transpose.matrix_map continuous_star
#align continuous.matrix_conj_transpose Continuous.matrix_conjTranspose

instance [Star R] [ContinuousStar R] : ContinuousStar (Matrix m m R) :=
  ⟨continuous_id.matrix_conjTranspose⟩

@[continuity]
theorem Continuous.matrix_col {A : X → n → R} (hA : Continuous A) : Continuous fun x => col (A x) :=
  continuous_matrix fun i _ => (continuous_apply i).comp hA
#align continuous.matrix_col Continuous.matrix_col

@[continuity]
theorem Continuous.matrix_row {A : X → n → R} (hA : Continuous A) : Continuous fun x => row (A x) :=
  continuous_matrix fun _ _ => (continuous_apply _).comp hA
#align continuous.matrix_row Continuous.matrix_row

@[continuity]
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => diagonal (A x) :=
  continuous_matrix fun i _ => ((continuous_apply i).comp hA).if_const _ continuous_zero
#align continuous.matrix_diagonal Continuous.matrix_diagonal

@[continuity]
theorem Continuous.matrix_dotProduct [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → n → R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => dotProduct (A x) (B x) :=
  continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hA).mul ((continuous_apply i).comp hB)
#align continuous.matrix_dot_product Continuous.matrix_dotProduct

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity]
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → Matrix m n R} {B : X → Matrix n p R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => A x * B x :=
  continuous_matrix fun _ _ =>
    continuous_finset_sum _ fun _ _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)
#align continuous.matrix_mul Continuous.matrix_mul

instance [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
    ContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩

instance [Fintype n] [NonUnitalNonAssocSemiring R] [TopologicalSemiring R] :
    TopologicalSemiring (Matrix n n R) where

instance Matrix.topologicalRing [Fintype n] [NonUnitalNonAssocRing R] [TopologicalRing R] :
    TopologicalRing (Matrix n n R) where
#align matrix.topological_ring Matrix.topologicalRing

@[continuity]
theorem Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X → m → R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => vecMulVec (A x) (B x) :=
  continuous_matrix fun _ _ => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)
#align continuous.matrix_vec_mul_vec Continuous.matrix_vecMulVec

@[continuity]
theorem Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype n] {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x *ᵥ B x :=
  continuous_pi fun i => ((continuous_apply i).comp hA).matrix_dotProduct hB
#align continuous.matrix_mul_vec Continuous.matrix_mulVec

@[continuity]
theorem Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype m] {A : X → m → R} {B : X → Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ᵥ* B x :=
  continuous_pi fun _i => hA.matrix_dotProduct <| continuous_pi fun _j => hB.matrix_elem _ _
#align continuous.matrix_vec_mul Continuous.matrix_vecMul

@[continuity]
theorem Continuous.matrix_submatrix {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l)
    (e₂ : p → n) : Continuous fun x => (A x).submatrix e₁ e₂ :=
  continuous_matrix fun _i _j => hA.matrix_elem _ _
#align continuous.matrix_submatrix Continuous.matrix_submatrix

@[continuity]
theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
    (e₂ : n ≃ p) : Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_submatrix _ _
#align continuous.matrix_reindex Continuous.matrix_reindex

@[continuity]
theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) :
    Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _
#align continuous.matrix_diag Continuous.matrix_diag

-- note this doesn't elaborate well from the above
theorem continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R → n → R) :=
  show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag
#align continuous_matrix_diag continuous_matrix_diag

@[continuity]
theorem Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => trace (A x) :=
  continuous_finset_sum _ fun _ _ => hA.matrix_elem _ _
#align continuous.matrix_trace Continuous.matrix_trace

@[continuity]
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).det := by
  simp_rw [Matrix.det_apply]
  refine continuous_finset_sum _ fun l _ => Continuous.const_smul ?_ _
  exact continuous_finset_prod _ fun l _ => hA.matrix_elem _ _
#align continuous.matrix_det Continuous.matrix_det

@[continuity]
theorem Continuous.matrix_updateColumn [DecidableEq n] (i : n) {A : X → Matrix m n R}
    {B : X → m → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).updateColumn i (B x) :=
  continuous_matrix fun _j k =>
    (continuous_apply k).comp <|
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)
#align continuous.matrix_update_column Continuous.matrix_updateColumn

@[continuity]
theorem Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB
#align continuous.matrix_update_row Continuous.matrix_updateRow

@[continuity]
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    {A : X → Matrix n n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => cramer (A x) (B x) :=
  continuous_pi fun _ => (hA.matrix_updateColumn _ hB).matrix_det
#align continuous.matrix_cramer Continuous.matrix_cramer

@[continuity]
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun _j k =>
    (hA.matrix_transpose.matrix_updateColumn k continuous_const).matrix_det
#align continuous.matrix_adjugate Continuous.matrix_adjugate

/-- When `Ring.inverse` is continuous at the determinant (such as in a `NormedRing`, or a
topological field), so is `Matrix.inv`. -/
theorem continuousAt_matrix_inv [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    (A : Matrix n n R) (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.continuousAt).smul continuous_id.matrix_adjugate.continuousAt
#align continuous_at_matrix_inv continuousAt_matrix_inv

-- lemmas about functions in `Data/Matrix/Block.lean`
section BlockMatrices

@[continuity]
theorem Continuous.matrix_fromBlocks {A : X → Matrix n l R} {B : X → Matrix n m R}
    {C : X → Matrix p l R} {D : X → Matrix p m R} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
  continuous_matrix <| by
    rintro (i | i) (j | j) <;> refine Continuous.matrix_elem ?_ i j <;> assumption
#align continuous.matrix_from_blocks Continuous.matrix_fromBlocks

@[continuity]
theorem Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, _j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero
#align continuous.matrix_block_diagonal Continuous.matrix_blockDiagonal

@[continuity]
theorem Continuous.matrix_blockDiag {A : X → Matrix (m × p) (n × p) R} (hA : Continuous A) :
    Continuous fun x => blockDiag (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _
#align continuous.matrix_block_diag Continuous.matrix_blockDiag

@[continuity]
theorem Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l]
    {A : X → ∀ i, Matrix (m' i) (n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiagonal' (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const
#align continuous.matrix_block_diagonal' Continuous.matrix_blockDiagonal'

@[continuity]
theorem Continuous.matrix_blockDiag' {A : X → Matrix (Σi, m' i) (Σi, n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiag' (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _
#align continuous.matrix_block_diag' Continuous.matrix_blockDiag'

end BlockMatrices

end Continuity

/-! ### Lemmas about infinite sums -/


section tsum

variable [Semiring α] [AddCommMonoid R] [TopologicalSpace R] [Module α R]

theorem HasSum.matrix_transpose {f : X → Matrix m n R} {a : Matrix m n R} (hf : HasSum f a) :
    HasSum (fun x => (f x)ᵀ) aᵀ :=
  (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose : _)
#align has_sum.matrix_transpose HasSum.matrix_transpose

theorem Summable.matrix_transpose {f : X → Matrix m n R} (hf : Summable f) :
    Summable fun x => (f x)ᵀ :=
  hf.hasSum.matrix_transpose.summable
#align summable.matrix_transpose Summable.matrix_transpose

@[simp]
theorem summable_matrix_transpose {f : X → Matrix m n R} :
    (Summable fun x => (f x)ᵀ) ↔ Summable f :=
  Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
    continuous_id.matrix_transpose continuous_id.matrix_transpose
#align summable_matrix_transpose summable_matrix_transpose

theorem Matrix.transpose_tsum [T2Space R] {f : X → Matrix m n R} : (∑' x, f x)ᵀ = ∑' x, (f x)ᵀ := by
  by_cases hf : Summable f
  · exact hf.hasSum.matrix_transpose.tsum_eq.symm
  · have hft := summable_matrix_transpose.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, transpose_zero]
#align matrix.transpose_tsum Matrix.transpose_tsum

theorem HasSum.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    {a : Matrix m n R} (hf : HasSum f a) : HasSum (fun x => (f x)ᴴ) aᴴ :=
  (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose : _)
#align has_sum.matrix_conj_transpose HasSum.matrix_conjTranspose

theorem Summable.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    (hf : Summable f) : Summable fun x => (f x)ᴴ :=
  hf.hasSum.matrix_conjTranspose.summable
#align summable.matrix_conj_transpose Summable.matrix_conjTranspose

@[simp]
theorem summable_matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R} :
    (Summable fun x => (f x)ᴴ) ↔ Summable f :=
  Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
#align summable_matrix_conj_transpose summable_matrix_conjTranspose

theorem Matrix.conjTranspose_tsum [StarAddMonoid R] [ContinuousStar R] [T2Space R]
    {f : X → Matrix m n R} : (∑' x, f x)ᴴ = ∑' x, (f x)ᴴ := by
  by_cases hf : Summable f
  · exact hf.hasSum.matrix_conjTranspose.tsum_eq.symm
  · have hft := summable_matrix_conjTranspose.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, conjTranspose_zero]
#align matrix.conj_transpose_tsum Matrix.conjTranspose_tsum

theorem HasSum.matrix_diagonal [DecidableEq n] {f : X → n → R} {a : n → R} (hf : HasSum f a) :
    HasSum (fun x => diagonal (f x)) (diagonal a) :=
  hf.map (diagonalAddMonoidHom n R) continuous_id.matrix_diagonal
#align has_sum.matrix_diagonal HasSum.matrix_diagonal

theorem Summable.matrix_diagonal [DecidableEq n] {f : X → n → R} (hf : Summable f) :
    Summable fun x => diagonal (f x) :=
  hf.hasSum.matrix_diagonal.summable
#align summable.matrix_diagonal Summable.matrix_diagonal

@[simp]
theorem summable_matrix_diagonal [DecidableEq n] {f : X → n → R} :
    (Summable fun x => diagonal (f x)) ↔ Summable f :=
  Summable.map_iff_of_leftInverse (Matrix.diagonalAddMonoidHom n R) (Matrix.diagAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag fun A => diag_diagonal A
#align summable_matrix_diagonal summable_matrix_diagonal

theorem Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X → n → R} :
    diagonal (∑' x, f x) = ∑' x, diagonal (f x) := by
  by_cases hf : Summable f
  · exact hf.hasSum.matrix_diagonal.tsum_eq.symm
  · have hft := summable_matrix_diagonal.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact diagonal_zero
#align matrix.diagonal_tsum Matrix.diagonal_tsum

theorem HasSum.matrix_diag {f : X → Matrix n n R} {a : Matrix n n R} (hf : HasSum f a) :
    HasSum (fun x => diag (f x)) (diag a) :=
  hf.map (diagAddMonoidHom n R) continuous_matrix_diag
#align has_sum.matrix_diag HasSum.matrix_diag

theorem Summable.matrix_diag {f : X → Matrix n n R} (hf : Summable f) :
    Summable fun x => diag (f x) :=
  hf.hasSum.matrix_diag.summable
#align summable.matrix_diag Summable.matrix_diag

section BlockMatrices

theorem HasSum.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R}
    {a : p → Matrix m n R} (hf : HasSum f a) :
    HasSum (fun x => blockDiagonal (f x)) (blockDiagonal a) :=
  hf.map (blockDiagonalAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
#align has_sum.matrix_block_diagonal HasSum.matrix_blockDiagonal

theorem Summable.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R} (hf : Summable f) :
    Summable fun x => blockDiagonal (f x) :=
  hf.hasSum.matrix_blockDiagonal.summable
#align summable.matrix_block_diagonal Summable.matrix_blockDiagonal

theorem summable_matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R} :
    (Summable fun x => blockDiagonal (f x)) ↔ Summable f :=
  Summable.map_iff_of_leftInverse (blockDiagonalAddMonoidHom m n p R)
    (blockDiagAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
    continuous_id.matrix_blockDiag fun A => blockDiag_blockDiagonal A
#align summable_matrix_block_diagonal summable_matrix_blockDiagonal

theorem Matrix.blockDiagonal_tsum [DecidableEq p] [T2Space R] {f : X → p → Matrix m n R} :
    blockDiagonal (∑' x, f x) = ∑' x, blockDiagonal (f x) := by
  by_cases hf : Summable f
  · exact hf.hasSum.matrix_blockDiagonal.tsum_eq.symm
  · have hft := summable_matrix_blockDiagonal.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact blockDiagonal_zero
#align matrix.block_diagonal_tsum Matrix.blockDiagonal_tsum

theorem HasSum.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
    (hf : HasSum f a) : HasSum (fun x => blockDiag (f x)) (blockDiag a) :=
  (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id : _)
#align has_sum.matrix_block_diag HasSum.matrix_blockDiag

theorem Summable.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} (hf : Summable f) :
    Summable fun x => blockDiag (f x) :=
  hf.hasSum.matrix_blockDiag.summable
#align summable.matrix_block_diag Summable.matrix_blockDiag

theorem HasSum.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    {a : ∀ i, Matrix (m' i) (n' i) R} (hf : HasSum f a) :
    HasSum (fun x => blockDiagonal' (f x)) (blockDiagonal' a) :=
  hf.map (blockDiagonal'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
#align has_sum.matrix_block_diagonal' HasSum.matrix_blockDiagonal'

theorem Summable.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    (hf : Summable f) : Summable fun x => blockDiagonal' (f x) :=
  hf.hasSum.matrix_blockDiagonal'.summable
#align summable.matrix_block_diagonal' Summable.matrix_blockDiagonal'

theorem summable_matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    (Summable fun x => blockDiagonal' (f x)) ↔ Summable f :=
  Summable.map_iff_of_leftInverse (blockDiagonal'AddMonoidHom m' n' R)
    (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
    continuous_id.matrix_blockDiag' fun A => blockDiag'_blockDiagonal' A
#align summable_matrix_block_diagonal' summable_matrix_blockDiagonal'

theorem Matrix.blockDiagonal'_tsum [DecidableEq l] [T2Space R]
    {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    blockDiagonal' (∑' x, f x) = ∑' x, blockDiagonal' (f x) := by
  by_cases hf : Summable f
  · exact hf.hasSum.matrix_blockDiagonal'.tsum_eq.symm
  · have hft := summable_matrix_blockDiagonal'.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact blockDiagonal'_zero
#align matrix.block_diagonal'_tsum Matrix.blockDiagonal'_tsum

theorem HasSum.matrix_blockDiag' {f : X → Matrix (Σi, m' i) (Σi, n' i) R}
    {a : Matrix (Σi, m' i) (Σi, n' i) R} (hf : HasSum f a) :
    HasSum (fun x => blockDiag' (f x)) (blockDiag' a) :=
  hf.map (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiag'
#align has_sum.matrix_block_diag' HasSum.matrix_blockDiag'

theorem Summable.matrix_blockDiag' {f : X → Matrix (Σi, m' i) (Σi, n' i) R} (hf : Summable f) :
    Summable fun x => blockDiag' (f x) :=
  hf.hasSum.matrix_blockDiag'.summable
#align summable.matrix_block_diag' Summable.matrix_blockDiag'

end BlockMatrices

end tsum

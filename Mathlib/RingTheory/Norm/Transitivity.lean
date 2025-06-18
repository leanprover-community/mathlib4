/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Transitivity of algebra norm

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## References

* [silvester2000] Silvester, *Determinants of Block Matrices*, The Mathematical Gazette (2000).

-/

variable {R S A n m : Type*} [CommRing R] [CommRing S]
variable (M : Matrix m m S) [DecidableEq m] [DecidableEq n] (k : m)
open Matrix Polynomial

namespace Algebra.Norm.Transitivity

/-- Given a ((m-1)+1)x((m-1)+1) block matrix `M = [[A,b],[c,d]]`, `auxMat M k` is the auxiliary
matrix `[[dI,0],[-c,1]]`. `k` corresponds to the last row/column of the matrix. -/
def auxMat : Matrix m m S :=
  of fun i j ↦
    if j = k then
      if i = k then 1 else 0
    else if i = k then -M k j
    else if i = j then M k k
    else 0

/-- `aux M k` is lower triangular. -/
lemma auxMat_blockTriangular : (auxMat M k).BlockTriangular (· ≠ k) :=
  fun i j lt ↦ by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp, not_not] at lt
    rw [auxMat, of_apply, if_pos lt.2, if_neg lt.1]

lemma auxMat_toSquareBlock_ne : (auxMat M k).toSquareBlock (· ≠ k) True = M k k • 1 := by
  ext i j
  simp [auxMat, toSquareBlock_def, if_neg (of_eq_true i.2), if_neg (of_eq_true j.2),
    Matrix.one_apply, Subtype.ext_iff]

lemma auxMat_toSquareBlock_eq : (auxMat M k).toSquareBlock (· ≠ k) False = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff, iff_false, not_not] at hi hj
  simp [auxMat, toSquareBlock_def, if_pos hi, if_pos hj, Matrix.one_apply, if_pos (hj ▸ hi)]

variable [Fintype m]

/-- `M * aux M k` is upper triangular. -/
lemma mul_auxMat_blockTriangular : (M * auxMat M k).BlockTriangular (· = k) :=
  fun i j lt ↦ by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp] at lt
    simp_rw [Matrix.mul_apply, auxMat, of_apply, if_neg lt.2, mul_ite, mul_neg, mul_zero]
    rw [Finset.sum_ite, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton,
      Finset.sum_ite_eq', if_pos, lt.1, mul_comm, neg_add_cancel]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt.2⟩

/-- The lower-right corner of `M * aux M k` is the same as the corner of `M`. -/
lemma mul_auxMat_corner : (M * auxMat M k) k k = M k k := by simp [Matrix.mul_apply, auxMat]

lemma mul_auxMat_toSquareBlock_eq :
    (M * auxMat M k).toSquareBlock (· = k) True = M k k • 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff, iff_true] at hi hj
  simp [toSquareBlock_def, hi, hj, mul_auxMat_corner]

set_option quotPrecheck false in
/-- The upper-left block of `M * aux M k`. -/
scoped notation "mulAuxMatBlock" => (M * auxMat M k).toSquareBlock (· = k) False

lemma det_mul_corner_pow :
    M.det * M k k ^ (Fintype.card m - 1) = M k k * (mulAuxMatBlock).det := by
  trans (M * auxMat M k).det
  · simp [det_mul, (auxMat_blockTriangular M k).det_fintype,
      auxMat_toSquareBlock_ne, auxMat_toSquareBlock_eq]
  rw [(mul_auxMat_blockTriangular M k).det_fintype, Fintype.prod_Prop, mul_auxMat_toSquareBlock_eq]
  simp_rw [det_smul_of_tower, eq_iff_iff, iff_true, Fintype.card_unique,
    pow_one, det_one, smul_eq_mul, mul_one]
  -- `Decidable (P = Q)` diamond induced by `Prop.linearOrder`, which is classical, when `P` and `Q`
  -- are themselves decidable.
  convert rfl

/-- A matrix with X added to the corner. -/
noncomputable def cornerAddX : Matrix m m S[X] :=
  (diagonal fun i ↦ if i = k then X else 0) + M.map C

variable [Fintype n] (f : S →+* Matrix n n R)

omit [Fintype m] in
lemma polyToMatrix_cornerAddX :
    f.polyToMatrix (cornerAddX M k k k) = (-f (M k k)).charmatrix := by
  simp [cornerAddX, Matrix.add_apply, charmatrix,
    RingHom.polyToMatrix, ← AlgEquiv.symm_toRingEquiv, map_neg]

lemma eval_zero_det_det : eval 0 (f.polyToMatrix (cornerAddX M k).det).det = (f M.det).det := by
  rw [← coe_evalRingHom, RingHom.map_det, ← RingHom.comp_apply,
    evalRingHom_mapMatrix_comp_polyToMatrix, f.comp_apply, RingHom.map_det]
  congr; ext; simp [cornerAddX, diagonal, apply_ite]

lemma eval_zero_comp_det :
    eval 0 (comp m m n n R[X] <| (cornerAddX M k).map f.polyToMatrix).det =
      (comp m m n n R <| M.map f).det := by
  simp_rw [← coe_evalRingHom, RingHom.map_det, ← compRingEquiv_apply, ← RingEquiv.coe_toRingHom,
    ← RingHom.mapMatrix_apply, ← RingHom.comp_apply, ← RingHom.comp_assoc,
    evalRingHom_mapMatrix_comp_compRingEquiv, RingHom.comp_assoc, RingHom.mapMatrix_comp,
    evalRingHom_mapMatrix_comp_polyToMatrix, ← RingHom.mapMatrix_comp, RingHom.comp_apply]
  congr with i j
  simp [cornerAddX, diagonal, apply_ite]

theorem comp_det_mul_pow :
    ((M.map f).comp m m n n R).det * (f (M k k)).det ^ (Fintype.card m - 1) =
      (f (M k k)).det * (((mulAuxMatBlock).map f).comp _ _ n n R).det := by
  trans (((M * auxMat M k).map f).comp m m n n R).det
  · simp_rw [← f.mapMatrix_apply, ← compRingEquiv_apply, map_mul, det_mul, f.mapMatrix_apply,
      compRingEquiv_apply, ((auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· ≠ k)), det_reindex_self, map_toSquareBlock,
      auxMat_toSquareBlock_eq, auxMat_toSquareBlock_ne, smul_one_eq_diagonal, ← diagonal_one,
      diagonal_map (map_zero _), comp_diagonal, det_reindex_self]
    simp
  · simp_rw [((mul_auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· = k)), det_reindex_self, map_toSquareBlock,
      mul_auxMat_toSquareBlock_eq, smul_one_eq_diagonal,
      diagonal_map (map_zero _), comp_diagonal, det_reindex_self]
    simp

variable {M f} in
lemma det_det_aux
    (ih : ∀ M, (f (det M)).det = ((M.map f).comp {a // (a = k) = False} _ n n R).det) :
    ((f M.det).det - ((M.map f).comp m m n n R).det) *
      (f (M k k)).det ^ (Fintype.card m - 1) = 0 := by
  rw [sub_mul, comp_det_mul_pow, ← det_pow, ← map_pow, ← det_mul, ← map_mul,
    det_mul_corner_pow, map_mul, det_mul, ih, sub_self]

end Algebra.Norm.Transitivity

open Algebra.Norm.Transitivity

/-- The main result in Silvester's paper *Determinants of Block Matrices*: the determinant of
a block matrix with commuting, equal-sized, square blocks can be computed by taking determinants
twice in a row: first take the determinant over the commutative ring generated by the
blocks (`S` here), then take the determinant over the base ring. -/
theorem Matrix.det_det [Fintype m] [Fintype n] (f : S →+* Matrix n n R) :
    (f M.det).det = ((M.map f).comp m m n n R).det := by
  set l := Fintype.card m with hl
  clear_value l; revert R S m
  induction' l with l ih <;> intro R S m _ _ M _ _ f card
  · rw [eq_comm, Fintype.card_eq_zero_iff] at card
    simp_rw [Matrix.det_isEmpty, map_one, det_one]
  have ⟨k⟩ := Fintype.card_pos_iff.mp (l.succ_pos.trans_eq card)
  let f' := f.polyToMatrix
  let M' := cornerAddX M k
  have : (f' M'.det).det = ((M'.map f').comp m m n n R[X]).det := by
    refine sub_eq_zero.mp <| mem_nonZeroDivisors_iff.mp
      (pow_mem ?_ _) _ (det_det_aux k fun M ↦ ih _ _ <| by simp [← card])
    rw [polyToMatrix_cornerAddX, ← charpoly]
    exact (Matrix.charpoly_monic _).mem_nonZeroDivisors
  rw [← eval_zero_det_det, congr_arg (eval 0) this, eval_zero_comp_det]

variable [Algebra R S] [Module.Free R S]

theorem LinearMap.det_restrictScalars [AddCommGroup A] [Module R A] [Module S A]
    [IsScalarTower R S A] [Module.Free S A] {f : A →ₗ[S] A} :
    (f.restrictScalars R).det = Algebra.norm R f.det := by
  classical
  nontriviality R
  nontriviality A
  have := Module.nontrivial S A
  let ⟨ιS, bS⟩ := Module.Free.exists_basis (R := R) (M := S)
  let ⟨ιA, bA⟩ := Module.Free.exists_basis (R := S) (M := A)
  have := bS.index_nonempty
  have := bA.index_nonempty
  cases fintypeOrInfinite ιS; swap
  · rw [Algebra.norm_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bS),
      det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
  cases fintypeOrInfinite ιA; swap
  · rw [det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bA), map_one,
      det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
  rw [Algebra.norm_eq_matrix_det bS, ← AlgHom.coe_toRingHom, ← det_toMatrix bA, det_det,
    ← det_toMatrix (bS.smulTower' bA), restrictScalars_toMatrix, RingHom.coe_coe]

/-- Let A/S/R be a tower of finite free tower of rings (with R and S commutative).
Then $\text{Norm}_{A/R} = \text{Norm}_{A/S} \circ \text{Norm}_{S/R}$. -/
theorem Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Free S A] {a : A} :
    norm R (norm S a) = norm R a := by
  rw [norm_apply S, norm_apply R a, ← LinearMap.det_restrictScalars]; rfl

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Matrix.DotProductStarClass
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Matrix.Dual

#align_import data.matrix.rank from "leanprover-community/mathlib"@"17219820a8aa8abe85adf5dfde19af1dd1bd8ae7"

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `Matrix.rank_eq_finrank_range_toLin`.

## Main declarations

* `Matrix.rank`: the rank of a matrix

## TODO

* Do a better job of generalizing over `ℚ`, `ℝ`, and `ℂ` in `Matrix.rank_transpose` and
  `Matrix.rank_conjTranspose`. See
  [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/row.20rank.20equals.20column.20rank/near/350462992).

-/


open Matrix

namespace Matrix

open FiniteDimensional

variable {l m n o R : Type _} [m_fin : Fintype m] [Fintype n] [Fintype o]

section CommRing

variable [CommRing R]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank (A : Matrix m n R) : ℕ :=
  finrank R <| LinearMap.range A.mulVecLin
#align matrix.rank Matrix.rank

@[simp]
theorem rank_one [StrongRankCondition R] [DecidableEq n] :
    rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank, mulVecLin_one, LinearMap.range_id, finrank_top, finrank_pi]
#align matrix.rank_one Matrix.rank_one

@[simp]
theorem rank_zero [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank, mulVecLin_zero, LinearMap.range_zero, finrank_bot]
#align matrix.rank_zero Matrix.rank_zero

theorem rank_le_card_width [StrongRankCondition R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card n := by
  haveI : Module.Finite R (n → R) := Module.Finite.pi
  haveI : Module.Free R (n → R) := Module.Free.pi _ _
  exact A.mulVecLin.finrank_range_le.trans_eq (finrank_pi _)
#align matrix.rank_le_card_width Matrix.rank_le_card_width

theorem rank_le_width [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ n :=
  A.rank_le_card_width.trans <| (Fintype.card_fin n).le
#align matrix.rank_le_width Matrix.rank_le_width

theorem rank_mul_le_left [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A ⬝ B).rank ≤ A.rank := by
  rw [rank, rank, mulVecLin_mul]
  exact Cardinal.toNat_le_of_le_of_lt_aleph0 (rank_lt_aleph0 _ _) (LinearMap.rank_comp_le_left _ _)
#align matrix.rank_mul_le_left Matrix.rank_mul_le_left

theorem rank_mul_le_right [StrongRankCondition R] (A : Matrix l m R) (B : Matrix m n R) :
    (A ⬝ B).rank ≤ B.rank := by
  rw [rank, rank, mulVecLin_mul]
  exact
    finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _) (rank_lt_aleph0 _ _)
#align matrix.rank_mul_le_right Matrix.rank_mul_le_right

theorem rank_mul_le [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A ⬝ B).rank ≤ min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)
#align matrix.rank_mul_le Matrix.rank_mul_le

theorem rank_unit [StrongRankCondition R] [DecidableEq n] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n := by
  refine' le_antisymm (rank_le_card_width A) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← mul_eq_mul, ← Units.val_mul, mul_inv_self, Units.val_one, rank_one] at this
#align matrix.rank_unit Matrix.rank_unit

theorem rank_of_isUnit [StrongRankCondition R] [DecidableEq n] (A : Matrix n n R) (h : IsUnit A) :
    A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A
#align matrix.rank_of_is_unit Matrix.rank_of_isUnit

/-- Right multiplying by an invertible matrix does not change the rank -/
lemma rank_mul_eq_left_of_isUnit_det [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (B ⬝ A).rank = B.rank := by
  suffices : Function.Surjective A.mulVecLin
  · rw [rank, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr this), ← rank]
  intro v
  exact ⟨(A⁻¹).mulVecLin v, by simp [mul_nonsing_inv _ hA]⟩

/-- Left multiplying by an invertible matrix does not change the rank -/
lemma rank_mul_eq_right_of_isUnit_det [DecidableEq m]
    (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (A ⬝ B).rank = B.rank := by
  let b : Basis m R (m → R) := Pi.basisFun R m
  replace hA : IsUnit (LinearMap.toMatrix b b A.mulVecLin).det := by
    convert hA; rw [← LinearEquiv.eq_symm_apply]; rfl
  have hAB : mulVecLin (A ⬝ B) = (LinearEquiv.ofIsUnitDet hA).comp (mulVecLin B) := by ext; simp
  rw [rank, rank, hAB, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

/-- Taking a subset of the rows and permuting the columns reduces the rank. -/
theorem rank_submatrix_le [StrongRankCondition R] [Fintype m] (f : n → m) (e : n ≃ m)
    (A : Matrix m m R) : rank (A.submatrix f e) ≤ rank A := by
  rw [rank, rank, mulVecLin_submatrix, LinearMap.range_comp, LinearMap.range_comp,
    show LinearMap.funLeft R R e.symm = LinearEquiv.funCongrLeft R R e.symm from rfl,
    LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _
#align matrix.rank_submatrix_le Matrix.rank_submatrix_le

theorem rank_reindex [Fintype m] (e₁ e₂ : m ≃ n) (A : Matrix m m R) :
    rank (reindex e₁ e₂ A) = rank A := by
  rw [rank, rank, mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]
#align matrix.rank_reindex Matrix.rank_reindex

@[simp]
theorem rank_submatrix [Fintype m] (A : Matrix m m R) (e₁ e₂ : n ≃ m) :
    rank (A.submatrix e₁ e₂) = rank A := by
  simpa only [reindex_apply] using rank_reindex e₁.symm e₂.symm A
#align matrix.rank_submatrix Matrix.rank_submatrix

theorem rank_eq_finrank_range_toLin [DecidableEq n] {M₁ M₂ : Type _} [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R) (v₁ : Basis m R M₁)
    (v₂ : Basis n R M₂) : A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A)) := by
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  have range_e₂ : LinearMap.range e₂ = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact e₂.surjective
  refine' LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ _)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) range_e₂]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := toLin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [toLin_eq_toLin', toLin'_apply'] at aux₁
  rw [Pi.basisFun_apply, LinearMap.coe_stdBasis] at aux₁ aux₂
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.refl_apply, aux₁, aux₂,
    LinearMap.coe_single, toLin_self, LinearEquiv.map_sum, LinearEquiv.map_smul, Basis.equiv_apply]
#align matrix.rank_eq_finrank_range_to_lin Matrix.rank_eq_finrank_range_toLin

theorem rank_le_card_height [StrongRankCondition R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card m := by
  haveI : Module.Finite R (m → R) := Module.Finite.pi
  haveI : Module.Free R (m → R) := Module.Free.pi _ _
  exact (Submodule.finrank_le _).trans (finrank_pi R).le
#align matrix.rank_le_card_height Matrix.rank_le_card_height

theorem rank_le_height [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ m :=
  A.rank_le_card_height.trans <| (Fintype.card_fin m).le
#align matrix.rank_le_height Matrix.rank_le_height

/-- The rank of a matrix is the rank of the space spanned by its columns. -/
theorem rank_eq_finrank_span_cols (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range Aᵀ)) := by rw [rank, Matrix.range_mulVecLin]
#align matrix.rank_eq_finrank_span_cols Matrix.rank_eq_finrank_span_cols

end CommRing

section Field
-- Praneeth Kolichala's proof for rank_tranpose see:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/row.20rank.20equals.20column.20rank/near/360941958

open LinearMap

theorem matrix.rank_transpose' {𝕜 i j : Type _}
    [Field 𝕜] [Fintype i] [Fintype j] [DecidableEq i][DecidableEq j] (m : Matrix i j 𝕜) :
    m.transpose.rank = m.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin mᵀ (Pi.basisFun 𝕜 j).dualBasis (Pi.basisFun 𝕜 i).dualBasis,
  Matrix.toLin_transpose, ← dualMap_def, finrank_range_dualMap_eq_finrank_range,
  Matrix.toLin_eq_toLin', Matrix.toLin'_apply', Matrix.rank]

end Field

section DotProductInnerProductSpace

variable {m : Type _} [Fintype m]
variable {R : Type _} [Field R] [StarRing R]
variable [DotProductInnerProductSpace m R] [DotProductInnerProductSpace n R]

open FiniteDimensional

theorem ker_mulVecLin_conjTranspose_mul_self' (A : Matrix m n R) :
    LinearMap.ker (Aᴴ ⬝ A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct (star x)) h
    haveI : NoZeroDivisors R := inferInstance
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_conjTranspose, star_star,
      DotProductInnerProductSpace.dotProduct_star_self_eq_zero_iff] at h
  · intro h
    rw [h, mulVec_zero]

@[simp]
theorem rank_conjTranspose_mul_self' (A : Matrix m n R) :
    (Aᴴ ⬝ A).rank = A.rank := by
  dsimp only [Matrix.rank]
  refine' add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) _
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᴴ ⬝ A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ ⬝ A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self']
  · simp only [LinearMap.finrank_range_add_finrank_ker]

@[simp]
theorem rank_conjTranspose' (A : Matrix m n R) : Aᴴ.rank = A.rank :=
  le_antisymm
    (((rank_conjTranspose_mul_self' _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
      congr_arg _ <| conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self' _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]
theorem rank_self_mul_conjTranspose' (A : Matrix m n R) : (A ⬝ Aᴴ).rank = A.rank := by
  simpa only [rank_conjTranspose', conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self' Aᴴ

end DotProductInnerProductSpace

/-! ### Lemmas about transpose and conjugate transpose

This section contains lemmas about the rank of `Matrix.transpose` and `Matrix.conjTranspose`.

Unfortunately the proofs are essentially duplicated between the two; `ℚ` is a linearly-ordered ring
but can't be a star-ordered ring, while `ℂ` is star-ordered (with `open ComplexOrder`) but
not linearly ordered. For now we don't prove the transpose case for `ℂ`.

TODO: the lemmas `Matrix.rank_transpose` and `Matrix.rank_conjTranspose` current follow a short
proof that is a simple consequence of `Matrix.rank_transpose_mul_self` and
`Matrix.rank_conjTranspose_mul_self`. This proof pulls in unnecessary assumptions on `R`, and should
be replaced with a proof that uses Gaussian reduction or argues via linear combinations.
-/

section LinearOrderedField

variable [Fintype m] [LinearOrderedField R]

theorem ker_mulVecLin_transpose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᵀ ⬝ A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h, mulVec_zero]
#align matrix.ker_mul_vec_lin_transpose_mul_self Matrix.ker_mulVecLin_transpose_mul_self

theorem rank_transpose_mul_self (A : Matrix m n R) : (Aᵀ ⬝ A).rank = A.rank := by
  dsimp only [rank]
  refine' add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) _
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᵀ ⬝ A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᵀ ⬝ A)) }
  · rw [ker_mulVecLin_transpose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]
#align matrix.rank_transpose_mul_self Matrix.rank_transpose_mul_self

/-- TODO: prove this in greater generality. -/
@[simp]
theorem rank_transpose (A : Matrix m n R) : Aᵀ.rank = A.rank :=
  le_antisymm ((rank_transpose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)
    ((rank_transpose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)
#align matrix.rank_transpose Matrix.rank_transpose

@[simp]
theorem rank_self_mul_transpose (A : Matrix m n R) : (A ⬝ Aᵀ).rank = A.rank := by
  simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ
#align matrix.rank_self_mul_transpose Matrix.rank_self_mul_transpose

end LinearOrderedField

/-- The rank of a matrix is the rank of the space spanned by its rows.

TODO: prove this in a generality that works for `ℂ` too, not just `ℚ` and `ℝ`. -/
theorem rank_eq_finrank_span_row [LinearOrderedField R] [Finite m] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A)) := by
  cases nonempty_fintype m
  rw [← rank_transpose, rank_eq_finrank_span_cols, transpose_transpose]
#align matrix.rank_eq_finrank_span_row Matrix.rank_eq_finrank_span_row

end Matrix

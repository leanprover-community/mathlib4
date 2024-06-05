/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Diagonal

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

variable {l m n o R : Type*} [Fintype n] [Fintype o]

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
    (A * B).rank ≤ A.rank := by
  rw [rank, rank, mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left _ _) (rank_lt_aleph0 _ _)
#align matrix.rank_mul_le_left Matrix.rank_mul_le_left

theorem rank_mul_le_right [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ B.rank := by
  rw [rank, rank, mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)
#align matrix.rank_mul_le_right Matrix.rank_mul_le_right

theorem rank_mul_le [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)
#align matrix.rank_mul_le Matrix.rank_mul_le

theorem rank_unit [StrongRankCondition R] [DecidableEq n] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n := by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_self, Units.val_one, rank_one] at this
#align matrix.rank_unit Matrix.rank_unit

theorem rank_of_isUnit [StrongRankCondition R] [DecidableEq n] (A : Matrix n n R) (h : IsUnit A) :
    A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A
#align matrix.rank_of_is_unit Matrix.rank_of_isUnit

/-- Right multiplying by an invertible matrix does not change the rank -/
@[simp]
lemma rank_mul_eq_left_of_isUnit_det [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (B * A).rank = B.rank := by
  suffices Function.Surjective A.mulVecLin by
    rw [rank, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr this), ← rank]
  intro v
  exact ⟨(A⁻¹).mulVecLin v, by simp [mul_nonsing_inv _ hA]⟩

/-- Left multiplying by an invertible matrix does not change the rank -/
@[simp]
lemma rank_mul_eq_right_of_isUnit_det [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (A * B).rank = B.rank := by
  let b : Basis m R (m → R) := Pi.basisFun R m
  replace hA : IsUnit (LinearMap.toMatrix b b A.mulVecLin).det := by
    convert hA; rw [← LinearEquiv.eq_symm_apply]; rfl
  have hAB : mulVecLin (A * B) = (LinearEquiv.ofIsUnitDet hA).comp (mulVecLin B) := by ext; simp
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

theorem rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R) (v₁ : Basis m R M₁)
    (v₂ : Basis n R M₂) : A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A)) := by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  have range_e₂ : LinearMap.range e₂ = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact e₂.surjective
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) range_e₂]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := toLin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [toLin_eq_toLin', toLin'_apply'] at aux₁
  rw [Pi.basisFun_apply, LinearMap.coe_stdBasis] at aux₁ aux₂
  simp only [e₁, e₁, LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.refl_apply, aux₁, aux₂,
    LinearMap.coe_single, toLin_self, map_sum, LinearEquiv.map_smul, Basis.equiv_apply]
#align matrix.rank_eq_finrank_range_to_lin Matrix.rank_eq_finrank_range_toLin

theorem rank_le_card_height [Fintype m] [StrongRankCondition R] (A : Matrix m n R) :
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

variable [Field R]

/-- The rank of a diagnonal matrix is the count of non-zero elements on its main diagonal -/
theorem rank_diagonal [Fintype m] [DecidableEq m] [DecidableEq R] (w : m → R) :
    (diagonal w).rank = Fintype.card {i // (w i) ≠ 0} := by
  rw [Matrix.rank, ← Matrix.toLin'_apply', FiniteDimensional.finrank, ← LinearMap.rank,
    LinearMap.rank_diagonal, Cardinal.toNat_natCast]

end Field

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

section StarOrderedField

variable [Fintype m] [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem ker_mulVecLin_conjTranspose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᴴ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, conjTranspose_mul_self_mulVec_eq_zero]
#align matrix.ker_mul_vec_lin_conj_transpose_mul_self Matrix.ker_mulVecLin_conjTranspose_mul_self

theorem rank_conjTranspose_mul_self (A : Matrix m n R) : (Aᴴ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) ?_
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᴴ * A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ * A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]
#align matrix.rank_conj_transpose_mul_self Matrix.rank_conjTranspose_mul_self

-- this follows the proof here https://math.stackexchange.com/a/81903/1896
/-- TODO: prove this in greater generality. -/
@[simp]
theorem rank_conjTranspose (A : Matrix m n R) : Aᴴ.rank = A.rank :=
  le_antisymm
    (((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
      congr_arg _ <| conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)
#align matrix.rank_conj_transpose Matrix.rank_conjTranspose

@[simp]
theorem rank_self_mul_conjTranspose (A : Matrix m n R) : (A * Aᴴ).rank = A.rank := by
  simpa only [rank_conjTranspose, conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self Aᴴ
#align matrix.rank_self_mul_conj_transpose Matrix.rank_self_mul_conjTranspose

end StarOrderedField

section LinearOrderedField

variable [Fintype m] [LinearOrderedField R]

theorem ker_mulVecLin_transpose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h, mulVec_zero]
#align matrix.ker_mul_vec_lin_transpose_mul_self Matrix.ker_mulVecLin_transpose_mul_self

theorem rank_transpose_mul_self (A : Matrix m n R) : (Aᵀ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) ?_
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᵀ * A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᵀ * A)) }
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
theorem rank_self_mul_transpose (A : Matrix m n R) : (A * Aᵀ).rank = A.rank := by
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

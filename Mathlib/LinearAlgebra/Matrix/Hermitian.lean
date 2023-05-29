/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.matrix.hermitian
! leanprover-community/mathlib commit caa58cbf5bfb7f81ccbaca4e8b8ac4bc2b39cc1c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.PiL2

/-! # Hermitian matrices

This file defines hermitian matrices and some basic results about them.

See also `is_self_adjoint`, which generalizes this definition to other star rings.

## Main definition

 * `matrix.is_hermitian` : a matrix `A : matrix n n α` is hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/


namespace Matrix

variable {α β : Type _} {m n : Type _} {A : Matrix n n α}

open scoped Matrix

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner α _ _ x y

section Star

variable [Star α] [Star β]

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def IsHermitian (A : Matrix n n α) : Prop :=
  Aᴴ = A
#align matrix.is_hermitian Matrix.IsHermitian

theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A :=
  h
#align matrix.is_hermitian.eq Matrix.IsHermitian.eq

protected theorem IsHermitian.isSelfAdjoint {A : Matrix n n α} (h : A.IsHermitian) :
    IsSelfAdjoint A :=
  h
#align matrix.is_hermitian.is_self_adjoint Matrix.IsHermitian.isSelfAdjoint

@[ext]
theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h; ext (i j); exact h i j
#align matrix.is_hermitian.ext Matrix.IsHermitian.ext

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  congr_fun (congr_fun h _) _
#align matrix.is_hermitian.apply Matrix.IsHermitian.apply

theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩
#align matrix.is_hermitian.ext_iff Matrix.IsHermitian.ext_iff

@[simp]
theorem IsHermitian.map {A : Matrix n n α} (h : A.IsHermitian) (f : α → β)
    (hf : Function.Semiconj f star star) : (A.map f).IsHermitian :=
  (conjTranspose_map f hf).symm.trans <| h.Eq.symm ▸ rfl
#align matrix.is_hermitian.map Matrix.IsHermitian.map

theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [is_hermitian, conj_transpose, transpose_map]; congr ; exact h
#align matrix.is_hermitian.transpose Matrix.IsHermitian.transpose

@[simp]
theorem isHermitian_transpose_iff (A : Matrix n n α) : Aᵀ.IsHermitian ↔ A.IsHermitian :=
  ⟨by intro h; rw [← transpose_transpose A]; exact is_hermitian.transpose h, IsHermitian.transpose⟩
#align matrix.is_hermitian_transpose_iff Matrix.isHermitian_transpose_iff

theorem IsHermitian.conjTranspose {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ.IsHermitian :=
  h.transpose.map _ fun _ => rfl
#align matrix.is_hermitian.conj_transpose Matrix.IsHermitian.conjTranspose

@[simp]
theorem IsHermitian.submatrix {A : Matrix n n α} (h : A.IsHermitian) (f : m → n) :
    (A.submatrix f f).IsHermitian :=
  (conjTranspose_submatrix _ _ _).trans (h.symm ▸ rfl)
#align matrix.is_hermitian.submatrix Matrix.IsHermitian.submatrix

@[simp]
theorem isHermitian_submatrix_equiv {A : Matrix n n α} (e : m ≃ n) :
    (A.submatrix e e).IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
#align matrix.is_hermitian_submatrix_equiv Matrix.isHermitian_submatrix_equiv

end Star

section InvolutiveStar

variable [InvolutiveStar α]

@[simp]
theorem isHermitian_conjTranspose_iff (A : Matrix n n α) : Aᴴ.IsHermitian ↔ A.IsHermitian :=
  IsSelfAdjoint.star_iff
#align matrix.is_hermitian_conj_transpose_iff Matrix.isHermitian_conjTranspose_iff

/-- A block matrix `A.from_blocks B C D` is hermitian,
    if `A` and `D` are hermitian and `Bᴴ = C`. -/
theorem IsHermitian.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) :
    (A.fromBlocks B C D).IsHermitian :=
  by
  have hCB : Cᴴ = B := by rw [← hBC, conj_transpose_conj_transpose]
  unfold Matrix.IsHermitian
  rw [from_blocks_conj_transpose]
  congr <;> assumption
#align matrix.is_hermitian.from_blocks Matrix.IsHermitian.fromBlocks

/-- This is the `iff` version of `matrix.is_hermitian.from_blocks`. -/
theorem isHermitian_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} :
    (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian :=
  ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, hCB, hD⟩ => IsHermitian.fromBlocks hA hBC hD⟩
#align matrix.is_hermitian_from_blocks_iff Matrix.isHermitian_fromBlocks_iff

end InvolutiveStar

section AddMonoid

variable [AddMonoid α] [StarAddMonoid α] [AddMonoid β] [StarAddMonoid β]

/-- A diagonal matrix is hermitian if the entries are self-adjoint -/
theorem isHermitian_diagonal_of_self_adjoint [DecidableEq n] (v : n → α) (h : IsSelfAdjoint v) :
    (diagonal v).IsHermitian :=
  (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose
        v).trans <|
    congr_arg _ h
#align matrix.is_hermitian_diagonal_of_self_adjoint Matrix.isHermitian_diagonal_of_self_adjoint

/-- A diagonal matrix is hermitian if the entries have the trivial `star` operation
(such as on the reals). -/
@[simp]
theorem isHermitian_diagonal [TrivialStar α] [DecidableEq n] (v : n → α) :
    (diagonal v).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)
#align matrix.is_hermitian_diagonal Matrix.isHermitian_diagonal

@[simp]
theorem isHermitian_zero : (0 : Matrix n n α).IsHermitian :=
  isSelfAdjoint_zero _
#align matrix.is_hermitian_zero Matrix.isHermitian_zero

@[simp]
theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  IsSelfAdjoint.add hA hB
#align matrix.is_hermitian.add Matrix.IsHermitian.add

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [StarAddMonoid α]

theorem isHermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian :=
  isSelfAdjoint_add_star_self A
#align matrix.is_hermitian_add_transpose_self Matrix.isHermitian_add_transpose_self

theorem isHermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian :=
  isSelfAdjoint_star_add_self A
#align matrix.is_hermitian_transpose_add_self Matrix.isHermitian_transpose_add_self

end AddCommMonoid

section AddGroup

variable [AddGroup α] [StarAddMonoid α]

@[simp]
theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian :=
  IsSelfAdjoint.neg h
#align matrix.is_hermitian.neg Matrix.IsHermitian.neg

@[simp]
theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).IsHermitian :=
  IsSelfAdjoint.sub hA hB
#align matrix.is_hermitian.sub Matrix.IsHermitian.sub

end AddGroup

section NonUnitalSemiring

variable [NonUnitalSemiring α] [StarRing α] [NonUnitalSemiring β] [StarRing β]

/-- Note this is more general than `is_self_adjoint.mul_star_self` as `B` can be rectangular. -/
theorem isHermitian_mul_conjTranspose_self [Fintype n] (A : Matrix m n α) : (A ⬝ Aᴴ).IsHermitian :=
  by rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]
#align matrix.is_hermitian_mul_conj_transpose_self Matrix.isHermitian_mul_conjTranspose_self

/-- Note this is more general than `is_self_adjoint.star_mul_self` as `B` can be rectangular. -/
theorem isHermitian_transpose_mul_self [Fintype m] (A : Matrix m n α) : (Aᴴ ⬝ A).IsHermitian := by
  rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]
#align matrix.is_hermitian_transpose_mul_self Matrix.isHermitian_transpose_mul_self

/-- Note this is more general than `is_self_adjoint.conjugate'` as `B` can be rectangular. -/
theorem isHermitian_conjTranspose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
    (hA : A.IsHermitian) : (Bᴴ ⬝ A ⬝ B).IsHermitian := by
  simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
    Matrix.mul_assoc]
#align matrix.is_hermitian_conj_transpose_mul_mul Matrix.isHermitian_conjTranspose_mul_mul

/-- Note this is more general than `is_self_adjoint.conjugate` as `B` can be rectangular. -/
theorem isHermitian_mul_mul_conjTranspose [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
    (hA : A.IsHermitian) : (B ⬝ A ⬝ Bᴴ).IsHermitian := by
  simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
    Matrix.mul_assoc]
#align matrix.is_hermitian_mul_mul_conj_transpose Matrix.isHermitian_mul_mul_conjTranspose

end NonUnitalSemiring

section Semiring

variable [Semiring α] [StarRing α] [Semiring β] [StarRing β]

/-- Note this is more general for matrices than `is_self_adjoint_one` as it does not
require `fintype n`, which is necessary for `monoid (matrix n n R)`. -/
@[simp]
theorem isHermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian :=
  conjTranspose_one
#align matrix.is_hermitian_one Matrix.isHermitian_one

end Semiring

section CommRing

variable [CommRing α] [StarRing α]

theorem IsHermitian.inv [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A⁻¹.IsHermitian := by simp [is_hermitian, conj_transpose_nonsing_inv, hA.eq]
#align matrix.is_hermitian.inv Matrix.IsHermitian.inv

@[simp]
theorem isHermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A] :
    A⁻¹.IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by rw [← inv_inv_of_invertible A]; exact is_hermitian.inv h, IsHermitian.inv⟩
#align matrix.is_hermitian_inv Matrix.isHermitian_inv

theorem IsHermitian.adjugate [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A.adjugate.IsHermitian := by simp [is_hermitian, adjugate_conj_transpose, hA.eq]
#align matrix.is_hermitian.adjugate Matrix.IsHermitian.adjugate

end CommRing

section IsROrC

open IsROrC

variable [IsROrC α] [IsROrC β]

/-- The diagonal elements of a complex hermitian matrix are real. -/
theorem IsHermitian.coe_re_apply_self {A : Matrix n n α} (h : A.IsHermitian) (i : n) :
    (re (A i i) : α) = A i i := by rw [← conj_eq_iff_re, ← star_def, ← conj_transpose_apply, h.eq]
#align matrix.is_hermitian.coe_re_apply_self Matrix.IsHermitian.coe_re_apply_self

/-- The diagonal elements of a complex hermitian matrix are real. -/
theorem IsHermitian.coe_re_diag {A : Matrix n n α} (h : A.IsHermitian) :
    (fun i => (re (A.diag i) : α)) = A.diag :=
  funext h.coe_re_apply_self
#align matrix.is_hermitian.coe_re_diag Matrix.IsHermitian.coe_re_diag

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
theorem isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] {A : Matrix n n α} :
    IsHermitian A ↔ A.toEuclideanLin.IsSymmetric :=
  by
  rw [LinearMap.IsSymmetric, (PiLp.equiv 2 fun _ : n => α).symm.Surjective.Forall₂]
  simp only [to_euclidean_lin_pi_Lp_equiv_symm, EuclideanSpace.inner_piLp_equiv_symm, to_lin'_apply,
    star_mul_vec, dot_product_mul_vec]
  constructor
  · rintro (h : Aᴴ = A) x y
    rw [h]
  · intro h
    ext (i j)
    simpa only [(Pi.single_star i 1).symm, ← star_mul_vec, mul_one, dot_product_single,
      single_vec_mul, star_one, one_mul] using
      h (@Pi.single _ _ _ (fun i => AddZeroClass.toHasZero α) i 1)
        (@Pi.single _ _ _ (fun i => AddZeroClass.toHasZero α) j 1)
#align matrix.is_hermitian_iff_is_symmetric Matrix.isHermitian_iff_isSymmetric

end IsROrC

end Matrix


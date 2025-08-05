/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Data.Matrix.ConjTranspose

/-! # Hermitian matrices

This file defines hermitian matrices and some basic results about them.

See also `IsSelfAdjoint`, which generalizes this definition to other star rings.

## Main definition

* `Matrix.IsHermitian` : a matrix `A : Matrix n n α` is hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/


namespace Matrix

variable {α β : Type*} {m n : Type*} {A : Matrix n n α}

open scoped Matrix

local notation "⟪" x ", " y "⟫" => inner α x y

section Star

variable [Star α] [Star β]

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A

instance (A : Matrix n n α) [Decidable (Aᴴ = A)] : Decidable (IsHermitian A) :=
  inferInstanceAs <| Decidable (_ = _)

theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A := h

protected theorem IsHermitian.isSelfAdjoint {A : Matrix n n α} (h : A.IsHermitian) :
    IsSelfAdjoint A := h

theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h; ext i j; exact h i j

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  congr_fun (congr_fun h _) _

theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩

@[simp]
theorem IsHermitian.map {A : Matrix n n α} (h : A.IsHermitian) (f : α → β)
    (hf : Function.Semiconj f star star) : (A.map f).IsHermitian :=
  (conjTranspose_map f hf).symm.trans <| h.eq.symm ▸ rfl

theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [IsHermitian, conjTranspose, transpose_map]
  exact congr_arg Matrix.transpose h

@[simp]
theorem isHermitian_transpose_iff (A : Matrix n n α) : Aᵀ.IsHermitian ↔ A.IsHermitian :=
  ⟨by intro h; rw [← transpose_transpose A]; exact IsHermitian.transpose h, IsHermitian.transpose⟩

theorem IsHermitian.conjTranspose {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ.IsHermitian :=
  h.transpose.map _ fun _ => rfl

@[simp]
theorem IsHermitian.submatrix {A : Matrix n n α} (h : A.IsHermitian) (f : m → n) :
    (A.submatrix f f).IsHermitian := (conjTranspose_submatrix _ _ _).trans (h.symm ▸ rfl)

@[simp]
theorem isHermitian_submatrix_equiv {A : Matrix n n α} (e : m ≃ n) :
    (A.submatrix e e).IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

end Star

section InvolutiveStar

variable [InvolutiveStar α]

@[simp]
theorem isHermitian_conjTranspose_iff (A : Matrix n n α) : Aᴴ.IsHermitian ↔ A.IsHermitian :=
  IsSelfAdjoint.star_iff

/-- A block matrix `A.from_blocks B C D` is hermitian,
if `A` and `D` are hermitian and `Bᴴ = C`. -/
theorem IsHermitian.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) :
    (A.fromBlocks B C D).IsHermitian := by
  have hCB : Cᴴ = B := by rw [← hBC, conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian
  rw [fromBlocks_conjTranspose, hBC, hCB, hA, hD]

/-- This is the `iff` version of `Matrix.IsHermitian.fromBlocks`. -/
theorem isHermitian_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} :
    (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian :=
  ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, _hCB, hD⟩ => IsHermitian.fromBlocks hA hBC hD⟩

end InvolutiveStar

section AddMonoid

variable [AddMonoid α] [StarAddMonoid α]

/-- A diagonal matrix is hermitian if the entries are self-adjoint (as a vector) -/
theorem isHermitian_diagonal_of_self_adjoint [DecidableEq n] (v : n → α) (h : IsSelfAdjoint v) :
    (diagonal v).IsHermitian :=
  (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose v).trans <| congr_arg _ h

/-- A diagonal matrix is hermitian if each diagonal entry is self-adjoint -/
lemma isHermitian_diagonal_iff [DecidableEq n] {d : n → α} :
    IsHermitian (diagonal d) ↔ (∀ i : n, IsSelfAdjoint (d i)) := by
  simp [isSelfAdjoint_iff, IsHermitian, conjTranspose, diagonal_transpose, diagonal_map]

/-- A diagonal matrix is hermitian if the entries have the trivial `star` operation
(such as on the reals). -/
@[simp]
theorem isHermitian_diagonal [TrivialStar α] [DecidableEq n] (v : n → α) :
    (diagonal v).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

@[simp]
theorem isHermitian_zero : (0 : Matrix n n α).IsHermitian :=
  IsSelfAdjoint.zero _

@[simp]
theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  IsSelfAdjoint.add hA hB

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [StarAddMonoid α]

theorem isHermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian :=
  IsSelfAdjoint.add_star_self A

theorem isHermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian :=
  IsSelfAdjoint.star_add_self A

end AddCommMonoid

section AddGroup

variable [AddGroup α] [StarAddMonoid α]

@[simp]
theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian :=
  IsSelfAdjoint.neg h

@[simp]
theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).IsHermitian :=
  IsSelfAdjoint.sub hA hB

end AddGroup

section NonUnitalSemiring

variable [NonUnitalSemiring α] [StarRing α]

/-- Note this is more general than `IsSelfAdjoint.mul_star_self` as `B` can be rectangular. -/
theorem isHermitian_mul_conjTranspose_self [Fintype n] (A : Matrix m n α) :
    (A * Aᴴ).IsHermitian := by rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Note this is more general than `IsSelfAdjoint.star_mul_self` as `B` can be rectangular. -/
theorem isHermitian_transpose_mul_self [Fintype m] (A : Matrix m n α) : (Aᴴ * A).IsHermitian := by
  rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Note this is more general than `IsSelfAdjoint.conjugate'` as `B` can be rectangular. -/
theorem isHermitian_conjTranspose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
    (hA : A.IsHermitian) : (Bᴴ * A * B).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/-- Note this is more general than `IsSelfAdjoint.conjugate` as `B` can be rectangular. -/
theorem isHermitian_mul_mul_conjTranspose [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
    (hA : A.IsHermitian) : (B * A * Bᴴ).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

lemma commute_iff [Fintype n] {A B : Matrix n n α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : Commute A B ↔ (A * B).IsHermitian :=
  hA.isSelfAdjoint.commute_iff hB.isSelfAdjoint

end NonUnitalSemiring

section Semiring

variable [Semiring α] [StarRing α]

/-- Note this is more general for matrices than `isSelfAdjoint_one` as it does not
require `Fintype n`, which is necessary for `Monoid (Matrix n n R)`. -/
@[simp]
theorem isHermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian :=
  conjTranspose_one

@[simp]
theorem isHermitian_natCast [DecidableEq n] (d : ℕ) : (d : Matrix n n α).IsHermitian :=
  conjTranspose_natCast _

theorem IsHermitian.pow [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsHermitian) (k : ℕ) :
    (A ^ k).IsHermitian := IsSelfAdjoint.pow h _

end Semiring

section Ring
variable [Ring α] [StarRing α]

@[simp]
theorem isHermitian_intCast [DecidableEq n] (d : ℤ) : (d : Matrix n n α).IsHermitian :=
  conjTranspose_intCast _

end Ring

section CommRing

variable [CommRing α] [StarRing α]

theorem IsHermitian.inv [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A⁻¹.IsHermitian := by simp [IsHermitian, conjTranspose_nonsing_inv, hA.eq]

@[simp]
theorem isHermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A] :
    A⁻¹.IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by rw [← inv_inv_of_invertible A]; exact IsHermitian.inv h, IsHermitian.inv⟩

theorem IsHermitian.adjugate [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A.adjugate.IsHermitian := by simp [IsHermitian, adjugate_conjTranspose, hA.eq]

/-- Note that `IsSelfAdjoint.zpow` does not apply to matrices as they are not a division ring. -/
theorem IsHermitian.zpow [Fintype m] [DecidableEq m] {A : Matrix m m α} (h : A.IsHermitian)
    (k : ℤ) :
    (A ^ k).IsHermitian := by
  rw [IsHermitian, conjTranspose_zpow, h]

end CommRing

section RCLike

open RCLike

variable [RCLike α]

/-- The diagonal elements of a complex hermitian matrix are real. -/
theorem IsHermitian.coe_re_apply_self {A : Matrix n n α} (h : A.IsHermitian) (i : n) :
    (re (A i i) : α) = A i i := by rw [← conj_eq_iff_re, ← star_def, ← conjTranspose_apply, h.eq]

/-- The diagonal elements of a complex hermitian matrix are real. -/
theorem IsHermitian.coe_re_diag {A : Matrix n n α} (h : A.IsHermitian) :
    (fun i => (re (A.diag i) : α)) = A.diag :=
  funext h.coe_re_apply_self

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
theorem isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] {A : Matrix n n α} :
    IsHermitian A ↔ A.toEuclideanLin.IsSymmetric := by
  rw [LinearMap.IsSymmetric, (WithLp.toLp_surjective _).forall₂]
  simp only [toEuclideanLin_toLp, Matrix.toLin'_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_mulVec]
  constructor
  · rintro (h : Aᴴ = A) x y
    rw [dotProduct_comm, ← dotProduct_mulVec, h, dotProduct_comm]
  · intro h
    ext i j
    simpa [(Pi.single_star i 1).symm] using h (Pi.single i 1) (Pi.single j 1)

end RCLike

end Matrix

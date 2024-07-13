/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Star.Unitary

#align_import linear_algebra.unitary_group from "leanprover-community/mathlib"@"2705404e701abc6b3127da906f40bae062a169c9"

/-!
# The Unitary Group

This file defines elements of the unitary group `Matrix.unitaryGroup n α`, where `α` is a
`StarRing`. This consists of all `n` by `n` matrices with entries in `α` such that the
star-transpose is its inverse. In addition, we define the group structure on
`Matrix.unitaryGroup n α`, and the embedding into the general linear group
`LinearMap.GeneralLinearGroup α (n → α)`.

We also define the orthogonal group `Matrix.orthogonalGroup n β`, where `β` is a `CommRing`.

## Main Definitions

* `Matrix.unitaryGroup` is the submonoid of matrices where the star-transpose is the inverse; the
  group structure (under multiplication) is inherited from a more general `unitary` construction.
* `Matrix.UnitaryGroup.embeddingGL` is the embedding `Matrix.unitaryGroup n α → GLₙ(α)`, where
  `GLₙ(α)` is `LinearMap.GeneralLinearGroup α (n → α)`.
* `Matrix.orthogonalGroup` is the submonoid of matrices where the transpose is the inverse.

## References

* https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/


universe u v

namespace Matrix

open LinearMap Matrix

section

variable (n : Type u) [DecidableEq n] [Fintype n]
variable (α : Type v) [CommRing α] [StarRing α]

/-- `Matrix.unitaryGroup n` is the group of `n` by `n` matrices where the star-transpose is the
inverse.
-/
abbrev unitaryGroup :=
  unitary (Matrix n n α)
#align matrix.unitary_group Matrix.unitaryGroup

end

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}

theorem mem_unitaryGroup_iff : A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1 := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA
#align matrix.mem_unitary_group_iff Matrix.mem_unitaryGroup_iff

theorem mem_unitaryGroup_iff' : A ∈ Matrix.unitaryGroup n α ↔ star A * A = 1 := by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA
#align matrix.mem_unitary_group_iff' Matrix.mem_unitaryGroup_iff'

theorem det_of_mem_unitary {A : Matrix n n α} (hA : A ∈ Matrix.unitaryGroup n α) :
    A.det ∈ unitary α := by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2
#align matrix.det_of_mem_unitary Matrix.det_of_mem_unitary

namespace UnitaryGroup

instance coeMatrix : Coe (unitaryGroup n α) (Matrix n n α) :=
  ⟨Subtype.val⟩
#align matrix.unitary_group.coe_matrix Matrix.UnitaryGroup.coeMatrix

instance coeFun : CoeFun (unitaryGroup n α) fun _ => n → n → α where coe A := A.val
#align matrix.unitary_group.coe_fun Matrix.UnitaryGroup.coeFun

/-- `Matrix.UnitaryGroup.toLin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `Matrix.unitaryGroup n` is defined, we show in
`Matrix.UnitaryGroup.toLinearEquiv` that this gives a linear equivalence.
-/
def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1
#align matrix.unitary_group.to_lin' Matrix.UnitaryGroup.toLin'

theorem ext_iff (A B : unitaryGroup n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff_val.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩
#align matrix.unitary_group.ext_iff Matrix.UnitaryGroup.ext_iff

@[ext]
theorem ext (A B : unitaryGroup n α) : (∀ i j, A i j = B i j) → A = B :=
  (UnitaryGroup.ext_iff A B).mpr
#align matrix.unitary_group.ext Matrix.UnitaryGroup.ext

theorem star_mul_self (A : unitaryGroup n α) : star A.1 * A.1 = 1 :=
  A.2.1
#align matrix.unitary_group.star_mul_self Matrix.UnitaryGroup.star_mul_self

@[simp]
theorem det_isUnit (A : unitaryGroup n α) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp <| (unitary.toUnits A).isUnit

section CoeLemmas

variable (A B : unitaryGroup n α)

@[simp] theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) := rfl
#align matrix.unitary_group.inv_val Matrix.UnitaryGroup.inv_val

@[simp] theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) := rfl
#align matrix.unitary_group.inv_apply Matrix.UnitaryGroup.inv_apply

@[simp] theorem mul_val : ↑(A * B) = A.1 * B.1 := rfl
#align matrix.unitary_group.mul_val Matrix.UnitaryGroup.mul_val

@[simp] theorem mul_apply : ⇑(A * B) = A.1 * B.1 := rfl
#align matrix.unitary_group.mul_apply Matrix.UnitaryGroup.mul_apply

@[simp] theorem one_val : ↑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl
#align matrix.unitary_group.one_val Matrix.UnitaryGroup.one_val

@[simp] theorem one_apply : ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl
#align matrix.unitary_group.one_apply Matrix.UnitaryGroup.one_apply

@[simp]
theorem toLin'_mul : toLin' (A * B) = (toLin' A).comp (toLin' B) :=
  Matrix.toLin'_mul A.1 B.1
#align matrix.unitary_group.to_lin'_mul Matrix.UnitaryGroup.toLin'_mul

@[simp]
theorem toLin'_one : toLin' (1 : unitaryGroup n α) = LinearMap.id :=
  Matrix.toLin'_one
#align matrix.unitary_group.to_lin'_one Matrix.UnitaryGroup.toLin'_one

end CoeLemmas

-- Porting note (#11215): TODO: redefine `toGL`/`embeddingGL` as in this example:
example : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  .toHomUnits ⟨⟨toLin', toLin'_one⟩, toLin'_mul⟩
-- Porting note: then we can get `toLinearEquiv` from `GeneralLinearGroup.toLinearEquiv`

/-- `Matrix.unitaryGroup.toLinearEquiv A` is matrix multiplication of vectors by `A`, as a linear
equivalence. -/
def toLinearEquiv (A : unitaryGroup n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_left_inv, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLin' A⁻¹) x = toLin' (A * A⁻¹) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_right_inv, toLin'_one, id_apply] }
#align matrix.unitary_group.to_linear_equiv Matrix.UnitaryGroup.toLinearEquiv

/-- `Matrix.unitaryGroup.toGL` is the map from the unitary group to the general linear group -/
def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n → α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.to_GL Matrix.UnitaryGroup.toGL

theorem coe_toGL (A : unitaryGroup n α) : (toGL A).1 = toLin' A := rfl
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.coe_to_GL Matrix.UnitaryGroup.coe_toGL

@[simp]
theorem toGL_one : toGL (1 : unitaryGroup n α) = 1 := Units.ext <| by
  simp only [coe_toGL, toLin'_one]
  rfl
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.to_GL_one Matrix.UnitaryGroup.toGL_one

@[simp]
theorem toGL_mul (A B : unitaryGroup n α) : toGL (A * B) = toGL A * toGL B := Units.ext <| by
  simp only [coe_toGL, toLin'_mul]
  rfl
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.to_GL_mul Matrix.UnitaryGroup.toGL_mul

/-- `Matrix.unitaryGroup.embeddingGL` is the embedding from `Matrix.unitaryGroup n α` to
`LinearMap.GeneralLinearGroup n α`. -/
def embeddingGL : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩
set_option linter.uppercaseLean3 false in
#align matrix.unitary_group.embedding_GL Matrix.UnitaryGroup.embeddingGL

end UnitaryGroup

section specialUnitaryGroup

variable (n) (α)

/-- `Matrix.specialUnitaryGroup` is the group of unitary `n` by `n` matrices where the determinant
is 1. (This definition is only correct if 2 is invertible.)-/
abbrev specialUnitaryGroup := unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom

variable {n} {α}

theorem mem_specialUnitaryGroup_iff :
    A ∈ specialUnitaryGroup n α ↔ A ∈ unitaryGroup n α ∧ A.det = 1 :=
  Iff.rfl

end specialUnitaryGroup

section OrthogonalGroup

variable (n) (β : Type v) [CommRing β]

-- Porting note (#11215): TODO: will lemmas about `Matrix.orthogonalGroup` work without making
-- `starRingOfComm` a local instance? E.g., can we talk about unitary group and orthogonal group
-- at the same time?
attribute [local instance] starRingOfComm

/-- `Matrix.orthogonalGroup n` is the group of `n` by `n` matrices where the transpose is the
inverse. -/
abbrev orthogonalGroup := unitaryGroup n β
#align matrix.orthogonal_group Matrix.orthogonalGroup

theorem mem_orthogonalGroup_iff {A : Matrix n n β} :
    A ∈ Matrix.orthogonalGroup n β ↔ A * star A = 1 := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA
#align matrix.mem_orthogonal_group_iff Matrix.mem_orthogonalGroup_iff

theorem mem_orthogonalGroup_iff' {A : Matrix n n β} :
    A ∈ Matrix.orthogonalGroup n β ↔ star A * A = 1 := by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA
#align matrix.mem_orthogonal_group_iff' Matrix.mem_orthogonalGroup_iff'

end OrthogonalGroup

section specialOrthogonalGroup

variable (n) (β : Type v) [CommRing β]

attribute [local instance] starRingOfComm

/-- `Matrix.specialOrthogonalGroup n` is the group of orthogonal `n` by `n` where the determinant
is one. (This definition is only correct if 2 is invertible.)-/
abbrev specialOrthogonalGroup := specialUnitaryGroup n β

variable {n} {β} {A : Matrix n n β}

theorem mem_specialOrthogonalGroup_iff :
    A ∈ specialOrthogonalGroup n β ↔ A ∈ orthogonalGroup n β ∧ A.det = 1 :=
  Iff.rfl

end specialOrthogonalGroup

end Matrix

/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Unitary Group

This file defines elements of the unitary group `Matrix.unitaryGroup n α`, where `α` is a
`StarRing`. This consists of all `n` by `n` matrices with entries in `α` such that the
star-transpose is its inverse. In addition, we define the group structure on
`Matrix.unitaryGroup n α`, and the embedding into the general linear group
`LinearMap.GeneralLinearGroup α (n → α)`.

We also define the orthogonal group `Matrix.orthogonalGroup n R`, where `R` is a `CommRing`.

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
abbrev unitaryGroup : Submonoid (Matrix n n α) :=
  unitary (Matrix n n α)

-- the group and star structure is already defined in another file
example : Group (unitaryGroup n α) := inferInstance
example : StarMul (unitaryGroup n α) := inferInstance

end

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}

theorem mem_unitaryGroup_iff : A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1 := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA

theorem mem_unitaryGroup_iff' : A ∈ Matrix.unitaryGroup n α ↔ star A * A = 1 := by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA

theorem det_of_mem_unitary {A : Matrix n n α} (hA : A ∈ Matrix.unitaryGroup n α) :
    A.det ∈ unitary α := by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2

open scoped Kronecker in
/-- The kronecker product of two unitary matrices is unitary.

This is stated for `unitary` instead of `unitaryGroup` as it holds even for
non-commutative coefficients. -/
theorem kronecker_mem_unitary {R m : Type*} [Semiring R] [StarRing R] [Fintype m]
    [DecidableEq m] {U₁ : Matrix n n R} {U₂ : Matrix m m R}
    (hU₁ : U₁ ∈ unitary (Matrix n n R)) (hU₂ : U₂ ∈ unitary (Matrix m m R)) :
    U₁ ⊗ₖ U₂ ∈ unitary (Matrix (n × m) (n × m) R) := by
  simp_rw [unitary.mem_iff, star_eq_conjTranspose, conjTranspose_kronecker']
  constructor <;> ext <;> simp only [mul_apply, submatrix_apply, kroneckerMap_apply, Prod.fst_swap,
    conjTranspose_apply, ← star_apply, Prod.snd_swap, ← mul_assoc]
  · simp_rw [mul_assoc _ (star U₁ _ _), ← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₁.1, Matrix.one_apply,
      mul_boole, ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₂.1,
      Matrix.one_apply, Finset.sum_const_zero, ← ite_and, Prod.eq_iff_fst_eq_snd_eq]
  · simp_rw [mul_assoc _ _ (star U₂ _ _), ← Finset.univ_product_univ, Finset.sum_product,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₂.2, Matrix.one_apply, mul_boole,
      ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₁.2, Matrix.one_apply,
      Finset.sum_const_zero, ← ite_and, and_comm, Prod.eq_iff_fst_eq_snd_eq]

namespace UnitaryGroup

instance coeMatrix : Coe (unitaryGroup n α) (Matrix n n α) :=
  ⟨Subtype.val⟩

instance coeFun : CoeFun (unitaryGroup n α) fun _ => n → n → α where coe A := A.val

/-- `Matrix.UnitaryGroup.toLin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `Matrix.unitaryGroup n` is defined, we show in
`Matrix.UnitaryGroup.toLinearEquiv` that this gives a linear equivalence.
-/
def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1

theorem ext_iff (A B : unitaryGroup n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]
theorem ext (A B : unitaryGroup n α) : (∀ i j, A i j = B i j) → A = B :=
  (UnitaryGroup.ext_iff A B).mpr

theorem star_mul_self (A : unitaryGroup n α) : star A.1 * A.1 = 1 :=
  A.2.1

@[simp]
theorem det_isUnit (A : unitaryGroup n α) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp <| (unitary.toUnits A).isUnit

section CoeLemmas

variable (A B : unitaryGroup n α)

@[simp] theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) := rfl

@[simp] theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) := rfl

@[simp] theorem mul_val : ↑(A * B) = A.1 * B.1 := rfl

@[simp] theorem mul_apply : ⇑(A * B) = A.1 * B.1 := rfl

@[simp] theorem one_val : ↑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl

@[simp] theorem one_apply : ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl

@[simp]
theorem toLin'_mul : toLin' (A * B) = (toLin' A).comp (toLin' B) :=
  Matrix.toLin'_mul A.1 B.1

@[simp]
theorem toLin'_one : toLin' (1 : unitaryGroup n α) = LinearMap.id :=
  Matrix.toLin'_one

end CoeLemmas

-- TODO: redefine `toGL`/`embeddingGL` as in the following example,
-- so that we can get `toLinearEquiv` from `GeneralLinearGroup.toLinearEquiv`
example : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  .toHomUnits ⟨⟨toLin', toLin'_one⟩, toLin'_mul⟩

/-- `Matrix.unitaryGroup.toLinearEquiv A` is matrix multiplication of vectors by `A`, as a linear
equivalence. -/
def toLinearEquiv (A : unitaryGroup n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [inv_mul_cancel, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLin' A⁻¹) x = toLin' (A * A⁻¹) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_inv_cancel, toLin'_one, id_apply] }

/-- `Matrix.unitaryGroup.toGL` is the map from the unitary group to the general linear group -/
def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n → α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)

theorem coe_toGL (A : unitaryGroup n α) : (toGL A).1 = toLin' A := rfl

@[simp]
theorem toGL_one : toGL (1 : unitaryGroup n α) = 1 := Units.ext <| by
  simp only [coe_toGL, toLin'_one]
  rfl

@[simp]
theorem toGL_mul (A B : unitaryGroup n α) : toGL (A * B) = toGL A * toGL B := Units.ext <| by
  simp only [coe_toGL, toLin'_mul]
  rfl

/-- `Matrix.unitaryGroup.embeddingGL` is the embedding from `Matrix.unitaryGroup n α` to
`LinearMap.GeneralLinearGroup n α`. -/
def embeddingGL : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩

end UnitaryGroup

section specialUnitaryGroup

variable (n) (α)

/-- `Matrix.specialUnitaryGroup` is the group of unitary `n` by `n` matrices where the determinant
is 1. (This definition is only correct if 2 is invertible.) -/
def specialUnitaryGroup : Submonoid (Matrix n n α) := unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom

variable {n} {α}

theorem specialUnitaryGroup_le_unitaryGroup : specialUnitaryGroup n α ≤ unitaryGroup n α :=
  inf_le_left

theorem mem_specialUnitaryGroup_iff :
    A ∈ specialUnitaryGroup n α ↔ A ∈ unitaryGroup n α ∧ A.det = 1 :=
  Iff.rfl

instance : StarMul (specialUnitaryGroup n α) where
  star A := ⟨star A, by simpa using A.prop.1, by have := A.prop.2; simp_all [star_eq_conjTranspose]⟩
  star_mul A B := Subtype.ext <| star_mul A.1 B.1
  star_involutive A := Subtype.ext <| star_involutive A.1

@[simp, norm_cast]
theorem specialUnitaryGroup.coe_star (A : specialUnitaryGroup n α) : (star A).1 = star A.1 := rfl

instance : Inv (specialUnitaryGroup n α) where inv := star

theorem star_eq_inv (A : specialUnitaryGroup n α) : star A = A⁻¹ :=
  rfl

instance : Group (specialUnitaryGroup n α) where
  inv_mul_cancel A := Subtype.ext A.prop.1.1

end specialUnitaryGroup

section OrthogonalGroup

variable (n) (R : Type v) [CommRing R]

-- TODO: will lemmas about `Matrix.orthogonalGroup` work without making
-- `starRingOfComm` a local instance? E.g., can we talk about unitary group and orthogonal group
-- at the same time?
attribute [local instance] starRingOfComm

/-- `Matrix.orthogonalGroup n` is the group of `n` by `n` matrices where the transpose is the
inverse. -/
abbrev orthogonalGroup := unitaryGroup n R

theorem mem_orthogonalGroup_iff {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔ A * Aᵀ = 1 :=
  mem_unitaryGroup_iff

theorem mem_orthogonalGroup_iff' {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔ Aᵀ * A = 1 :=
  mem_unitaryGroup_iff'

end OrthogonalGroup

section specialOrthogonalGroup

variable (n) (R : Type v) [CommRing R]

attribute [local instance] starRingOfComm

/-- `Matrix.specialOrthogonalGroup n` is the group of orthogonal `n` by `n` where the determinant
is one. (This definition is only correct if 2 is invertible.) -/
abbrev specialOrthogonalGroup : Submonoid (Matrix n n R) := specialUnitaryGroup n R

variable {n} {R} {A : Matrix n n R}

-- the group and star structure is automatic from `specialUnitaryGroup`
example : Group (specialOrthogonalGroup n R) := inferInstance
example : StarMul (specialOrthogonalGroup n R) := inferInstance

theorem mem_specialOrthogonalGroup_iff :
    A ∈ specialOrthogonalGroup n R ↔ A ∈ orthogonalGroup n R ∧ A.det = 1 :=
  Iff.rfl

@[simp]
lemma of_mem_specialOrthogonalGroup_fin_two_iff {a b c d : R} :
    !![a, b; c, d] ∈ Matrix.specialOrthogonalGroup (Fin 2) R ↔
      a = d ∧ b = -c ∧ a ^ 2 + b ^ 2 = 1 := by
  trans ((a * a + b * b = 1 ∧ a * c + b * d = 0) ∧
    c * a + d * b = 0 ∧ c * c + d * d = 1) ∧ a * d - b * c = 1
  · simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
      ← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]
  grind

lemma mem_specialOrthogonalGroup_fin_two_iff {M : Matrix (Fin 2) (Fin 2) R} :
    M ∈ Matrix.specialOrthogonalGroup (Fin 2) R ↔
      M 0 0 = M 1 1 ∧ M 0 1 = - M 1 0 ∧ M 0 0 ^ 2 + M 0 1 ^ 2 = 1 := by
  rw [← M.etaExpand_eq]
  exact of_mem_specialOrthogonalGroup_fin_two_iff

end specialOrthogonalGroup

end Matrix

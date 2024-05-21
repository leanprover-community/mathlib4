/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

#align_import algebra.quaternion_basis from "leanprover-community/mathlib"@"3aa5b8a9ed7a7cabd36e6e1d022c9858ab8a8c2d"

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `QuaternionAlgebra.Basis A c₁ c₂`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂]`.
* `QuaternionAlgebra.Basis.self R`: the canonical basis for `ℍ[R,c₁,c₂]`.
* `QuaternionAlgebra.Basis.compHom b f`: transform a basis `b` by an AlgHom `f`.
* `QuaternionAlgebra.lift`: Define an `AlgHom` out of `ℍ[R,c₁,c₂]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `Complex.lift`,
  but takes a bundled `QuaternionAlgebra.Basis` instead of just a `Subtype` as the amount of
  data / proves is non-negligible.
-/


open Quaternion

namespace QuaternionAlgebra

/-- A quaternion basis contains the information both sufficient and necessary to construct an
`R`-algebra homomorphism from `ℍ[R,c₁,c₂]` to `A`; or equivalently, a surjective
`R`-algebra homomorphism from `ℍ[R,c₁,c₂]` to an `R`-subalgebra of `A`.

Note that for definitional convenience, `k` is provided as a field even though `i_mul_j` fully
determines it. -/
structure Basis {R : Type*} (A : Type*) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ : R) where
  (i j k : A)
  i_mul_i : i * i = c₁ • (1 : A)
  j_mul_j : j * j = c₂ • (1 : A)
  i_mul_j : i * j = k
  j_mul_i : j * i = -k
#align quaternion_algebra.basis QuaternionAlgebra.Basis

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable {c₁ c₂ : R}

namespace Basis

/-- Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `q₁ = q₂`. -/
@[ext]
protected theorem ext ⦃q₁ q₂ : Basis A c₁ c₂⦄ (hi : q₁.i = q₂.i) (hj : q₁.j = q₂.j) : q₁ = q₂ := by
  cases q₁; rename_i q₁_i_mul_j _
  cases q₂; rename_i q₂_i_mul_j _
  congr
  rw [← q₁_i_mul_j, ← q₂_i_mul_j]
  congr
#align quaternion_algebra.basis.ext QuaternionAlgebra.Basis.ext

variable (R)

/-- There is a natural quaternionic basis for the `QuaternionAlgebra`. -/
@[simps i j k]
protected def self : Basis ℍ[R,c₁,c₂] c₁ c₂ where
  i := ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp
#align quaternion_algebra.basis.self QuaternionAlgebra.Basis.self

variable {R}

instance : Inhabited (Basis ℍ[R,c₁,c₂] c₁ c₂) :=
  ⟨Basis.self R⟩

variable (q : Basis A c₁ c₂)

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

@[simp]
theorem i_mul_k : q.i * q.k = c₁ • q.j := by
  rw [← i_mul_j, ← mul_assoc, i_mul_i, smul_mul_assoc, one_mul]
#align quaternion_algebra.basis.i_mul_k QuaternionAlgebra.Basis.i_mul_k

@[simp]
theorem k_mul_i : q.k * q.i = -c₁ • q.j := by
  rw [← i_mul_j, mul_assoc, j_mul_i, mul_neg, i_mul_k, neg_smul]
#align quaternion_algebra.basis.k_mul_i QuaternionAlgebra.Basis.k_mul_i

@[simp]
theorem k_mul_j : q.k * q.j = c₂ • q.i := by
  rw [← i_mul_j, mul_assoc, j_mul_j, mul_smul_comm, mul_one]
#align quaternion_algebra.basis.k_mul_j QuaternionAlgebra.Basis.k_mul_j

@[simp]
theorem j_mul_k : q.j * q.k = -c₂ • q.i := by
  rw [← i_mul_j, ← mul_assoc, j_mul_i, neg_mul, k_mul_j, neg_smul]
#align quaternion_algebra.basis.j_mul_k QuaternionAlgebra.Basis.j_mul_k

@[simp]
theorem k_mul_k : q.k * q.k = -((c₁ * c₂) • (1 : A)) := by
  rw [← i_mul_j, mul_assoc, ← mul_assoc q.j _ _, j_mul_i, ← i_mul_j, ← mul_assoc, mul_neg, ←
    mul_assoc, i_mul_i, smul_mul_assoc, one_mul, neg_mul, smul_mul_assoc, j_mul_j, smul_smul]
#align quaternion_algebra.basis.k_mul_k QuaternionAlgebra.Basis.k_mul_k

/-- Intermediate result used to define `QuaternionAlgebra.Basis.liftHom`. -/
def lift (x : ℍ[R,c₁,c₂]) : A :=
  algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k
#align quaternion_algebra.basis.lift QuaternionAlgebra.Basis.lift

theorem lift_zero : q.lift (0 : ℍ[R,c₁,c₂]) = 0 := by simp [lift]
#align quaternion_algebra.basis.lift_zero QuaternionAlgebra.Basis.lift_zero

theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂]) = 1 := by simp [lift]
#align quaternion_algebra.basis.lift_one QuaternionAlgebra.Basis.lift_one

theorem lift_add (x y : ℍ[R,c₁,c₂]) : q.lift (x + y) = q.lift x + q.lift y := by
  simp only [lift, add_re, map_add, add_imI, add_smul, add_imJ, add_imK]
  abel
#align quaternion_algebra.basis.lift_add QuaternionAlgebra.Basis.lift_add

theorem lift_mul (x y : ℍ[R,c₁,c₂]) : q.lift (x * y) = q.lift x * q.lift y := by
  simp only [lift, Algebra.algebraMap_eq_smul_one]
  simp_rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, add_smul, ← add_assoc, mul_neg, neg_smul]
  simp only [mul_right_comm _ _ (c₁ * c₂), mul_comm _ (c₁ * c₂)]
  simp only [mul_comm _ c₁, mul_right_comm _ _ c₁]
  simp only [mul_comm _ c₂, mul_right_comm _ _ c₂]
  simp only [← mul_comm c₁ c₂, ← mul_assoc]
  simp only [mul_re, sub_eq_add_neg, add_smul, neg_smul, mul_imI, ← add_assoc, mul_imJ, mul_imK]
  abel
#align quaternion_algebra.basis.lift_mul QuaternionAlgebra.Basis.lift_mul

theorem lift_smul (r : R) (x : ℍ[R,c₁,c₂]) : q.lift (r • x) = r • q.lift x := by
  simp [lift, mul_smul, ← Algebra.smul_def]
#align quaternion_algebra.basis.lift_smul QuaternionAlgebra.Basis.lift_smul

/-- A `QuaternionAlgebra.Basis` implies an `AlgHom` from the quaternions. -/
@[simps!]
def liftHom : ℍ[R,c₁,c₂] →ₐ[R] A :=
  AlgHom.mk'
    { toFun := q.lift
      map_zero' := q.lift_zero
      map_one' := q.lift_one
      map_add' := q.lift_add
      map_mul' := q.lift_mul } q.lift_smul
#align quaternion_algebra.basis.lift_hom QuaternionAlgebra.Basis.liftHom

/-- Transform a `QuaternionAlgebra.Basis` through an `AlgHom`. -/
@[simps i j k]
def compHom (F : A →ₐ[R] B) : Basis B c₁ c₂ where
  i := F q.i
  i_mul_i := by rw [← F.map_mul, q.i_mul_i, F.map_smul, F.map_one]
  j := F q.j
  j_mul_j := by rw [← F.map_mul, q.j_mul_j, F.map_smul, F.map_one]
  k := F q.k
  i_mul_j := by rw [← F.map_mul, q.i_mul_j]
  j_mul_i := by rw [← F.map_mul, q.j_mul_i, F.map_neg]
#align quaternion_algebra.basis.comp_hom QuaternionAlgebra.Basis.compHom

end Basis

/-- A quaternionic basis on `A` is equivalent to a map from the quaternion algebra to `A`. -/
@[simps]
def lift : Basis A c₁ c₂ ≃ (ℍ[R,c₁,c₂] →ₐ[R] A) where
  toFun := Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [Basis.lift]
  right_inv F := by
    ext
    dsimp [Basis.lift]
    rw [← F.commutes]
    simp only [← F.commutes, ← F.map_smul, ← F.map_add, mk_add_mk, smul_mk, smul_zero,
      algebraMap_eq]
    congr <;> simp
#align quaternion_algebra.lift QuaternionAlgebra.lift

/-- Two `R`-algebra morphisms from a quaternion algebra are equal if they agree on `i` and `j`. -/
@[ext]
theorem hom_ext ⦃f g : ℍ[R,c₁,c₂] →ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
  lift.symm.injective <| Basis.ext hi hj

end QuaternionAlgebra

namespace Quaternion
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

open QuaternionAlgebra (Basis)

/-- Two `R`-algebra morphisms from the quaternions are equal if they agree on `i` and `j`. -/
@[ext]
theorem hom_ext ⦃f g : ℍ[R] →ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
  QuaternionAlgebra.hom_ext hi hj

end Quaternion

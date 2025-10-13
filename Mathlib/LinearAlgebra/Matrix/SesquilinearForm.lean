/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Moritz Doll
-/
import Mathlib.Algebra.GroupWithZero.Action.Opposite
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Sesquilinear form

This file defines the conversion between sesquilinear maps and matrices.

## Main definitions

* `Matrix.toLinearMap₂` given a basis define a bilinear map
* `Matrix.toLinearMap₂'` define the bilinear map on `n → R`
* `LinearMap.toMatrix₂`: calculate the matrix coefficients of a bilinear map
* `LinearMap.toMatrix₂'`: calculate the matrix coefficients of a bilinear map on `n → R`

## TODO

At the moment this is quite a literal port from `Matrix.BilinearForm`. Everything should be
generalized to fully semibilinear forms.

## Tags

Sesquilinear form, Sesquilinear map, matrix, basis

-/

open Finset LinearMap Matrix Module
open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

section AuxToLinearMap

variable [Semiring R₁] [Semiring S₁] [Semiring R₂] [Semiring S₂] [AddCommMonoid N₂]
  [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₂ S₁ N₂]
variable [Fintype n] [Fintype m]
variable (σ₁ : R₁ →+* S₁) (σ₂ : R₂ →+* S₂)

/-- The map from `Matrix n n R` to bilinear maps on `n → R`.

This is an auxiliary definition for the equivalence `Matrix.toLinearMap₂'`. -/
def Matrix.toLinearMap₂'Aux (f : Matrix n m N₂) : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂ :=
  -- porting note: we don't seem to have `∑ i j` as valid notation yet
  mk₂'ₛₗ σ₁ σ₂ (fun (v : n → R₁) (w : m → R₂) => ∑ i, ∑ j, σ₂ (w j) • σ₁ (v i) • f i j)
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, smul_add, sum_add_distrib, add_smul])
    (fun c v w => by
      simp only [Pi.smul_apply, smul_sum, smul_eq_mul, σ₁.map_mul, ← smul_comm _ (σ₁ c),
        MulAction.mul_smul])
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, add_smul, sum_add_distrib])
    (fun _ v w => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, MulAction.mul_smul, smul_sum])

variable [DecidableEq n] [DecidableEq m]

theorem Matrix.toLinearMap₂'Aux_single (f : Matrix n m N₂) (i : n) (j : m) :
    f.toLinearMap₂'Aux σ₁ σ₂ (Pi.single i 1) (Pi.single j 1) = f i j := by
  rw [Matrix.toLinearMap₂'Aux, mk₂'ₛₗ_apply]
  have : (∑ i', ∑ j', (if i = i' then (1 : S₁) else (0 : S₁)) •
        (if j = j' then (1 : S₂) else (0 : S₂)) • f i' j') =
      f i j := by
    simp_rw [← Finset.smul_sum]
    simp only [ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop

end AuxToLinearMap

section AuxToMatrix

section CommSemiring

variable [CommSemiring R] [Semiring R₁] [Semiring S₁] [Semiring R₂] [Semiring S₂]
variable [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid N₂]
  [Module R N₂] [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂]
  [SMulCommClass S₂ S₁ N₂]
variable {σ₁ : R₁ →+* S₁} {σ₂ : R₂ →+* S₂}
variable (R)

/-- The linear map from sesquilinear maps to `Matrix n m N₂` given an `n`-indexed basis for `M₁`
and an `m`-indexed basis for `M₂`.

This is an auxiliary definition for the equivalence `Matrix.toLinearMapₛₗ₂'`. -/
def LinearMap.toMatrix₂Aux (b₁ : n → M₁) (b₂ : m → M₂) :
    (M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂) →ₗ[R] Matrix n m N₂ where
  toFun f := of fun i j => f (b₁ i) (b₂ j)
  map_add' _f _g := rfl
  map_smul' _f _g := rfl

@[simp]
theorem LinearMap.toMatrix₂Aux_apply (f : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂) (b₁ : n → M₁) (b₂ : m → M₂)
    (i : n) (j : m) : LinearMap.toMatrix₂Aux R b₁ b₂ f i j = f (b₁ i) (b₂ j) :=
  rfl

variable [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

theorem LinearMap.toLinearMap₂'Aux_toMatrix₂Aux (f : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂) :
    Matrix.toLinearMap₂'Aux σ₁ σ₂
        (LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1) (fun j => Pi.single j 1) f) =
      f := by
  refine ext_basis (Pi.basisFun R₁ n) (Pi.basisFun R₂ m) fun i j => ?_
  simp_rw [Pi.basisFun_apply, Matrix.toLinearMap₂'Aux_single, LinearMap.toMatrix₂Aux_apply]

theorem Matrix.toMatrix₂Aux_toLinearMap₂'Aux (f : Matrix n m N₂) :
    LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1)
        (fun j => Pi.single j 1) (f.toLinearMap₂'Aux σ₁ σ₂) =
      f := by
  ext i j
  simp_rw [LinearMap.toMatrix₂Aux_apply, Matrix.toLinearMap₂'Aux_single]

end CommSemiring

end AuxToMatrix

section ToMatrix'

/-! ### Bilinear maps over `n → R`

This section deals with the conversion between matrices and sesquilinear maps on `n → R`.
-/

variable [CommSemiring R] [AddCommMonoid N₂] [Module R N₂] [Semiring R₁] [Semiring R₂]
  [Semiring S₁] [Semiring S₂] [Module S₁ N₂] [Module S₂ N₂]
  [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂] [SMulCommClass S₂ S₁ N₂]
variable {σ₁ : R₁ →+* S₁} {σ₂ : R₂ →+* S₂}
variable [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

variable (R)

/-- The linear equivalence between sesquilinear maps and `n × m` matrices -/
def LinearMap.toMatrixₛₗ₂' : ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂) ≃ₗ[R] Matrix n m N₂ :=
  { LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1) (fun j => Pi.single j 1) with
    toFun := LinearMap.toMatrix₂Aux R _ _
    invFun := Matrix.toLinearMap₂'Aux σ₁ σ₂
    left_inv := LinearMap.toLinearMap₂'Aux_toMatrix₂Aux R
    right_inv := Matrix.toMatrix₂Aux_toLinearMap₂'Aux R }

/-- The linear equivalence between bilinear maps and `n × m` matrices -/
def LinearMap.toMatrix₂' : ((n → S₁) →ₗ[S₁] (m → S₂) →ₗ[S₂] N₂) ≃ₗ[R] Matrix n m N₂ :=
  LinearMap.toMatrixₛₗ₂' R

variable (σ₁ σ₂)

/-- The linear equivalence between `n × n` matrices and sesquilinear maps on `n → R` -/
def Matrix.toLinearMapₛₗ₂' : Matrix n m N₂ ≃ₗ[R] (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂ :=
  (LinearMap.toMatrixₛₗ₂' R).symm

/-- The linear equivalence between `n × n` matrices and bilinear maps on `n → R` -/
def Matrix.toLinearMap₂' : Matrix n m N₂ ≃ₗ[R] (n → S₁) →ₗ[S₁] (m → S₂) →ₗ[S₂] N₂ :=
  (LinearMap.toMatrix₂' R).symm

variable {R}

theorem Matrix.toLinearMapₛₗ₂'_aux_eq (M : Matrix n m N₂) :
    Matrix.toLinearMap₂'Aux σ₁ σ₂ M = Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M :=
  rfl

theorem Matrix.toLinearMapₛₗ₂'_apply (M : Matrix n m N₂) (x : n → R₁) (y : m → R₂) :
    -- porting note: we don't seem to have `∑ i j` as valid notation yet
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M x y = ∑ i, ∑ j, σ₁ (x i) •  σ₂ (y j) • M i j := by
  rw [toLinearMapₛₗ₂', toMatrixₛₗ₂', LinearEquiv.coe_symm_mk, toLinearMap₂'Aux, mk₂'ₛₗ_apply]
  apply Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [smul_comm]

theorem Matrix.toLinearMap₂'_apply (M : Matrix n m N₂) (x : n → S₁) (y : m → S₂) :
    -- porting note: we don't seem to have `∑ i j` as valid notation yet
    Matrix.toLinearMap₂' R M x y = ∑ i, ∑ j, x i • y j • M i j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [RingHom.id_apply, RingHom.id_apply, smul_comm]

theorem Matrix.toLinearMap₂'_apply' {T : Type*} [CommSemiring T] (M : Matrix n m T) (v : n → T)
    (w : m → T) : Matrix.toLinearMap₂' T M v w = v ⬝ᵥ (M *ᵥ w) := by
  simp_rw [Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_eq_mul, smul_eq_mul, mul_comm (w _), ← mul_assoc]

@[simp]
theorem Matrix.toLinearMapₛₗ₂'_single (M : Matrix n m N₂) (i : n) (j : m) :
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single σ₁ σ₂ M i j

@[simp]
theorem Matrix.toLinearMap₂'_single (M : Matrix n m N₂) (i : n) (j : m) :
    Matrix.toLinearMap₂' R M (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single _ _ M i j

@[simp]
theorem LinearMap.toMatrixₛₗ₂'_symm :
    ((LinearMap.toMatrixₛₗ₂' R).symm : Matrix n m N₂ ≃ₗ[R] _) = Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ :=
  rfl

@[simp]
theorem Matrix.toLinearMapₛₗ₂'_symm :
    ((Matrix.toLinearMapₛₗ₂' R σ₁ σ₂).symm : _ ≃ₗ[R] Matrix n m N₂) = LinearMap.toMatrixₛₗ₂' R :=
  (LinearMap.toMatrixₛₗ₂' R).symm_symm

@[simp]
theorem Matrix.toLinearMapₛₗ₂'_toMatrix' (B : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂) :
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ (LinearMap.toMatrixₛₗ₂' R B) = B :=
  (Matrix.toLinearMapₛₗ₂' R σ₁ σ₂).apply_symm_apply B

@[simp]
theorem Matrix.toLinearMap₂'_toMatrix' (B : (n → S₁) →ₗ[S₁] (m → S₂) →ₗ[S₂] N₂) :
    Matrix.toLinearMap₂' R (LinearMap.toMatrix₂' R B) = B :=
  (Matrix.toLinearMap₂' R).apply_symm_apply B

@[simp]
theorem LinearMap.toMatrix'_toLinearMapₛₗ₂' (M : Matrix n m N₂) :
    LinearMap.toMatrixₛₗ₂' R (Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M) = M :=
  (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]
theorem LinearMap.toMatrix'_toLinearMap₂' (M : Matrix n m N₂) :
    LinearMap.toMatrix₂' R (Matrix.toLinearMap₂' R (S₁ := S₁) (S₂ := S₂) M) = M :=
  (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]
theorem LinearMap.toMatrixₛₗ₂'_apply (B : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂) (i : n) (j : m) :
    LinearMap.toMatrixₛₗ₂' R B i j = B (Pi.single i 1) (Pi.single j 1) :=
  rfl

@[simp]
theorem LinearMap.toMatrix₂'_apply (B : (n → S₁) →ₗ[S₁] (m → S₂) →ₗ[S₂] N₂) (i : n) (j : m) :
    LinearMap.toMatrix₂' R B i j = B (Pi.single i 1) (Pi.single j 1) :=
  rfl

end ToMatrix'

section CommToMatrix'

-- TODO: Introduce matrix multiplication by matrices of scalars

variable {R : Type*} [CommSemiring R]
variable [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]
variable [Fintype n'] [Fintype m']
variable [DecidableEq n'] [DecidableEq m']

@[simp]
theorem LinearMap.toMatrix₂'_compl₁₂ (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (l : (n' → R) →ₗ[R] n → R)
    (r : (m' → R) →ₗ[R] m → R) :
    toMatrix₂' R (B.compl₁₂ l r) = (toMatrix' l)ᵀ * toMatrix₂' R B * toMatrix' r := by
  ext i j
  simp only [LinearMap.toMatrix₂'_apply, LinearMap.compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix', LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul (Pi.basisFun R n) (Pi.basisFun R m) (l _) (r _)]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, Pi.basisFun_repr, mul_assoc, mul_comm, mul_left_comm,
        Pi.basisFun_apply, of_apply]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp only [zero_smul, Finsupp.sum_zero]

theorem LinearMap.toMatrix₂'_comp (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (f : (n' → R) →ₗ[R] n → R) :
    toMatrix₂' R (B.comp f) = (toMatrix' f)ᵀ * toMatrix₂' R B := by
  rw [← LinearMap.compl₂_id (B.comp f), ← LinearMap.compl₁₂]
  simp

theorem LinearMap.toMatrix₂'_compl₂ (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (f : (m' → R) →ₗ[R] m → R) :
    toMatrix₂' R (B.compl₂ f) = toMatrix₂' R B * toMatrix' f := by
  rw [← LinearMap.comp_id B, ← LinearMap.compl₁₂]
  simp

theorem LinearMap.mul_toMatrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) :
    M * toMatrix₂' R B * N = toMatrix₂' R (B.compl₁₂ (toLin' Mᵀ) (toLin' N)) := by
  simp

theorem LinearMap.mul_toMatrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix n' n R) :
    M * toMatrix₂' R B = toMatrix₂' R (B.comp <| toLin' Mᵀ) := by
  simp only [B.toMatrix₂'_comp, transpose_transpose, toMatrix'_toLin']

theorem LinearMap.toMatrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix m m' R) :
    toMatrix₂' R B * M = toMatrix₂' R (B.compl₂ <| toLin' M) := by
  simp only [B.toMatrix₂'_compl₂, toMatrix'_toLin']

theorem Matrix.toLinearMap₂'_comp (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    LinearMap.compl₁₂ (Matrix.toLinearMap₂' R M) (toLin' P) (toLin' Q) =
      toLinearMap₂' R (Pᵀ * M * Q) :=
  (LinearMap.toMatrix₂' R).injective (by simp)

end CommToMatrix'

section ToMatrix

/-! ### Bilinear maps over arbitrary vector spaces

This section deals with the conversion between matrices and bilinear maps on
a module with a fixed basis.
-/


variable [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]

section

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

/-- `LinearMap.toMatrix₂ b₁ b₂` is the equivalence between `R`-bilinear maps on `M` and
`n`-by-`m` matrices with entries in `R`, if `b₁` and `b₂` are `R`-bases for `M₁` and `M₂`,
respectively. -/
noncomputable def LinearMap.toMatrix₂ : (M₁ →ₗ[R] M₂ →ₗ[R] N₂) ≃ₗ[R] Matrix n m N₂ :=
  (b₁.equivFun.arrowCongr (b₂.equivFun.arrowCongr (LinearEquiv.refl R N₂))).trans
    (LinearMap.toMatrix₂' R)

/-- `Matrix.toLinearMap₂ b₁ b₂` is the equivalence between `R`-bilinear maps on `M` and
`n`-by-`m` matrices with entries in `R`, if `b₁` and `b₂` are `R`-bases for `M₁` and `M₂`,
respectively; this is the reverse direction of `LinearMap.toMatrix₂ b₁ b₂`. -/
noncomputable def Matrix.toLinearMap₂ : Matrix n m N₂ ≃ₗ[R] M₁ →ₗ[R] M₂ →ₗ[R] N₂ :=
  (LinearMap.toMatrix₂ b₁ b₂).symm

-- We make this and not `LinearMap.toMatrix₂` a `simp` lemma to avoid timeouts
@[simp]
theorem LinearMap.toMatrix₂_apply (B : M₁ →ₗ[R] M₂ →ₗ[R] N₂) (i : n) (j : m) :
    LinearMap.toMatrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j) := by
  simp only [toMatrix₂, LinearEquiv.trans_apply, toMatrix₂'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, Pi.single_apply, ite_smul, one_smul, zero_smul, sum_ite_eq',
    mem_univ, ↓reduceIte, LinearEquiv.refl_apply]

@[simp]
theorem Matrix.toLinearMap₂_apply (M : Matrix n m N₂) (x : M₁) (y : M₂) :
    Matrix.toLinearMap₂ b₁ b₂ M x y = ∑ i, ∑ j, b₁.repr x i • b₂.repr y j • M i j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm ((RingHom.id R) ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

-- Not a `simp` lemma since `LinearMap.toMatrix₂` needs an extra argument
theorem LinearMap.toMatrix₂Aux_eq (B : M₁ →ₗ[R] M₂ →ₗ[R] N₂) :
    LinearMap.toMatrix₂Aux R b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B :=
  Matrix.ext fun i j => by rw [LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂Aux_apply]

@[simp]
theorem LinearMap.toMatrix₂_symm :
    (LinearMap.toMatrix₂ b₁ b₂).symm = Matrix.toLinearMap₂ (N₂ := N₂) b₁ b₂ :=
  rfl

@[simp]
theorem Matrix.toLinearMap₂_symm :
    (Matrix.toLinearMap₂ b₁ b₂).symm = LinearMap.toMatrix₂ (N₂ := N₂) b₁ b₂ :=
  (LinearMap.toMatrix₂ b₁ b₂).symm_symm

theorem Matrix.toLinearMap₂_basisFun :
    Matrix.toLinearMap₂ (Pi.basisFun R n) (Pi.basisFun R m) =
      Matrix.toLinearMap₂' R (N₂ := N₂) := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toLinearMap₂_apply, Pi.basisFun_repr,
    toLinearMap₂'_apply]

theorem LinearMap.toMatrix₂_basisFun :
    LinearMap.toMatrix₂ (Pi.basisFun R n) (Pi.basisFun R m) =
    LinearMap.toMatrix₂' R (N₂ := N₂) := by
  ext B
  rw [LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂'_apply, Pi.basisFun_apply, Pi.basisFun_apply]

@[simp]
theorem Matrix.toLinearMap₂_toMatrix₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] N₂) :
    Matrix.toLinearMap₂ b₁ b₂ (LinearMap.toMatrix₂ b₁ b₂ B) = B :=
  (Matrix.toLinearMap₂ b₁ b₂).apply_symm_apply B

@[simp]
theorem LinearMap.toMatrix₂_toLinearMap₂ (M : Matrix n m N₂) :
    LinearMap.toMatrix₂ b₁ b₂ (Matrix.toLinearMap₂ b₁ b₂ M) = M :=
  (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)
variable [AddCommMonoid M₁'] [Module R M₁']
variable [AddCommMonoid M₂'] [Module R M₂']
variable (b₁' : Basis n' R M₁')
variable (b₂' : Basis m' R M₂')
variable [Fintype n'] [Fintype m']
variable [DecidableEq n'] [DecidableEq m']

-- Cannot be a `simp` lemma because `b₁` and `b₂` must be inferred.
theorem LinearMap.toMatrix₂_compl₁₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (l : M₁' →ₗ[R] M₁)
    (r : M₂' →ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ l r) =
      (toMatrix b₁' b₁ l)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B * toMatrix b₂' b₂ r := by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix_apply, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp only [zero_smul, Finsupp.sum_zero]

theorem LinearMap.toMatrix₂_comp (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (f : M₁' →ₗ[R] M₁) :
    LinearMap.toMatrix₂ b₁' b₂ (B.comp f) =
      (toMatrix b₁' b₁ f)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B := by
  rw [← LinearMap.compl₂_id (B.comp f), ← LinearMap.compl₁₂, LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

theorem LinearMap.toMatrix₂_compl₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (f : M₂' →ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ f) =
      LinearMap.toMatrix₂ b₁ b₂ B * toMatrix b₂' b₂ f := by
  rw [← LinearMap.comp_id B, ← LinearMap.compl₁₂, LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

@[simp]
theorem LinearMap.toMatrix₂_mul_basis_toMatrix (c₁ : Basis n' R M₁) (c₂ : Basis m' R M₂)
    (B : M₁ →ₗ[R] M₂ →ₗ[R] R) :
    (b₁.toMatrix c₁)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B * b₂.toMatrix c₂ =
      LinearMap.toMatrix₂ c₁ c₂ B := by
  simp_rw [← LinearMap.toMatrix_id_eq_basis_toMatrix]
  rw [← LinearMap.toMatrix₂_compl₁₂, LinearMap.compl₁₂_id_id]

theorem LinearMap.mul_toMatrix₂_mul (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) :
    M * LinearMap.toMatrix₂ b₁ b₂ B * N =
      LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ (toLin b₁' b₁ Mᵀ) (toLin b₂' b₂ N)) := by
  simp_rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, toMatrix_toLin, transpose_transpose]

theorem LinearMap.mul_toMatrix₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : Matrix n' n R) :
    M * LinearMap.toMatrix₂ b₁ b₂ B =
      LinearMap.toMatrix₂ b₁' b₂ (B.comp (toLin b₁' b₁ Mᵀ)) := by
  rw [LinearMap.toMatrix₂_comp b₁, toMatrix_toLin, transpose_transpose]

theorem LinearMap.toMatrix₂_mul (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : Matrix m m' R) :
    LinearMap.toMatrix₂ b₁ b₂ B * M =
      LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ (toLin b₂' b₂ M)) := by
  rw [LinearMap.toMatrix₂_compl₂ b₁ b₂, toMatrix_toLin]

theorem Matrix.toLinearMap₂_compl₁₂ (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    (Matrix.toLinearMap₂ b₁ b₂ M).compl₁₂ (toLin b₁' b₁ P) (toLin b₂' b₂ Q) =
      Matrix.toLinearMap₂ b₁' b₂' (Pᵀ * M * Q) :=
  (LinearMap.toMatrix₂ b₁' b₂').injective
    (by
      simp only [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, LinearMap.toMatrix₂_toLinearMap₂,
        toMatrix_toLin])

end

end ToMatrix

/-! ### Adjoint pairs -/


section MatrixAdjoints

open Matrix

variable [CommRing R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable [Fintype n] [Fintype n']
variable (b₁ : Basis n R M₁) (b₂ : Basis n' R M₂)
variable (J J₂ : Matrix n n R) (J' : Matrix n' n' R)
variable (A : Matrix n' n R) (A' : Matrix n n' R)
variable (A₁ A₂ : Matrix n n R)

/-- The condition for the matrices `A`, `A'` to be an adjoint pair with respect to the square
matrices `J`, `J₃`. -/
def Matrix.IsAdjointPair :=
  Aᵀ * J' = J * A'

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def Matrix.IsSelfAdjoint :=
  Matrix.IsAdjointPair J J A₁ A₁

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def Matrix.IsSkewAdjoint :=
  Matrix.IsAdjointPair J J A₁ (-A₁)

variable [DecidableEq n] [DecidableEq n']

@[simp]
theorem isAdjointPair_toLinearMap₂' :
    LinearMap.IsAdjointPair (Matrix.toLinearMap₂' R J) (Matrix.toLinearMap₂' R J')
        (Matrix.toLin' A) (Matrix.toLin' A') ↔
      Matrix.IsAdjointPair J J' A A' := by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    ∀ B B' : (n → R) →ₗ[R] (n' → R) →ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂' R B = LinearMap.toMatrix₂' R B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂' R).injective h
  simp_rw [h, LinearMap.toMatrix₂'_comp, LinearMap.toMatrix₂'_compl₂,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLinearMap₂']
  rfl

@[simp]
theorem isAdjointPair_toLinearMap₂ :
    LinearMap.IsAdjointPair (Matrix.toLinearMap₂ b₁ b₁ J)
      (Matrix.toLinearMap₂ b₂ b₂ J') (Matrix.toLin b₁ b₂ A) (Matrix.toLin b₂ b₁ A') ↔
      Matrix.IsAdjointPair J J' A A' := by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    ∀ B B' : M₁ →ₗ[R] M₂ →ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂ b₁ b₂).injective h
  simp_rw [h, LinearMap.toMatrix₂_comp b₂ b₂, LinearMap.toMatrix₂_compl₂ b₁ b₁,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix₂_toLinearMap₂]
  rfl

theorem Matrix.isAdjointPair_equiv (P : Matrix n n R) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A₁ A₂ ↔
      J.IsAdjointPair J (P * A₁ * P⁻¹) (P * A₂ * P⁻¹) := by
  have h' : IsUnit P.det := P.isUnit_iff_isUnit_det.mp h
  let u := P.nonsingInvUnit h'
  let v := Pᵀ.nonsingInvUnit (P.isUnit_det_transpose h')
  let x := A₁ᵀ * Pᵀ * J
  let y := J * P * A₂
  suffices x * u = v * y ↔ v⁻¹ * x = y * u⁻¹ by
    dsimp only [Matrix.IsAdjointPair]
    simp only [Matrix.transpose_mul]
    simp only [← mul_assoc, P.transpose_nonsing_inv]
    convert this using 2
    · rw [mul_assoc, mul_assoc, ← mul_assoc J]
      rfl
    · rw [mul_assoc, mul_assoc, ← mul_assoc _ _ J]
      rfl
  rw [Units.eq_mul_inv_iff_mul_eq]
  conv_rhs => rw [mul_assoc]
  rw [v.inv_mul_eq_iff_eq_mul]

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pairSelfAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  (isPairSelfAdjointSubmodule (Matrix.toLinearMap₂' R J)
    (Matrix.toLinearMap₂' R J₂)).map
    ((LinearMap.toMatrix' : ((n → R) →ₗ[R] n → R) ≃ₗ[R] Matrix n n R) :
      ((n → R) →ₗ[R] n → R) →ₗ[R] Matrix n n R)

@[simp]
theorem mem_pairSelfAdjointMatricesSubmodule :
    A₁ ∈ pairSelfAdjointMatricesSubmodule J J₂ ↔ Matrix.IsAdjointPair J J₂ A₁ A₁ := by
  simp only [pairSelfAdjointMatricesSubmodule, Submodule.mem_map_equiv,
    mem_isPairSelfAdjointSubmodule, toMatrix'_symm, ← isAdjointPair_toLinearMap₂',
    IsPairSelfAdjoint, toLin'_apply']

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def selfAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  pairSelfAdjointMatricesSubmodule J J

@[simp]
theorem mem_selfAdjointMatricesSubmodule :
    A₁ ∈ selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A₁ := by
  rw [selfAdjointMatricesSubmodule, mem_pairSelfAdjointMatricesSubmodule, Matrix.IsSelfAdjoint]

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skewAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  pairSelfAdjointMatricesSubmodule (-J) J

@[simp]
theorem mem_skewAdjointMatricesSubmodule :
    A₁ ∈ skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A₁ := by
  rw [skewAdjointMatricesSubmodule, mem_pairSelfAdjointMatricesSubmodule]
  simp [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]

end MatrixAdjoints

namespace LinearMap

/-! ### Nondegenerate bilinear forms -/


section Det

open Matrix

variable [CommRing R₁] [AddCommMonoid M₁] [Module R₁ M₁]
variable [DecidableEq ι] [Fintype ι]

theorem _root_.Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂
    {M : Matrix ι ι R₁} (b : Basis ι R₁ M₁) :
    (Matrix.toLinearMap₂' R₁ M).SeparatingLeft (R := R₁) ↔
      (Matrix.toLinearMap₂ b b M).SeparatingLeft :=
  (separatingLeft_congr_iff b.equivFun.symm b.equivFun.symm).symm

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form
theorem _root_.Matrix.Nondegenerate.toLinearMap₂' {M : Matrix ι ι R₁} (h : M.Nondegenerate) :
    (Matrix.toLinearMap₂' R₁ M).SeparatingLeft (R := R₁) := fun x hx =>
  h.eq_zero_of_ortho fun y => by simpa only [toLinearMap₂'_apply'] using hx y

@[simp]
theorem _root_.Matrix.separatingLeft_toLinearMap₂'_iff {M : Matrix ι ι R₁} :
    (Matrix.toLinearMap₂' R₁ M).SeparatingLeft (R := R₁) ↔ M.Nondegenerate := by
  refine ⟨fun h ↦ Matrix.nondegenerate_def.mpr ?_, Matrix.Nondegenerate.toLinearMap₂'⟩
  exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans <| hv w

theorem _root_.Matrix.Nondegenerate.toLinearMap₂ {M : Matrix ι ι R₁} (h : M.Nondegenerate)
    (b : Basis ι R₁ M₁) : (toLinearMap₂ b b M).SeparatingLeft :=
  (Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂ b).mp h.toLinearMap₂'

@[simp]
theorem _root_.Matrix.separatingLeft_toLinearMap₂_iff {M : Matrix ι ι R₁} (b : Basis ι R₁ M₁) :
    (toLinearMap₂ b b M).SeparatingLeft ↔ M.Nondegenerate := by
  rw [← Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂,
    Matrix.separatingLeft_toLinearMap₂'_iff]

-- Lemmas transferring nondegeneracy between a bilinear form and its associated matrix
@[simp]
theorem nondegenerate_toMatrix₂'_iff {B : (ι → R₁) →ₗ[R₁] (ι → R₁) →ₗ[R₁] R₁} :
    (LinearMap.toMatrix₂' R₁ B).Nondegenerate ↔ B.SeparatingLeft :=
  Matrix.separatingLeft_toLinearMap₂'_iff.symm.trans <|
    (Matrix.toLinearMap₂'_toMatrix' (R := R₁) B).symm ▸ Iff.rfl

theorem SeparatingLeft.toMatrix₂' {B : (ι → R₁) →ₗ[R₁] (ι → R₁) →ₗ[R₁] R₁} (h : B.SeparatingLeft) :
    (LinearMap.toMatrix₂' R₁ B).Nondegenerate :=
  nondegenerate_toMatrix₂'_iff.mpr h

@[simp]
theorem nondegenerate_toMatrix_iff {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : Basis ι R₁ M₁) :
    (toMatrix₂ b b B).Nondegenerate ↔ B.SeparatingLeft :=
  (Matrix.separatingLeft_toLinearMap₂_iff b).symm.trans <|
    (Matrix.toLinearMap₂_toMatrix₂ b b B).symm ▸ Iff.rfl

theorem SeparatingLeft.toMatrix₂ {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (h : B.SeparatingLeft)
    (b : Basis ι R₁ M₁) : (toMatrix₂ b b B).Nondegenerate :=
  (nondegenerate_toMatrix_iff b).mpr h

-- Some shorthands for combining the above with `Matrix.nondegenerate_of_det_ne_zero`
variable [IsDomain R₁]

theorem separatingLeft_toLinearMap₂'_iff_det_ne_zero {M : Matrix ι ι R₁} :
    (Matrix.toLinearMap₂' R₁ M).SeparatingLeft (R := R₁) ↔ M.det ≠ 0 := by
  rw [Matrix.separatingLeft_toLinearMap₂'_iff, Matrix.nondegenerate_iff_det_ne_zero]

theorem separatingLeft_toLinearMap₂'_of_det_ne_zero' (M : Matrix ι ι R₁) (h : M.det ≠ 0) :
    (Matrix.toLinearMap₂' R₁ M).SeparatingLeft (R := R₁) :=
  separatingLeft_toLinearMap₂'_iff_det_ne_zero.mpr h

theorem separatingLeft_iff_det_ne_zero {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : Basis ι R₁ M₁) :
    B.SeparatingLeft ↔ (toMatrix₂ b b B).det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_toMatrix_iff]

theorem separatingLeft_of_det_ne_zero {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : Basis ι R₁ M₁)
    (h : (toMatrix₂ b b B).det ≠ 0) : B.SeparatingLeft :=
  (separatingLeft_iff_det_ne_zero b).mpr h

end Det

end LinearMap

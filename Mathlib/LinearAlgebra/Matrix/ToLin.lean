/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Module.Algebra
import Mathlib.Algebra.Algebra.Subalgebra.Tower

#align_import linear_algebra.matrix.to_lin from "leanprover-community/mathlib"@"0e2aab2b0d521f060f62a14d2cf2e2c54e8491d6"

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `LinearMap.toMatrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
   the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `Matrix κ ι R`
 * `Matrix.toLin`: the inverse of `LinearMap.toMatrix`
 * `LinearMap.toMatrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
   to `Matrix m n R` (with the standard basis on `m → R` and `n → R`)
 * `Matrix.toLin'`: the inverse of `LinearMap.toMatrix'`
 * `algEquivMatrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
   `R`-endomorphisms of `M` and `Matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `Matrix.mulVec` gives us a linear equivalence
`Matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `Matrix.vecMul` gives us a linear equivalence
`Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `Matrix.vecMul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
    Fintype (Matrix m n R) := by unfold Matrix; infer_instance
                                 -- ⊢ Fintype (m → n → R)
                                                -- 🎉 no goals

section ToMatrixRight

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

/-- `Matrix.vecMul M` is a linear map. -/
@[simps]
def Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R where
  toFun x := M.vecMul x
  map_add' _ _ := funext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := funext fun _ => smul_dotProduct _ _ _
#align matrix.vec_mul_linear Matrix.vecMulLinear

variable [Fintype m] [DecidableEq m]

@[simp]
theorem Matrix.vecMul_stdBasis (M : Matrix m n R) (i j) :
    M.vecMul (LinearMap.stdBasis R (fun _ => R) i 1) j = M i j := by
  have : (∑ i', (if i = i' then 1 else 0) * M i' j) = M i j := by
    simp_rw [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [vecMul, dotProduct]
  -- ⊢ ∑ x : m, ↑(LinearMap.stdBasis R (fun x => R) i) 1 x * M x j = M i j
  convert this
  -- ⊢ ↑(LinearMap.stdBasis R (fun x => R) i) 1 x✝ = if i = x✝ then 1 else 0
  split_ifs with h <;> simp only [stdBasis_apply]
  -- ⊢ ↑(LinearMap.stdBasis R (fun x => R) i) 1 x✝ = 1
                       -- ⊢ Function.update 0 i 1 x✝ = 1
                       -- ⊢ Function.update 0 i 1 x✝ = 0
  · rw [h, Function.update_same]
    -- 🎉 no goals
  · rw [Function.update_noteq (Ne.symm h), Pi.zero_apply]
    -- 🎉 no goals
#align matrix.vec_mul_std_basis Matrix.vecMul_stdBasis

/-- Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `Matrix m n R`,
by having matrices act by right multiplication.
 -/
def LinearMap.toMatrixRight' : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun f i j := f (stdBasis R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun f i j => ↑f (↑(stdBasis R (fun x = …
    simp only [Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
    -- 🎉 no goals
    -- ⊢ ∀ (i : m), ↑(vecMulLinear (AddHom.toFun { toAddHom := { toFun := fun f i j = …
  left_inv f := by
    -- ⊢ ↑(vecMulLinear (AddHom.toFun { toAddHom := { toFun := fun f i j => ↑f (↑(std …
             -- ⊢ ↑(vecMulLinear (AddHom.toFun { toAddHom := { toFun := fun f i j => ↑f (↑(std …
    -- ⊢ (fun f i j => ↑f (↑(stdBasis R (fun x => R) i) 1) j) (f + g) i j = ((fun f i …
    apply (Pi.basisFun R m).ext
    -- 🎉 no goals
    -- 🎉 no goals
    intro j; ext i
    -- ⊢ AddHom.toFun { toFun := fun f i j => ↑f (↑(stdBasis R (fun x => R) i) 1) j,  …
    simp only [Pi.basisFun_apply, Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
    -- 🎉 no goals
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, Matrix.smul_apply]
#align linear_map.to_matrix_right' LinearMap.toMatrixRight'

/-- A `Matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
abbrev Matrix.toLinearMapRight' : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] n → R :=
  LinearEquiv.symm LinearMap.toMatrixRight'
#align matrix.to_linear_map_right' Matrix.toLinearMapRight'

@[simp]
theorem Matrix.toLinearMapRight'_apply (M : Matrix m n R) (v : m → R) :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M v = M.vecMul v :=
  rfl
#align matrix.to_linear_map_right'_apply Matrix.toLinearMapRight'_apply

@[simp]
theorem Matrix.toLinearMapRight'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) (M * N) =
      ((Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) N).comp
        ((Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M) :=
  LinearMap.ext fun _x => (vecMul_vecMul _ M N).symm
#align matrix.to_linear_map_right'_mul Matrix.toLinearMapRight'_mul

theorem Matrix.toLinearMapRight'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) (M * N) x =
      (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) N
        ((Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M x) :=
  (vecMul_vecMul _ M N).symm
#align matrix.to_linear_map_right'_mul_apply Matrix.toLinearMapRight'_mul_apply

@[simp]
theorem Matrix.toLinearMapRight'_one :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) (1 : Matrix m m R) = LinearMap.id := by
  ext
  -- ⊢ ↑(comp (↑toLinearMapRight' 1) (single i✝)) 1 x✝ = ↑(comp LinearMap.id (singl …
  simp [LinearMap.one_apply, stdBasis_apply]
  -- 🎉 no goals
#align matrix.to_linear_map_right'_one Matrix.toLinearMapRight'_one

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vecMul` and `M'.vecMul`. -/
@[simps]
def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (n → R) ≃ₗ[R] m → R :=
  { -- porting note: needs type annotation for `⇑` to resolve
    (LinearMap.toMatrixRight' : _ ≃ₗ[Rᵐᵒᵖ] _).symm
      M' with
    -- porting note: needs type annotation for `⇑` to resolve
    toFun := (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M'
    -- porting note: needs type annotation for `⇑` to resolve
    invFun := (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M
    left_inv := fun x => by
      dsimp only -- porting note: needed due to non-flat structures
      -- ⊢ ↑(↑toLinearMapRight' M) (↑(↑toLinearMapRight' M') x) = x
      rw [← Matrix.toLinearMapRight'_mul_apply, hM'M, Matrix.toLinearMapRight'_one, id_apply]
      -- 🎉 no goals
    right_inv := fun x => by
      dsimp only -- porting note: needed due to non-flat structures
      -- ⊢ ↑(↑toLinearMapRight' M') (↑(↑toLinearMapRight' M) x) = x
      rw [← Matrix.toLinearMapRight'_mul_apply, hMM', Matrix.toLinearMapRight'_one, id_apply] }
      -- 🎉 no goals
#align matrix.to_linear_equiv_right'_of_inv Matrix.toLinearEquivRight'OfInv

end ToMatrixRight

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/


section ToMatrix'

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

/-- `Matrix.mulVec M` is a linear map. -/
def Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R where
  toFun := M.mulVec
  map_add' _ _ := funext fun _ => dotProduct_add _ _ _
  map_smul' _ _ := funext fun _ => dotProduct_smul _ _ _
#align matrix.mul_vec_lin Matrix.mulVecLin

@[simp]
theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n → R) :
    M.mulVecLin v = M.mulVec v :=
  rfl
#align matrix.mul_vec_lin_apply Matrix.mulVecLin_apply

@[simp]
theorem Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 :=
  LinearMap.ext zero_mulVec
#align matrix.mul_vec_lin_zero Matrix.mulVecLin_zero

@[simp]
theorem Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin :=
  LinearMap.ext fun _ => add_mulVec _ _ _
#align matrix.mul_vec_lin_add Matrix.mulVecLin_add

theorem Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm :=
  LinearMap.ext fun _ => submatrix_mulVec_equiv _ _ _ _
#align matrix.mul_vec_lin_submatrix Matrix.mulVecLin_submatrix

/-- A variant of `Matrix.mulVecLin_submatrix` that keeps around `LinearEquiv`s. -/
theorem Matrix.mulVecLin_reindex [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    (reindex e₁ e₂ M).mulVecLin =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ
        M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_submatrix _ _ _
#align matrix.mul_vec_lin_reindex Matrix.mulVecLin_reindex

variable [Fintype n]

@[simp]
theorem Matrix.mulVecLin_one [DecidableEq n] :
    Matrix.mulVecLin (1 : Matrix n n R) = LinearMap.id := by
  ext; simp [Matrix.one_apply, Pi.single_apply]
  -- ⊢ ↑(comp (mulVecLin 1) (single i✝)) 1 x✝ = ↑(comp LinearMap.id (single i✝)) 1 x✝
       -- 🎉 no goals
#align matrix.mul_vec_lin_one Matrix.mulVecLin_one

@[simp]
theorem Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) :=
  LinearMap.ext fun _ => (mulVec_mulVec _ _ _).symm
#align matrix.mul_vec_lin_mul Matrix.mulVecLin_mul

theorem Matrix.ker_mulVecLin_eq_bot_iff {M : Matrix n n R} :
    (LinearMap.ker M.mulVecLin) = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 := by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  -- 🎉 no goals
#align matrix.ker_mul_vec_lin_eq_bot_iff Matrix.ker_mulVecLin_eq_bot_iff

theorem Matrix.mulVec_stdBasis [DecidableEq n] (M : Matrix m n R) (i j) :
    M.mulVec (LinearMap.stdBasis R (fun _ => R) j 1) i = M i j :=
  (congr_fun (Matrix.mulVec_single _ _ (1 : R)) i).trans <| mul_one _
#align matrix.mul_vec_std_basis Matrix.mulVec_stdBasis

@[simp]
theorem Matrix.mulVec_stdBasis_apply [DecidableEq n] (M : Matrix m n R) (j) :
    M.mulVec (LinearMap.stdBasis R (fun _ => R) j 1) = Mᵀ j :=
  funext fun i => Matrix.mulVec_stdBasis M i j
#align matrix.mul_vec_std_basis_apply Matrix.mulVec_stdBasis_apply

theorem Matrix.range_mulVecLin (M : Matrix m n R) :
    LinearMap.range M.mulVecLin = span R (range Mᵀ) := by
  letI := Classical.decEq n
  -- ⊢ LinearMap.range (mulVecLin M) = span R (Set.range Mᵀ)
  simp_rw [range_eq_map, ← iSup_range_stdBasis, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.mulVecLin_apply, M.mulVec_stdBasis_apply, iSup_span, range_eq_iUnion]
#align matrix.range_mul_vec_lin Matrix.range_mulVecLin

variable [DecidableEq n]

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `Matrix m n R`. -/
def LinearMap.toMatrix' : ((n → R) →ₗ[R] m → R) ≃ₗ[R] Matrix m n R where
  toFun f := of fun i j => f (stdBasis R (fun _ => R) j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun f => ↑of fun i j => ↑f (↑(stdBasis …
    simp only [Matrix.mulVec_stdBasis, Matrix.mulVecLin_apply, of_apply]
    -- 🎉 no goals
    -- ⊢ ∀ (i : n), ↑(mulVecLin (AddHom.toFun { toAddHom := { toFun := fun f => ↑of f …
  left_inv f := by
    -- ⊢ ↑(mulVecLin (AddHom.toFun { toAddHom := { toFun := fun f => ↑of fun i j => ↑ …
             -- ⊢ ↑(mulVecLin (AddHom.toFun { toAddHom := { toFun := fun f => ↑of fun i j => ↑ …
    -- ⊢ (fun f => ↑of fun i j => ↑f (↑(stdBasis R (fun x => R) j) 1) i) (f + g) i j  …
    apply (Pi.basisFun R n).ext
    -- 🎉 no goals
    -- 🎉 no goals
    intro j; ext i
    -- ⊢ AddHom.toFun { toFun := fun f => ↑of fun i j => ↑f (↑(stdBasis R (fun x => R …
    simp only [Pi.basisFun_apply, Matrix.mulVec_stdBasis, Matrix.mulVecLin_apply, of_apply]
    -- 🎉 no goals
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, of_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, of_apply, Matrix.smul_apply]
#align linear_map.to_matrix' LinearMap.toMatrix'

/-- A `Matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`.

Note that the forward-direction does not require `DecidableEq` and is `Matrix.vecMulLin`. -/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm
#align matrix.to_lin' Matrix.toLin'

theorem Matrix.toLin'_apply' (M : Matrix m n R) : Matrix.toLin' M = M.mulVecLin :=
  rfl
#align matrix.to_lin'_apply' Matrix.toLin'_apply'

@[simp]
theorem LinearMap.toMatrix'_symm :
    (LinearMap.toMatrix'.symm : Matrix m n R ≃ₗ[R] _) = Matrix.toLin' :=
  rfl
#align linear_map.to_matrix'_symm LinearMap.toMatrix'_symm

@[simp]
theorem Matrix.toLin'_symm :
    (Matrix.toLin'.symm : ((n → R) →ₗ[R] m → R) ≃ₗ[R] _) = LinearMap.toMatrix' :=
  rfl
#align matrix.to_lin'_symm Matrix.toLin'_symm

@[simp]
theorem LinearMap.toMatrix'_toLin' (M : Matrix m n R) : LinearMap.toMatrix' (Matrix.toLin' M) = M :=
  LinearMap.toMatrix'.apply_symm_apply M
#align linear_map.to_matrix'_to_lin' LinearMap.toMatrix'_toLin'

@[simp]
theorem Matrix.toLin'_toMatrix' (f : (n → R) →ₗ[R] m → R) :
    Matrix.toLin' (LinearMap.toMatrix' f) = f :=
  Matrix.toLin'.apply_symm_apply f
#align matrix.to_lin'_to_matrix' Matrix.toLin'_toMatrix'

@[simp]
theorem LinearMap.toMatrix'_apply (f : (n → R) →ₗ[R] m → R) (i j) :
    LinearMap.toMatrix' f i j = f (fun j' => if j' = j then 1 else 0) i := by
  simp only [LinearMap.toMatrix', LinearEquiv.coe_mk, of_apply]
  -- ⊢ ↑f (↑(stdBasis R (fun x => R) j) 1) i = ↑f (fun j' => if j' = j then 1 else  …
  refine congr_fun ?_ _  -- porting note: `congr` didn't do this
  -- ⊢ ↑f (↑(stdBasis R (fun x => R) j) 1) = ↑f fun j' => if j' = j then 1 else 0
  congr
  -- ⊢ ↑(stdBasis R (fun x => R) j) 1 = fun j' => if j' = j then 1 else 0
  ext j'
  -- ⊢ ↑(stdBasis R (fun x => R) j) 1 j' = if j' = j then 1 else 0
  split_ifs with h
  -- ⊢ ↑(stdBasis R (fun x => R) j) 1 j' = 1
  · rw [h, stdBasis_same]
    -- 🎉 no goals
  apply stdBasis_ne _ _ _ _ h
  -- 🎉 no goals
#align linear_map.to_matrix'_apply LinearMap.toMatrix'_apply

@[simp]
theorem Matrix.toLin'_apply (M : Matrix m n R) (v : n → R) : Matrix.toLin' M v = M.mulVec v :=
  rfl
#align matrix.to_lin'_apply Matrix.toLin'_apply

@[simp]
theorem Matrix.toLin'_one : Matrix.toLin' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.mulVecLin_one
#align matrix.to_lin'_one Matrix.toLin'_one

@[simp]
theorem LinearMap.toMatrix'_id : LinearMap.toMatrix' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 := by
  ext
  -- ⊢ ↑toMatrix' id i✝ x✝ = OfNat.ofNat 1 i✝ x✝
  rw [Matrix.one_apply, LinearMap.toMatrix'_apply, id_apply]
  -- 🎉 no goals
#align linear_map.to_matrix'_id LinearMap.toMatrix'_id

@[simp]
theorem Matrix.toLin'_mul [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLin' (M * N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  Matrix.mulVecLin_mul _ _
#align matrix.to_lin'_mul Matrix.toLin'_mul

@[simp]
theorem Matrix.toLin'_submatrix [Fintype l] [DecidableEq l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    Matrix.toLin' (M.submatrix f₁ e₂) =
      funLeft R R f₁ ∘ₗ (Matrix.toLin' M) ∘ₗ funLeft _ _ e₂.symm :=
  Matrix.mulVecLin_submatrix _ _ _
#align matrix.to_lin'_submatrix Matrix.toLin'_submatrix

/-- A variant of `Matrix.toLin'_submatrix` that keeps around `LinearEquiv`s. -/
theorem Matrix.toLin'_reindex [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    Matrix.toLin' (reindex e₁ e₂ M) =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ (Matrix.toLin' M) ∘ₗ
        ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_reindex _ _ _
#align matrix.to_lin'_reindex Matrix.toLin'_reindex

/-- Shortcut lemma for `Matrix.toLin'_mul` and `LinearMap.comp_apply` -/
theorem Matrix.toLin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
    (x) : Matrix.toLin' (M * N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.toLin'_mul, LinearMap.comp_apply]
  -- 🎉 no goals
#align matrix.to_lin'_mul_apply Matrix.toLin'_mul_apply

theorem LinearMap.toMatrix'_comp [Fintype l] [DecidableEq l] (f : (n → R) →ₗ[R] m → R)
    (g : (l → R) →ₗ[R] n → R) :
    LinearMap.toMatrix' (f.comp g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g := by
  suffices f.comp g = Matrix.toLin' (LinearMap.toMatrix' f * LinearMap.toMatrix' g) by
    rw [this, LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  -- 🎉 no goals
#align linear_map.to_matrix'_comp LinearMap.toMatrix'_comp

theorem LinearMap.toMatrix'_mul [Fintype m] [DecidableEq m] (f g : (m → R) →ₗ[R] m → R) :
    LinearMap.toMatrix' (f * g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g :=
  LinearMap.toMatrix'_comp f g
#align linear_map.to_matrix'_mul LinearMap.toMatrix'_mul

@[simp]
theorem LinearMap.toMatrix'_algebraMap (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n → R)) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id]
  -- 🎉 no goals
#align linear_map.to_matrix'_algebra_map LinearMap.toMatrix'_algebraMap

theorem Matrix.ker_toLin'_eq_bot_iff {M : Matrix n n R} :
    LinearMap.ker (Matrix.toLin' M) = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 :=
  Matrix.ker_mulVecLin_eq_bot_iff
#align matrix.ker_to_lin'_eq_bot_iff Matrix.ker_toLin'_eq_bot_iff

theorem Matrix.range_toLin' (M : Matrix m n R) :
    LinearMap.range (Matrix.toLin' M) = span R (range Mᵀ) :=
  Matrix.range_mulVecLin _
#align matrix.range_to_lin' Matrix.range_toLin'

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mulVec` and `M'.mulVec`. -/
@[simps]
def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (m → R) ≃ₗ[R] n → R :=
  { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x => by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
                            -- 🎉 no goals
    right_inv := fun x => by
      simp only
      -- ⊢ ↑(↑toLin' M') (↑(↑toLin' M) x) = x
      rw [← Matrix.toLin'_mul_apply, hM'M, Matrix.toLin'_one, id_apply] }
      -- 🎉 no goals
#align matrix.to_lin'_of_inv Matrix.toLin'OfInv

/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `Matrix n n R`. -/
def LinearMap.toMatrixAlgEquiv' : ((n → R) →ₗ[R] n → R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_mul LinearMap.toMatrix'_algebraMap
#align linear_map.to_matrix_alg_equiv' LinearMap.toMatrixAlgEquiv'

/-- A `Matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R :=
  LinearMap.toMatrixAlgEquiv'.symm
#align matrix.to_lin_alg_equiv' Matrix.toLinAlgEquiv'

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_symm :
    (LinearMap.toMatrixAlgEquiv'.symm : Matrix n n R ≃ₐ[R] _) = Matrix.toLinAlgEquiv' :=
  rfl
#align linear_map.to_matrix_alg_equiv'_symm LinearMap.toMatrixAlgEquiv'_symm

@[simp]
theorem Matrix.toLinAlgEquiv'_symm :
    (Matrix.toLinAlgEquiv'.symm : ((n → R) →ₗ[R] n → R) ≃ₐ[R] _) = LinearMap.toMatrixAlgEquiv' :=
  rfl
#align matrix.to_lin_alg_equiv'_symm Matrix.toLinAlgEquiv'_symm

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) = M :=
  LinearMap.toMatrixAlgEquiv'.apply_symm_apply M
#align linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv' LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'

@[simp]
theorem Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (f : (n → R) →ₗ[R] n → R) :
    Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' f) = f :=
  Matrix.toLinAlgEquiv'.apply_symm_apply f
#align matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_apply (f : (n → R) →ₗ[R] n → R) (i j) :
    LinearMap.toMatrixAlgEquiv' f i j = f (fun j' => if j' = j then 1 else 0) i := by
  simp [LinearMap.toMatrixAlgEquiv']
  -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv'_apply LinearMap.toMatrixAlgEquiv'_apply

@[simp]
theorem Matrix.toLinAlgEquiv'_apply (M : Matrix n n R) (v : n → R) :
    Matrix.toLinAlgEquiv' M v = M.mulVec v :=
  rfl
#align matrix.to_lin_alg_equiv'_apply Matrix.toLinAlgEquiv'_apply

-- Porting note: the simpNF lemma rejects this, as `simp` already simplifies the lhs
-- to `(1 : (n → R) →ₗ[R] n → R)`.
-- @[simp]
theorem Matrix.toLinAlgEquiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.toLin'_one
#align matrix.to_lin_alg_equiv'_one Matrix.toLinAlgEquiv'_one

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_id :
    LinearMap.toMatrixAlgEquiv' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.toMatrix'_id
#align linear_map.to_matrix_alg_equiv'_id LinearMap.toMatrixAlgEquiv'_id

#align matrix.to_lin_alg_equiv'_mul map_mulₓ

theorem LinearMap.toMatrixAlgEquiv'_comp (f g : (n → R) →ₗ[R] n → R) :
    LinearMap.toMatrixAlgEquiv' (f.comp g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrix'_comp _ _
#align linear_map.to_matrix_alg_equiv'_comp LinearMap.toMatrixAlgEquiv'_comp

theorem LinearMap.toMatrixAlgEquiv'_mul (f g : (n → R) →ₗ[R] n → R) :
    LinearMap.toMatrixAlgEquiv' (f * g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrixAlgEquiv'_comp f g
#align linear_map.to_matrix_alg_equiv'_mul LinearMap.toMatrixAlgEquiv'_mul

end ToMatrix'

section ToMatrix

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [Fintype m] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def LinearMap.toMatrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'
#align linear_map.to_matrix LinearMap.toMatrix

/-- `LinearMap.toMatrix'` is a particular case of `LinearMap.toMatrix`, for the standard basis
`Pi.basisFun R n`. -/
theorem LinearMap.toMatrix_eq_toMatrix' :
    LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n) = LinearMap.toMatrix' :=
  rfl
#align linear_map.to_matrix_eq_to_matrix' LinearMap.toMatrix_eq_toMatrix'

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm
#align matrix.to_lin Matrix.toLin

/-- `Matrix.toLin'` is a particular case of `Matrix.toLin`, for the standard basis
`Pi.basisFun R n`. -/
theorem Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin' :=
  rfl
#align matrix.to_lin_eq_to_lin' Matrix.toLin_eq_toLin'

@[simp]
theorem LinearMap.toMatrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂ :=
  rfl
#align linear_map.to_matrix_symm LinearMap.toMatrix_symm

@[simp]
theorem Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂ :=
  rfl
#align matrix.to_lin_symm Matrix.toLin_symm

@[simp]
theorem Matrix.toLin_toMatrix (f : M₁ →ₗ[R] M₂) :
    Matrix.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f := by
  rw [← Matrix.toLin_symm, LinearEquiv.apply_symm_apply]
  -- 🎉 no goals
#align matrix.to_lin_to_matrix Matrix.toLin_toMatrix

@[simp]
theorem LinearMap.toMatrix_toLin (M : Matrix m n R) :
    LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M := by
  rw [← Matrix.toLin_symm, LinearEquiv.symm_apply_apply]
  -- 🎉 no goals
#align linear_map.to_matrix_to_lin LinearMap.toMatrix_toLin

theorem LinearMap.toMatrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i := by
  rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, Basis.equivFun_symm_apply, Finset.sum_eq_single j, if_pos rfl,
    one_smul, Basis.equivFun_apply]
  · intro j' _ hj'
    -- ⊢ (if j' = j then 1 else 0) • ↑v₁ j' = 0
    rw [if_neg hj', zero_smul]
    -- 🎉 no goals
  · intro hj
    -- ⊢ (if j = j then 1 else 0) • ↑v₁ j = 0
    have := Finset.mem_univ j
    -- ⊢ (if j = j then 1 else 0) • ↑v₁ j = 0
    contradiction
    -- 🎉 no goals
#align linear_map.to_matrix_apply LinearMap.toMatrix_apply

theorem LinearMap.toMatrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  funext fun i => f.toMatrix_apply _ _ i j
#align linear_map.to_matrix_transpose_apply LinearMap.toMatrix_transpose_apply

theorem LinearMap.toMatrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  LinearMap.toMatrix_apply v₁ v₂ f i j
#align linear_map.to_matrix_apply' LinearMap.toMatrix_apply'

theorem LinearMap.toMatrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  LinearMap.toMatrix_transpose_apply v₁ v₂ f j
#align linear_map.to_matrix_transpose_apply' LinearMap.toMatrix_transpose_apply'

theorem Matrix.toLin_apply (M : Matrix m n R) (v : M₁) :
    Matrix.toLin v₁ v₂ M v = ∑ j, M.mulVec (v₁.repr v) j • v₂ j :=
  show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply, v₂.equivFun_symm_apply]
    -- 🎉 no goals
#align matrix.to_lin_apply Matrix.toLin_apply

@[simp]
theorem Matrix.toLin_self (M : Matrix m n R) (i : n) :
    Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j := by
  rw [Matrix.toLin_apply, Finset.sum_congr rfl fun j _hj => ?_]
  -- ⊢ mulVec M (↑(↑v₁.repr (↑v₁ i))) j • ↑v₂ j = M j i • ↑v₂ j
  rw [Basis.repr_self, Matrix.mulVec, dotProduct, Finset.sum_eq_single i, Finsupp.single_eq_same,
    mul_one]
  · intro i' _ i'_ne
    -- ⊢ M j i' * ↑(Finsupp.single i 1) i' = 0
    rw [Finsupp.single_eq_of_ne i'_ne.symm, mul_zero]
    -- 🎉 no goals
  · intros
    -- ⊢ M j i * ↑(Finsupp.single i 1) i = 0
    have := Finset.mem_univ i
    -- ⊢ M j i * ↑(Finsupp.single i 1) i = 0
    contradiction
    -- 🎉 no goals
#align matrix.to_lin_self Matrix.toLin_self

/-- This will be a special case of `LinearMap.toMatrix_id_eq_basis_toMatrix`. -/
theorem LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ id = 1 := by
  ext i j
  -- ⊢ ↑(toMatrix v₁ v₁) id i j = OfNat.ofNat 1 i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  -- 🎉 no goals
#align linear_map.to_matrix_id LinearMap.toMatrix_id

theorem LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1 :=
  LinearMap.toMatrix_id v₁
#align linear_map.to_matrix_one LinearMap.toMatrix_one

@[simp]
theorem Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrix_id v₁, Matrix.toLin_toMatrix]
  -- 🎉 no goals
#align matrix.to_lin_one Matrix.toLin_one

theorem LinearMap.toMatrix_reindexRange [DecidableEq M₁] [DecidableEq M₂] (f : M₁ →ₗ[R] M₂) (k : m)
    (i : n) :
    LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, Set.mem_range_self k⟩
        ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrix v₁ v₂ f k i :=
  by simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]
     -- 🎉 no goals
#align linear_map.to_matrix_reindex_range LinearMap.toMatrix_reindexRange

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem LinearMap.toMatrix_comp [Fintype l] [DecidableEq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ v₃ (f.comp g) =
    LinearMap.toMatrix v₂ v₃ f * LinearMap.toMatrix v₁ v₂ g := by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_comp _ v₂.equivFun,
    LinearMap.toMatrix'_comp]
#align linear_map.to_matrix_comp LinearMap.toMatrix_comp

theorem LinearMap.toMatrix_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix v₁ v₁ g := by
  rw [LinearMap.mul_eq_comp, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]
  -- 🎉 no goals
#align linear_map.to_matrix_mul LinearMap.toMatrix_mul

@[simp]
theorem LinearMap.toMatrix_algebraMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id]
  -- 🎉 no goals
#align linear_map.to_matrix_algebra_map LinearMap.toMatrix_algebraMap

theorem LinearMap.toMatrix_mulVec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
    (LinearMap.toMatrix v₁ v₂ f).mulVec (v₁.repr x) = v₂.repr (f x) := by
  ext i
  -- ⊢ mulVec (↑(toMatrix v₁ v₂) f) (↑(↑v₁.repr x)) i = ↑(↑v₂.repr (↑f x)) i
  rw [← Matrix.toLin'_apply, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix',
    LinearEquiv.arrowCongr_apply, v₂.equivFun_apply]
  congr
  -- ⊢ ↑(LinearEquiv.symm (Basis.equivFun v₁)) ↑(↑v₁.repr x) = x
  exact v₁.equivFun.symm_apply_apply x
  -- 🎉 no goals
#align linear_map.to_matrix_mul_vec_repr LinearMap.toMatrix_mulVec_repr

@[simp]
theorem LinearMap.toMatrix_basis_equiv [Fintype l] [DecidableEq l] (b : Basis l R M₁)
    (b' : Basis l R M₂) :
    LinearMap.toMatrix b' b (b'.equiv b (Equiv.refl l) : M₂ →ₗ[R] M₁) = 1 := by
  ext i j
  -- ⊢ ↑(toMatrix b' b) (↑(Basis.equiv b' b (Equiv.refl l))) i j = OfNat.ofNat 1 i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  -- 🎉 no goals
#align linear_map.to_matrix_basis_equiv LinearMap.toMatrix_basis_equiv

theorem Matrix.toLin_mul [Fintype l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin v₁ v₂ B) := by
  apply (LinearMap.toMatrix v₁ v₃).injective
  -- ⊢ ↑(toMatrix v₁ v₃) (↑(toLin v₁ v₃) (A * B)) = ↑(toMatrix v₁ v₃) (comp (↑(toLi …
  haveI : DecidableEq l := fun _ _ => Classical.propDecidable _
  -- ⊢ ↑(toMatrix v₁ v₃) (↑(toLin v₁ v₃) (A * B)) = ↑(toMatrix v₁ v₃) (comp (↑(toLi …
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  -- ⊢ ↑(toMatrix v₁ v₃) (↑(toLin v₁ v₃) (A * B)) = ↑(toMatrix v₂ v₃) (↑(toLin v₂ v …
  repeat' rw [LinearMap.toMatrix_toLin]
  -- 🎉 no goals
#align matrix.to_lin_mul Matrix.toLin_mul

/-- Shortcut lemma for `Matrix.toLin_mul` and `LinearMap.comp_apply`. -/
theorem Matrix.toLin_mul_apply [Fintype l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
    (x) : Matrix.toLin v₁ v₃ (A * B) x = (Matrix.toLin v₂ v₃ A) (Matrix.toLin v₁ v₂ B x) := by
  rw [Matrix.toLin_mul v₁ v₂, LinearMap.comp_apply]
  -- 🎉 no goals
#align matrix.to_lin_mul_apply Matrix.toLin_mul_apply

/-- If `M` and `M` are each other's inverse matrices, `Matrix.toLin M` and `Matrix.toLin M'`
form a linear equivalence. -/
@[simps]
def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
    (hM'M : M' * M = 1) : M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x => by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
                            -- 🎉 no goals
    right_inv := fun x => by
      simp only
      -- ⊢ ↑(↑(toLin v₁ v₂) M) (↑(↑(toLin v₂ v₁) M') x) = x
      rw [← Matrix.toLin_mul_apply, hMM', Matrix.toLin_one, id_apply] }
      -- 🎉 no goals
#align matrix.to_lin_of_inv Matrix.toLinOfInv

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def LinearMap.toMatrixAlgEquiv : (M₁ →ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_mul v₁)
    (LinearMap.toMatrix_algebraMap v₁)
#align linear_map.to_matrix_alg_equiv LinearMap.toMatrixAlgEquiv

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ →ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm
#align matrix.to_lin_alg_equiv Matrix.toLinAlgEquiv

@[simp]
theorem LinearMap.toMatrixAlgEquiv_symm :
    (LinearMap.toMatrixAlgEquiv v₁).symm = Matrix.toLinAlgEquiv v₁ :=
  rfl
#align linear_map.to_matrix_alg_equiv_symm LinearMap.toMatrixAlgEquiv_symm

@[simp]
theorem Matrix.toLinAlgEquiv_symm :
    (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁ :=
  rfl
#align matrix.to_lin_alg_equiv_symm Matrix.toLinAlgEquiv_symm

@[simp]
theorem Matrix.toLinAlgEquiv_toMatrixAlgEquiv (f : M₁ →ₗ[R] M₁) :
    Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.apply_symm_apply]
  -- 🎉 no goals
#align matrix.to_lin_alg_equiv_to_matrix_alg_equiv Matrix.toLinAlgEquiv_toMatrixAlgEquiv

@[simp]
theorem LinearMap.toMatrixAlgEquiv_toLinAlgEquiv (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.symm_apply_apply]
  -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv_to_lin_alg_equiv LinearMap.toMatrixAlgEquiv_toLinAlgEquiv

theorem LinearMap.toMatrixAlgEquiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]
  -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv_apply LinearMap.toMatrixAlgEquiv_apply

theorem LinearMap.toMatrixAlgEquiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  funext fun i => f.toMatrix_apply _ _ i j
#align linear_map.to_matrix_alg_equiv_transpose_apply LinearMap.toMatrixAlgEquiv_transpose_apply

theorem LinearMap.toMatrixAlgEquiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
  LinearMap.toMatrixAlgEquiv_apply v₁ f i j
#align linear_map.to_matrix_alg_equiv_apply' LinearMap.toMatrixAlgEquiv_apply'

theorem LinearMap.toMatrixAlgEquiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j
#align linear_map.to_matrix_alg_equiv_transpose_apply' LinearMap.toMatrixAlgEquiv_transpose_apply'

theorem Matrix.toLinAlgEquiv_apply (M : Matrix n n R) (v : M₁) :
    Matrix.toLinAlgEquiv v₁ M v = ∑ j, M.mulVec (v₁.repr v) j • v₁ j :=
  show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply, v₁.equivFun_symm_apply]
    -- 🎉 no goals
#align matrix.to_lin_alg_equiv_apply Matrix.toLinAlgEquiv_apply

@[simp]
theorem Matrix.toLinAlgEquiv_self (M : Matrix n n R) (i : n) :
    Matrix.toLinAlgEquiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
  Matrix.toLin_self _ _ _ _
#align matrix.to_lin_alg_equiv_self Matrix.toLinAlgEquiv_self

theorem LinearMap.toMatrixAlgEquiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1 := by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]
  -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv_id LinearMap.toMatrixAlgEquiv_id

-- Porting note: the simpNF lemma rejects this, as `simp` already simplifies the lhs
-- to `(1 : M₁ →ₗ[R] M₁)`.
-- @[simp]
theorem Matrix.toLinAlgEquiv_one : Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  -- 🎉 no goals
#align matrix.to_lin_alg_equiv_one Matrix.toLinAlgEquiv_one

theorem LinearMap.toMatrixAlgEquiv_reindexRange [DecidableEq M₁] (f : M₁ →ₗ[R] M₁) (k i : n) :
    LinearMap.toMatrixAlgEquiv v₁.reindexRange f
        ⟨v₁ k, Set.mem_range_self k⟩ ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrixAlgEquiv v₁ f k i :=
  by simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]
     -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv_reindex_range LinearMap.toMatrixAlgEquiv_reindexRange

theorem LinearMap.toMatrixAlgEquiv_comp (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f.comp g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g :=
  by simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]
     -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv_comp LinearMap.toMatrixAlgEquiv_comp

theorem LinearMap.toMatrixAlgEquiv_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f * g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  rw [LinearMap.mul_eq_comp, LinearMap.toMatrixAlgEquiv_comp v₁ f g]
  -- 🎉 no goals
#align linear_map.to_matrix_alg_equiv_mul LinearMap.toMatrixAlgEquiv_mul

theorem Matrix.toLinAlgEquiv_mul (A B : Matrix n n R) :
    Matrix.toLinAlgEquiv v₁ (A * B) =
      (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B) :=
  by convert Matrix.toLin_mul v₁ v₁ v₁ A B
     -- 🎉 no goals
#align matrix.to_lin_alg_equiv_mul Matrix.toLinAlgEquiv_mul

@[simp]
theorem Matrix.toLin_finTwoProd_apply (a b c d : R) (x : R × R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] x =
      (a * x.fst + b * x.snd, c * x.fst + d * x.snd) :=
  -- porting note: added `(Prod.smul_mk)` which is already a simp lemma
  by simp [Matrix.toLin_apply, Matrix.mulVec, Matrix.dotProduct, (Prod.smul_mk)]
     -- 🎉 no goals
#align matrix.to_lin_fin_two_prod_apply Matrix.toLin_finTwoProd_apply

theorem Matrix.toLin_finTwoProd (a b c d : R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] =
      (a • LinearMap.fst R R R + b • LinearMap.snd R R R).prod
        (c • LinearMap.fst R R R + d • LinearMap.snd R R R) :=
  LinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _
#align matrix.to_lin_fin_two_prod Matrix.toLin_finTwoProd

@[simp]
theorem toMatrix_distrib_mul_action_toLinearMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (DistribMulAction.toLinearMap R M₁ x) =
    Matrix.diagonal fun _ => x := by
  ext
  -- ⊢ ↑(toMatrix v₁ v₁) (DistribMulAction.toLinearMap R M₁ x) i✝ x✝ = Matrix.diago …
  rw [LinearMap.toMatrix_apply, DistribMulAction.toLinearMap_apply, LinearEquiv.map_smul,
    Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_pi_single, Matrix.diagonal_apply,
    Pi.single_apply]
#align to_matrix_distrib_mul_action_to_linear_map toMatrix_distrib_mul_action_toLinearMap

end ToMatrix

namespace Algebra

section Lmul

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem toMatrix_lmul' (x : S) (i j) :
    LinearMap.toMatrix b b (lmul R S x) i j = b.repr (x * b j) i := by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']
  -- 🎉 no goals
#align algebra.to_matrix_lmul' Algebra.toMatrix_lmul'

@[simp]
theorem toMatrix_lsmul (x : R) :
    LinearMap.toMatrix b b (Algebra.lsmul R R S x) = Matrix.diagonal fun _ => x :=
  toMatrix_distrib_mul_action_toLinearMap b x
#align algebra.to_matrix_lsmul Algebra.toMatrix_lsmul

/-- `leftMulMatrix b x` is the matrix corresponding to the linear map `fun y ↦ x * y`.

`leftMulMatrix_eq_repr_mul` gives a formula for the entries of `leftMulMatrix`.

This definition is useful for doing (more) explicit computations with `LinearMap.mulLeft`,
such as the trace form or norm map for algebras.
-/
noncomputable def leftMulMatrix : S →ₐ[R] Matrix m m R where
  toFun x := LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    dsimp only  -- porting node: needed due to new-style structures
    -- ⊢ ↑(toMatrix b b) (↑(lmul R S) 0) = 0
    rw [AlgHom.map_zero, LinearEquiv.map_zero]
    -- 🎉 no goals
    -- ⊢ ↑(toMatrix b b) (↑(lmul R S) 1) = 1
  map_one' := by
    -- 🎉 no goals
    dsimp only  -- porting node: needed due to new-style structures
    rw [AlgHom.map_one, LinearMap.toMatrix_one]
  map_add' x y := by
    dsimp only  -- porting node: needed due to new-style structures
    -- ⊢ ↑(toMatrix b b) (↑(lmul R S) (x + y)) = ↑(toMatrix b b) (↑(lmul R S) x) + ↑( …
    -- ⊢ ↑(toMatrix b b) (↑(lmul R S) (x * y)) = ↑(toMatrix b b) (↑(lmul R S) x) * ↑( …
    rw [AlgHom.map_add, LinearEquiv.map_add]
    -- 🎉 no goals
    -- 🎉 no goals
  map_mul' x y := by
    dsimp only  -- porting node: needed due to new-style structures
    rw [AlgHom.map_mul, LinearMap.toMatrix_mul]
  commutes' r := by
    dsimp only  -- porting node: needed due to new-style structures
    -- ⊢ ↑(toMatrix b b) (↑(lmul R S) (↑(algebraMap R S) r)) = ↑(algebraMap R (Matrix …
    ext
    -- ⊢ ↑(toMatrix b b) (↑(lmul R S) (↑(algebraMap R S) r)) i✝ x✝ = ↑(algebraMap R ( …
    rw [lmul_algebraMap, toMatrix_lsmul, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self]
#align algebra.left_mul_matrix Algebra.leftMulMatrix

theorem leftMulMatrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) :=
  rfl
#align algebra.left_mul_matrix_apply Algebra.leftMulMatrix_apply

theorem leftMulMatrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (x * b j) i := by
  -- This is defeq to just `toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [leftMulMatrix_apply, toMatrix_lmul' b x i j]
  -- 🎉 no goals
#align algebra.left_mul_matrix_eq_repr_mul Algebra.leftMulMatrix_eq_repr_mul

theorem leftMulMatrix_mulVec_repr (x y : S) :
    (leftMulMatrix b x).mulVec (b.repr y) = b.repr (x * y) :=
  (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y
#align algebra.left_mul_matrix_mul_vec_repr Algebra.leftMulMatrix_mulVec_repr

@[simp]
theorem toMatrix_lmul_eq (x : S) :
    LinearMap.toMatrix b b (LinearMap.mulLeft R x) = leftMulMatrix b x :=
  rfl
#align algebra.to_matrix_lmul_eq Algebra.toMatrix_lmul_eq

theorem leftMulMatrix_injective : Function.Injective (leftMulMatrix b) := fun x x' h =>
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
                                    -- 🎉 no goals
    _ = x' := mul_one x'
#align algebra.left_mul_matrix_injective Algebra.leftMulMatrix_injective

end Lmul

section LmulTower

variable {R S T : Type*} [CommRing R] [CommRing S] [Ring T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable (b : Basis m R S) (c : Basis n S T)

theorem smul_leftMulMatrix (x) (ik jk) :
    leftMulMatrix (b.smul c) x ik jk = leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smul_apply,
    Basis.smul_repr, Finsupp.smul_apply, id.smul_eq_mul, LinearEquiv.map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']
#align algebra.smul_left_mul_matrix Algebra.smul_leftMulMatrix

theorem smul_leftMulMatrix_algebraMap (x : S) :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) = blockDiagonal fun _ => leftMulMatrix b x := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  -- ⊢ ↑(leftMulMatrix (Basis.smul b c)) (↑(algebraMap S T) x) (i, k) (j, k') = blo …
  rw [smul_leftMulMatrix, AlgHom.commutes, blockDiagonal_apply, algebraMap_matrix_apply]
  -- ⊢ ↑(leftMulMatrix b) (if (i, k).snd = (j, k').snd then ↑(algebraMap S S) x els …
  split_ifs with h <;> simp only at h <;> simp [h]
  -- ⊢ ↑(leftMulMatrix b) (if (i, k).snd = (j, k').snd then ↑(algebraMap S S) x els …
                       -- ⊢ ↑(leftMulMatrix b) (if (i, k).snd = (j, k').snd then ↑(algebraMap S S) x els …
                       -- ⊢ ↑(leftMulMatrix b) (if (i, k).snd = (j, k').snd then ↑(algebraMap S S) x els …
                                          -- 🎉 no goals
                                          -- 🎉 no goals
#align algebra.smul_left_mul_matrix_algebra_map Algebra.smul_leftMulMatrix_algebraMap

theorem smul_leftMulMatrix_algebraMap_eq (x : S) (i j k) :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j := by
  rw [smul_leftMulMatrix_algebraMap, blockDiagonal_apply_eq]
  -- 🎉 no goals
#align algebra.smul_left_mul_matrix_algebra_map_eq Algebra.smul_leftMulMatrix_algebraMap_eq

theorem smul_leftMulMatrix_algebraMap_ne (x : S) (i j) {k k'} (h : k ≠ k') :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) (i, k) (j, k') = 0 := by
  rw [smul_leftMulMatrix_algebraMap, blockDiagonal_apply_ne _ _ _ h]
  -- 🎉 no goals
#align algebra.smul_left_mul_matrix_algebra_map_ne Algebra.smul_leftMulMatrix_algebraMap_ne

end LmulTower

end Algebra

section

variable {R : Type v} [CommRing R] {n : Type*} [DecidableEq n]

variable {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M]

variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def algEquivMatrix' [Fintype n] : Module.End R (n → R) ≃ₐ[R] Matrix n n R :=
  { LinearMap.toMatrix' with
    map_mul' := LinearMap.toMatrix'_comp
    map_add' := LinearMap.toMatrix'.map_add
    -- porting note: golfed away messy failing proof
    commutes' := LinearMap.toMatrix'_algebraMap }
#align alg_equiv_matrix' algEquivMatrix'

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def LinearEquiv.algConj (e : M₁ ≃ₗ[R] M₂) : Module.End R M₁ ≃ₐ[R] Module.End R M₂ :=
  { e.conj with
    map_mul' := fun f g => by apply e.arrowCongr_comp
                              -- 🎉 no goals
    map_add' := e.conj.map_add
    commutes' := fun r => by
      change e.conj (r • LinearMap.id) = r • LinearMap.id
      -- ⊢ ↑(conj e) (r • LinearMap.id) = r • LinearMap.id
      rw [LinearEquiv.map_smul, LinearEquiv.conj_id] }
      -- 🎉 no goals
#align linear_equiv.alg_conj LinearEquiv.algConj

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  h.equivFun.algConj.trans algEquivMatrix'
#align alg_equiv_matrix algEquivMatrix

end

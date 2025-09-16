/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Ideal.Span

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

open LinearMap Matrix Module Set Submodule

/-!
### Bilinear versions of matrix products

The definitions in this section are stated with two extra rings, to allow for non-commutative rings.
-/

section Bilinear
variable {l m n R S A : Type*}
variable [Semiring R] [Semiring S] [NonUnitalNonAssocSemiring A]
variable [Module R A] [Module S A]
variable [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

variable (R S)

/-- `Matrix.vecMul` as a bilinear map.

When `A` is non-commutative, this can be instantiated as `vecMulBilin A Aᵐᵒᵖ` -/
def Matrix.vecMulBilin [Fintype m] : (m → A) →ₗ[R] Matrix m n A →ₗ[S] (n → A) where
  toFun x :=
  { toFun M := x ᵥ* M
    map_add' _ _ := vecMul_add _ _ _
    map_smul' _ _ := vecMul_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMul _ _ _

@[simp]
theorem Matrix.vecMulBilin_apply [Fintype m] (v : m → A) (M : Matrix m n A) :
    Matrix.vecMulBilin R S v M = v ᵥ* M := rfl

example {A} [Semiring A] [Fintype m] := (vecMulBilin A Aᵐᵒᵖ : _ →ₗ[_] Matrix m n A →ₗ[_] _)

/-- `Matrix.mulVec` as a bilinear map.

When `A` is non-commutative, this can be instantiated as `mulVecBilin A Aᵐᵒᵖ` -/
def Matrix.mulVecBilin [Fintype n] : Matrix m n A →ₗ[R] (n → A) →ₗ[S] (m → A) where
  toFun M :=
  { toFun x := M *ᵥ x
    map_add' _ _ := mulVec_add _ _ _
    map_smul' _ _ := mulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_mulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_mulVec _ _ _

@[simp]
theorem Matrix.mulVecBilin_apply [Fintype n] (M : Matrix m n A) (v : n → A) :
    Matrix.mulVecBilin R S M v = M *ᵥ v := rfl

example {A} [Semiring A] [Fintype n] := (mulVecBilin A Aᵐᵒᵖ : Matrix m n A →ₗ[_] _ →ₗ[_] _)

/-- `vecMulVec` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `vecMulVecLinear A Aᵐᵒᵖ`. -/
@[simps]
def vecMulVecBilin : (m → A) →ₗ[R] (n → A) →ₗ[S] Matrix m n A where
  toFun x :=
    { toFun y := vecMulVec x y
      map_add' _ _ := vecMulVec_add _ _ _
      map_smul' _ _ := vecMulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMulVec _ _ _

example {A} [Semiring A] := (vecMulVecBilin A Aᵐᵒᵖ : (m → A) →ₗ[_] (n → A) →ₗ[_] _)

/-- `vecMulVec` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `vecMulVecLinear A Aᵐᵒᵖ`. -/
@[simps]
def dotProductBilin [Fintype m] : (m → A) →ₗ[R] (m → A) →ₗ[S] A where
  toFun x :=
    { toFun y := dotProduct x y
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' _ _ := dotProduct_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_dotProduct _ _ _

example {A} [Semiring A] [Fintype m] := (dotProductBilin A Aᵐᵒᵖ : (m → A) →ₗ[_] _ →ₗ[_] _)

end Bilinear

section ToMatrixRight
variable {R : Type*} [Semiring R]
variable {l m n : Type*}

/-- `Matrix.vecMul M` is a linear map.

Note this is a special case of `Matrix.vecMulBilin`. -/
abbrev Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R :=
  Matrix.vecMulBilin R Rᵐᵒᵖ |>.flip M

@[simp] theorem Matrix.vecMulLinear_apply [Fintype m] (M : Matrix m n R) (x : m → R) :
    M.vecMulLinear x = x ᵥ* M := rfl

theorem Matrix.coe_vecMulLinear [Fintype m] (M : Matrix m n R) :
    (M.vecMulLinear : _ → _) = M.vecMul := rfl

variable [Fintype m]

theorem range_vecMulLinear (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M.row) := by
  letI := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_single, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    LinearMap.single, LinearMap.coe_mk, AddHom.coe_mk, row_def]
  unfold vecMul
  simp_rw [single_dotProduct, one_mul]

theorem Matrix.vecMul_injective_iff {M : Matrix m n R} :
    Function.Injective M.vecMul ↔ LinearIndependent R M.row := by
  rw [← coe_vecMulLinear, linearIndependent_iff_injective_fintypeLinearCombination]
  congr! 1
  exact funext fun _ => Matrix.vecMul_eq_sum _ _

lemma Matrix.linearIndependent_rows_of_isUnit {A : Matrix m m R}
    [DecidableEq m] (ha : IsUnit A) : LinearIndependent R A.row := by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

section
variable [DecidableEq m]

/-- Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `Matrix m n R`,
by having matrices act by right multiplication.
-/
def LinearMap.toMatrixRight' : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun f i j := f (single R (fun _ ↦ R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, Matrix.smul_apply]

/-- A `Matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
abbrev Matrix.toLinearMapRight' [DecidableEq m] : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] n → R :=
  LinearEquiv.symm LinearMap.toMatrixRight'

@[simp]
theorem Matrix.toLinearMapRight'_apply (M : Matrix m n R) (v : m → R) :
    (Matrix.toLinearMapRight') M v = v ᵥ* M := rfl

@[simp]
theorem Matrix.toLinearMapRight'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    Matrix.toLinearMapRight' (M * N) =
      (Matrix.toLinearMapRight' N).comp (Matrix.toLinearMapRight' M) :=
  LinearMap.ext fun _x ↦ (vecMul_vecMul _ M N).symm

theorem Matrix.toLinearMapRight'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    Matrix.toLinearMapRight' (M * N) x =
      Matrix.toLinearMapRight' N (Matrix.toLinearMapRight' M x) :=
  (vecMul_vecMul _ M N).symm

@[simp]
theorem Matrix.toLinearMapRight'_one :
    Matrix.toLinearMapRight' (1 : Matrix m m R) = LinearMap.id := by
  ext
  simp

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vecMul` and `M'.vecMul`. -/
@[simps]
def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (n → R) ≃ₗ[R] m → R :=
  { LinearMap.toMatrixRight'.symm M' with
    toFun := Matrix.toLinearMapRight' M'
    invFun := Matrix.toLinearMapRight' M
    left_inv := fun x ↦ by
      rw [← Matrix.toLinearMapRight'_mul_apply, hM'M, Matrix.toLinearMapRight'_one, id_apply]
    right_inv := fun x ↦ by
      rw [← Matrix.toLinearMapRight'_mul_apply, hMM', Matrix.toLinearMapRight'_one, id_apply] }

end
end ToMatrixRight

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/


section mulVec

variable {R : Type*} [CommSemiring R]
variable {k l m n : Type*}

/-- `Matrix.mulVec M` as a linear map.

Note this is a special case of `Matrix.mulVecBilin`. -/
abbrev Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R := mulVecBilin R R M

theorem Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R) :
    (M.mulVecLin : _ → _) = M.mulVec := rfl

@[simp]
theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n → R) :
    M.mulVecLin v = M *ᵥ v :=
  rfl

@[simp]
theorem Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 :=
  LinearMap.ext zero_mulVec

@[simp]
theorem Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin :=
  LinearMap.ext fun _ ↦ add_mulVec _ _ _

@[simp] theorem Matrix.mulVecLin_transpose [Fintype m] (M : Matrix m n R) :
    Mᵀ.mulVecLin = M.vecMulLinear := by
  ext; simp [mulVec_transpose]

@[simp] theorem Matrix.vecMulLinear_transpose [Fintype n] (M : Matrix m n R) :
    Mᵀ.vecMulLinear = M.mulVecLin := by
  ext; simp [vecMul_transpose]

theorem Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm :=
  LinearMap.ext fun _ ↦ submatrix_mulVec_equiv _ _ _ _

/-- A variant of `Matrix.mulVecLin_submatrix` that keeps around `LinearEquiv`s. -/
theorem Matrix.mulVecLin_reindex [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    (reindex e₁ e₂ M).mulVecLin =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ
        M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_submatrix _ _ _

variable [Fintype n]

@[simp]
theorem Matrix.mulVecLin_one [DecidableEq n] :
    Matrix.mulVecLin (1 : Matrix n n R) = LinearMap.id := by
  ext; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]
theorem Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) :=
  LinearMap.ext fun _ ↦ (mulVec_mulVec _ _ _).symm

theorem Matrix.ker_mulVecLin_eq_bot_iff {M : Matrix m n R} :
    (LinearMap.ker M.mulVecLin) = ⊥ ↔ ∀ v, M *ᵥ v = 0 → v = 0 := by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]

theorem Matrix.range_mulVecLin (M : Matrix m n R) :
    LinearMap.range M.mulVecLin = span R (range M.col) := by
  rw [← vecMulLinear_transpose, range_vecMulLinear, row_transpose]

theorem Matrix.mulVec_injective_iff {M : Matrix m n R} :
    Function.Injective M.mulVec ↔ LinearIndependent R M.col := by
  change Function.Injective (fun x ↦ _) ↔ _
  simp_rw [← M.vecMul_transpose, vecMul_injective_iff, row_transpose]

lemma Matrix.linearIndependent_cols_of_isUnit [Fintype m]
    {A : Matrix m m R} [DecidableEq m] (ha : IsUnit A) :
    LinearIndependent R A.col := by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

end mulVec

section ToMatrix'

variable {R : Type*} [CommSemiring R]
variable {k l m n : Type*} [DecidableEq n] [Fintype n]

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `Matrix m n R`. -/
def LinearMap.toMatrix' : ((n → R) →ₗ[R] m → R) ≃ₗ[R] Matrix m n R where
  toFun f := of fun i j ↦ f (Pi.single j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    simp only [Matrix.mulVec_single_one, col_apply, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_single_one, col_apply,
      Matrix.mulVecLin_apply, of_apply]
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, of_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, of_apply, Matrix.smul_apply]

/-- A `Matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`.

Note that the forward-direction does not require `DecidableEq` and is `Matrix.mulVecLin`. -/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm

theorem Matrix.toLin'_apply' (M : Matrix m n R) : Matrix.toLin' M = M.mulVecLin :=
  rfl

@[simp]
theorem LinearMap.toMatrix'_symm :
    (LinearMap.toMatrix'.symm : Matrix m n R ≃ₗ[R] _) = Matrix.toLin' :=
  rfl

@[simp]
theorem Matrix.toLin'_symm :
    (Matrix.toLin'.symm : ((n → R) →ₗ[R] m → R) ≃ₗ[R] _) = LinearMap.toMatrix' :=
  rfl

@[simp]
theorem LinearMap.toMatrix'_toLin' (M : Matrix m n R) : LinearMap.toMatrix' (Matrix.toLin' M) = M :=
  LinearMap.toMatrix'.apply_symm_apply M

@[simp]
theorem Matrix.toLin'_toMatrix' (f : (n → R) →ₗ[R] m → R) :
    Matrix.toLin' (LinearMap.toMatrix' f) = f :=
  Matrix.toLin'.apply_symm_apply f

@[simp]
theorem LinearMap.toMatrix'_apply (f : (n → R) →ₗ[R] m → R) (i j) :
    LinearMap.toMatrix' f i j = f (fun j' ↦ if j' = j then 1 else 0) i := by
  simp [toMatrix', ← Pi.single_apply]

@[simp]
theorem Matrix.toLin'_apply (M : Matrix m n R) (v : n → R) : Matrix.toLin' M v = M *ᵥ v :=
  rfl

@[simp]
theorem LinearMap.toMatrix'_mulVec (f : (n → R) →ₗ[R] m → R) (v : n → R) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← toLin'_apply, toLin'_toMatrix']

@[simp]
theorem Matrix.toLin'_one : Matrix.toLin' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.mulVecLin_one

@[simp]
theorem LinearMap.toMatrix'_id : LinearMap.toMatrix' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 := by
  ext
  rw [Matrix.one_apply, LinearMap.toMatrix'_apply, id_apply]

@[simp]
theorem LinearMap.toMatrix'_one : LinearMap.toMatrix' (1 : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.toMatrix'_id

@[simp]
theorem Matrix.toLin'_mul [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLin' (M * N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  Matrix.mulVecLin_mul _ _

@[simp]
theorem Matrix.toLin'_pow (M : Matrix n n R) (k : ℕ) :
    (M ^ k).toLin' = M.toLin' ^ k := by
  induction k with
  | zero => simp [End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin'_mul, ih, Module.End.mul_eq_comp]

@[simp]
theorem Matrix.toLin'_submatrix [Fintype l] [DecidableEq l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    Matrix.toLin' (M.submatrix f₁ e₂) =
      funLeft R R f₁ ∘ₗ (Matrix.toLin' M) ∘ₗ funLeft _ _ e₂.symm :=
  Matrix.mulVecLin_submatrix _ _ _

/-- A variant of `Matrix.toLin'_submatrix` that keeps around `LinearEquiv`s. -/
theorem Matrix.toLin'_reindex [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    Matrix.toLin' (reindex e₁ e₂ M) =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ (Matrix.toLin' M) ∘ₗ
        ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_reindex _ _ _

/-- Shortcut lemma for `Matrix.toLin'_mul` and `LinearMap.comp_apply` -/
theorem Matrix.toLin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
    (x) : Matrix.toLin' (M * N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.toLin'_mul, LinearMap.comp_apply]

theorem LinearMap.toMatrix'_comp [Fintype l] [DecidableEq l] (f : (n → R) →ₗ[R] m → R)
    (g : (l → R) →ₗ[R] n → R) :
    LinearMap.toMatrix' (f.comp g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g := by
  suffices f.comp g = Matrix.toLin' (LinearMap.toMatrix' f * LinearMap.toMatrix' g) by
    rw [this, LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']

theorem LinearMap.toMatrix'_mul [Fintype m] [DecidableEq m] (f g : (m → R) →ₗ[R] m → R) :
    LinearMap.toMatrix' (f * g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g :=
  LinearMap.toMatrix'_comp f g

@[simp]
theorem LinearMap.toMatrix'_algebraMap (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n → R)) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, smul_eq_diagonal_mul]

theorem Matrix.ker_toLin'_eq_bot_iff {M : Matrix n n R} :
    LinearMap.ker (Matrix.toLin' M) = ⊥ ↔ ∀ v, M *ᵥ v = 0 → v = 0 :=
  Matrix.ker_mulVecLin_eq_bot_iff

theorem Matrix.range_toLin' (M : Matrix m n R) :
    LinearMap.range (Matrix.toLin' M) = span R (range M.col) :=
  Matrix.range_mulVecLin _

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mulVec` and `M'.mulVec`. -/
@[simps]
def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (m → R) ≃ₗ[R] n → R :=
  { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x ↦ by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x ↦ by
      rw [← Matrix.toLin'_mul_apply, hM'M, Matrix.toLin'_one, id_apply] }

/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `Matrix n n R`. -/
def LinearMap.toMatrixAlgEquiv' : ((n → R) →ₗ[R] n → R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_one LinearMap.toMatrix'_mul

/-- A `Matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R :=
  LinearMap.toMatrixAlgEquiv'.symm

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_symm :
    (LinearMap.toMatrixAlgEquiv'.symm : Matrix n n R ≃ₐ[R] _) = Matrix.toLinAlgEquiv' :=
  rfl

@[simp]
theorem Matrix.toLinAlgEquiv'_symm :
    (Matrix.toLinAlgEquiv'.symm : ((n → R) →ₗ[R] n → R) ≃ₐ[R] _) = LinearMap.toMatrixAlgEquiv' :=
  rfl

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) = M :=
  LinearMap.toMatrixAlgEquiv'.apply_symm_apply M

@[simp]
theorem Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (f : (n → R) →ₗ[R] n → R) :
    Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' f) = f :=
  Matrix.toLinAlgEquiv'.apply_symm_apply f

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_apply (f : (n → R) →ₗ[R] n → R) (i j) :
    LinearMap.toMatrixAlgEquiv' f i j = f (fun j' ↦ if j' = j then 1 else 0) i := by
  simp [LinearMap.toMatrixAlgEquiv']

@[simp]
theorem Matrix.toLinAlgEquiv'_apply (M : Matrix n n R) (v : n → R) :
    Matrix.toLinAlgEquiv' M v = M *ᵥ v :=
  rfl

theorem Matrix.toLinAlgEquiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.toLin'_one

@[simp]
theorem LinearMap.toMatrixAlgEquiv'_id :
    LinearMap.toMatrixAlgEquiv' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.toMatrix'_id

theorem LinearMap.toMatrixAlgEquiv'_comp (f g : (n → R) →ₗ[R] n → R) :
    LinearMap.toMatrixAlgEquiv' (f.comp g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrix'_comp _ _

theorem LinearMap.toMatrixAlgEquiv'_mul (f g : (n → R) →ₗ[R] n → R) :
    LinearMap.toMatrixAlgEquiv' (f * g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrixAlgEquiv'_comp f g

@[simp]
theorem LinearMap.isUnit_toMatrix'_iff {f : (n → R) →ₗ[R] n → R} : IsUnit f.toMatrix' ↔ IsUnit f :=
  isUnit_map_iff LinearMap.toMatrixAlgEquiv' f

@[simp]
theorem Matrix.isUnit_toLin'_iff {M : Matrix n n R} : IsUnit M.toLin' ↔ IsUnit M :=
  isUnit_map_iff LinearMap.toMatrixAlgEquiv'.symm M

end ToMatrix'

section ToMatrix

section Finite

variable {R : Type*} [CommSemiring R]
variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def LinearMap.toMatrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'

/-- `LinearMap.toMatrix'` is a particular case of `LinearMap.toMatrix`, for the standard basis
`Pi.basisFun R n`. -/
@[simp] theorem LinearMap.toMatrix_eq_toMatrix' :
    LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n) = LinearMap.toMatrix' :=
  rfl

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm

/-- `Matrix.toLin'` is a particular case of `Matrix.toLin`, for the standard basis
`Pi.basisFun R n`. -/
theorem Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin' :=
  rfl

@[simp]
theorem LinearMap.toMatrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂ :=
  rfl

@[simp]
theorem Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂ :=
  rfl

@[simp]
theorem Matrix.toLin_toMatrix (f : M₁ →ₗ[R] M₂) :
    Matrix.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f := by
  rw [← Matrix.toLin_symm, LinearEquiv.apply_symm_apply]

@[simp]
theorem LinearMap.toMatrix_toLin (M : Matrix m n R) :
    LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M := by
  rw [← Matrix.toLin_symm, LinearEquiv.symm_apply_apply]

theorem LinearMap.toMatrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i := by
  rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, Basis.equivFun_symm_apply, Finset.sum_eq_single j, if_pos rfl,
    one_smul, Basis.equivFun_apply]
  · intro j' _ hj'
    rw [if_neg hj', zero_smul]
  · intro hj
    have := Finset.mem_univ j
    contradiction

theorem LinearMap.toMatrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  funext fun i ↦ f.toMatrix_apply _ _ i j

theorem LinearMap.toMatrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  LinearMap.toMatrix_apply v₁ v₂ f i j

theorem LinearMap.toMatrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  LinearMap.toMatrix_transpose_apply v₁ v₂ f j

/-- This will be a special case of `LinearMap.toMatrix_id_eq_basis_toMatrix`. -/
theorem LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ id = 1 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

@[simp]
theorem LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1 :=
  LinearMap.toMatrix_id v₁

@[simp]
lemma LinearMap.toMatrix_singleton {ι : Type*} [Unique ι] (f : R →ₗ[R] R) (i j : ι) :
    f.toMatrix (.singleton ι R) (.singleton ι R) i j = f 1 := by
  simp [toMatrix, Subsingleton.elim j default]

@[simp]
theorem Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrix_id v₁, Matrix.toLin_toMatrix]

theorem LinearMap.toMatrix_reindexRange [DecidableEq M₁] (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
    LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, Set.mem_range_self k⟩
        ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrix v₁ v₂ f k i := by
  simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

@[simp]
theorem LinearMap.toMatrix_algebraMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id, smul_eq_diagonal_mul]

theorem LinearMap.toMatrix_mulVec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
    LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x) := by
  ext i
  rw [← Matrix.toLin'_apply, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix',
    LinearEquiv.arrowCongr_apply, v₂.equivFun_apply]
  congr
  exact v₁.equivFun.symm_apply_apply x

@[simp]
theorem LinearMap.toMatrix_basis_equiv [Fintype l] [DecidableEq l] (b : Basis l R M₁)
    (b' : Basis l R M₂) :
    LinearMap.toMatrix b' b (b'.equiv b (Equiv.refl l) : M₂ →ₗ[R] M₁) = 1 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

theorem LinearMap.toMatrix_smulBasis_left {G} [Group G] [DistribMulAction G M₁]
    [SMulCommClass G R M₁] (g : G) (f : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix (g • v₁) v₂ f =
      LinearMap.toMatrix v₁ v₂ (f ∘ₗ DistribMulAction.toLinearMap _ _ g) := by
  rfl

theorem LinearMap.toMatrix_smulBasis_right {G} [Group G] [DistribMulAction G M₂]
    [SMulCommClass G R M₂] (g : G) (f : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ (g • v₂) f =
      LinearMap.toMatrix v₁ v₂ (DistribMulAction.toLinearMap _ _ g⁻¹ ∘ₗ f) := by
  rfl

end Finite

variable {R : Type*} [CommSemiring R]
variable {l m n : Type*} [Fintype n] [Fintype m] [DecidableEq n]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

omit [DecidableEq n] in
/-- The matrix of `toSpanSingleton R M₂ x` given by bases `v₁` and `v₂` is equal to
`vecMulVec (v₂.repr x) v₁`. When `v₁ = Module.Basis.singleton`
then this is the column matrix of `v₂.repr x`.` -/
theorem LinearMap.toMatrix_toSpanSingleton [DecidableEq m] (v₁ : Module.Basis m R R) (x : M₂) :
    (toSpanSingleton R M₂ x).toMatrix v₁ v₂ = vecMulVec (v₂.repr x) v₁ := by
  ext; simp [toMatrix_apply, vecMulVec_apply, mul_comm]

theorem Matrix.toLin_apply (M : Matrix m n R) (v : M₁) :
    Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j :=
  show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply, v₂.equivFun_symm_apply]

@[simp]
theorem Matrix.toLin_self (M : Matrix m n R) (i : n) :
    Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j := by
  rw [Matrix.toLin_apply, Finset.sum_congr rfl fun j _hj ↦ ?_]
  rw [Basis.repr_self, Matrix.mulVec, dotProduct, Finset.sum_eq_single i, Finsupp.single_eq_same,
    mul_one]
  · intro i' _ i'_ne
    rw [Finsupp.single_eq_of_ne i'_ne, mul_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

theorem Matrix.toLin_apply_eq_zero_iff {R M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    {v₁ : Basis n R M₁} {v₂ : Basis m R M₂} {A : Matrix m n R} {x : M₁} :
    A.toLin v₁ v₂ x = 0 ↔ ∀ j, (A *ᵥ v₁.repr x) j = 0 := by
  rw [toLin_apply]
  exact ⟨Fintype.linearIndependent_iff.mp v₂.linearIndependent _, fun h ↦ by simp [h]⟩

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem LinearMap.toMatrix_comp [Finite l] [DecidableEq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ v₃ (f.comp g) =
    LinearMap.toMatrix v₂ v₃ f * LinearMap.toMatrix v₁ v₂ g := by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply]
  rw [LinearEquiv.arrowCongr_comp _ v₂.equivFun, LinearMap.toMatrix'_comp]

theorem LinearMap.toMatrix_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix v₁ v₁ g := by
  rw [Module.End.mul_eq_comp, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

lemma LinearMap.toMatrix_pow (f : M₁ →ₗ[R] M₁) (k : ℕ) :
    (toMatrix v₁ v₁ f) ^ k = toMatrix v₁ v₁ (f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih, ← toMatrix_mul]

theorem Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin v₁ v₂ B) := by
  apply (LinearMap.toMatrix v₁ v₃).injective
  haveI : DecidableEq l := fun _ _ ↦ Classical.propDecidable _
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  repeat' rw [LinearMap.toMatrix_toLin]

@[simp]
theorem Matrix.toLin_pow (A : Matrix n n R) (k : ℕ) :
    (A ^ k).toLin v₁ v₁ = (A.toLin v₁ v₁) ^ k := by
  induction k with
  | zero => simp only [pow_zero, toLin_one, End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin_mul v₁ v₁, ih, Module.End.mul_eq_comp]

/-- Shortcut lemma for `Matrix.toLin_mul` and `LinearMap.comp_apply`. -/
theorem Matrix.toLin_mul_apply [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
    (x) : Matrix.toLin v₁ v₃ (A * B) x = (Matrix.toLin v₂ v₃ A) (Matrix.toLin v₁ v₂ B x) := by
  rw [Matrix.toLin_mul v₁ v₂, LinearMap.comp_apply]

/-- If `M` and `M` are each other's inverse matrices, `Matrix.toLin M` and `Matrix.toLin M'`
form a linear equivalence. -/
@[simps]
def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
    (hM'M : M' * M = 1) : M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x ↦ by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x ↦ by
      rw [← Matrix.toLin_mul_apply, hMM', Matrix.toLin_one, id_apply] }

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def LinearMap.toMatrixAlgEquiv : (M₁ →ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv
    (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_one v₁) (LinearMap.toMatrix_mul v₁)

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ →ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm

@[simp]
theorem LinearMap.toMatrixAlgEquiv_symm :
    (LinearMap.toMatrixAlgEquiv v₁).symm = Matrix.toLinAlgEquiv v₁ :=
  rfl

@[simp]
theorem Matrix.toLinAlgEquiv_symm :
    (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁ :=
  rfl

@[simp]
theorem Matrix.toLinAlgEquiv_toMatrixAlgEquiv (f : M₁ →ₗ[R] M₁) :
    Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.apply_symm_apply]

@[simp]
theorem LinearMap.toMatrixAlgEquiv_toLinAlgEquiv (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.symm_apply_apply]

theorem LinearMap.toMatrixAlgEquiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]

theorem LinearMap.toMatrixAlgEquiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  funext fun i ↦ f.toMatrix_apply _ _ i j

theorem LinearMap.toMatrixAlgEquiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
  LinearMap.toMatrixAlgEquiv_apply v₁ f i j

theorem LinearMap.toMatrixAlgEquiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j

theorem Matrix.toLinAlgEquiv_apply (M : Matrix n n R) (v : M₁) :
    Matrix.toLinAlgEquiv v₁ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₁ j :=
  show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply, v₁.equivFun_symm_apply]

@[simp]
theorem Matrix.toLinAlgEquiv_self (M : Matrix n n R) (i : n) :
    Matrix.toLinAlgEquiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
  Matrix.toLin_self _ _ _ _

theorem LinearMap.toMatrixAlgEquiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1 := by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]

theorem Matrix.toLinAlgEquiv_one : Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

theorem LinearMap.toMatrixAlgEquiv_reindexRange [DecidableEq M₁] (f : M₁ →ₗ[R] M₁) (k i : n) :
    LinearMap.toMatrixAlgEquiv v₁.reindexRange f
        ⟨v₁ k, Set.mem_range_self k⟩ ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrixAlgEquiv v₁ f k i := by
  simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

theorem LinearMap.toMatrixAlgEquiv_comp (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f.comp g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

theorem LinearMap.toMatrixAlgEquiv_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f * g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  rw [Module.End.mul_eq_comp, LinearMap.toMatrixAlgEquiv_comp v₁ f g]

theorem Matrix.toLinAlgEquiv_mul (A B : Matrix n n R) :
    Matrix.toLinAlgEquiv v₁ (A * B) =
      (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B) := by
  convert Matrix.toLin_mul v₁ v₁ v₁ A B

@[simp]
theorem LinearMap.isUnit_toMatrix_iff {f : M₁ →ₗ[R] M₁} : IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f :=
  isUnit_map_iff (LinearMap.toMatrixAlgEquiv _) f

@[simp]
theorem Matrix.isUnit_toLin_iff {M : Matrix n n R} : IsUnit (M.toLin v₁ v₁) ↔ IsUnit M :=
  isUnit_map_iff (LinearMap.toMatrixAlgEquiv _).symm M

@[simp]
theorem Matrix.toLin_finTwoProd_apply (a b c d : R) (x : R × R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] x =
      (a * x.fst + b * x.snd, c * x.fst + d * x.snd) := by
  simp [Matrix.toLin_apply, Matrix.mulVec, dotProduct]

theorem Matrix.toLin_finTwoProd (a b c d : R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] =
      (a • LinearMap.fst R R R + b • LinearMap.snd R R R).prod
        (c • LinearMap.fst R R R + d • LinearMap.snd R R R) :=
  LinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _

@[simp]
theorem toMatrix_distrib_mul_action_toLinearMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (DistribMulAction.toLinearMap R M₁ x) =
    Matrix.diagonal fun _ ↦ x := by
  ext
  rw [LinearMap.toMatrix_apply, DistribMulAction.toLinearMap_apply, LinearEquiv.map_smul,
    Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_pi_single, Matrix.diagonal_apply,
    Pi.single_apply]

lemma LinearMap.toMatrix_prodMap [DecidableEq m] [DecidableEq (n ⊕ m)]
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) :
    toMatrix (v₁.prod v₂) (v₁.prod v₂) (φ₁.prodMap φ₂) =
      Matrix.fromBlocks (toMatrix v₁ v₁ φ₁) 0 0 (toMatrix v₂ v₂ φ₂) := by
  ext (i | i) (j | j) <;> simp [toMatrix]

end ToMatrix

namespace Algebra

section Lmul

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem toMatrix_lmul' (x : S) (i j) :
    LinearMap.toMatrix b b (lmul R S x) i j = b.repr (x * b j) i := by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']

@[simp]
theorem toMatrix_lsmul (x : R) :
    LinearMap.toMatrix b b (Algebra.lsmul R R S x) = Matrix.diagonal fun _ ↦ x :=
  toMatrix_distrib_mul_action_toLinearMap b x

/-- `leftMulMatrix b x` is the matrix corresponding to the linear map `fun y ↦ x * y`.

`leftMulMatrix_eq_repr_mul` gives a formula for the entries of `leftMulMatrix`.

This definition is useful for doing (more) explicit computations with `LinearMap.mulLeft`,
such as the trace form or norm map for algebras.
-/
noncomputable def leftMulMatrix : S →ₐ[R] Matrix m m R where
  toFun x := LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    rw [map_zero, LinearEquiv.map_zero]
  map_one' := by
    rw [map_one, LinearMap.toMatrix_one]
  map_add' x y := by
    rw [map_add, LinearEquiv.map_add]
  map_mul' x y := by
    rw [map_mul, LinearMap.toMatrix_mul]
  commutes' r := by
    ext
    rw [lmul_algebraMap, toMatrix_lsmul, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.algebraMap_self_apply]

theorem leftMulMatrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) :=
  rfl

theorem leftMulMatrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (x * b j) i := by
  -- This is defeq to just `toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [leftMulMatrix_apply, toMatrix_lmul' b x i j]

theorem leftMulMatrix_mulVec_repr (x y : S) :
    leftMulMatrix b x *ᵥ b.repr y = b.repr (x * y) :=
  (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y

@[simp]
theorem toMatrix_lmul_eq (x : S) :
    LinearMap.toMatrix b b (LinearMap.mulLeft R x) = leftMulMatrix b x :=
  rfl

theorem leftMulMatrix_injective : Function.Injective (leftMulMatrix b) := fun x x' h ↦
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
    _ = x' := mul_one x'

@[simp]
theorem smul_leftMulMatrix {G} [Group G] [DistribMulAction G S]
    [SMulCommClass G R S] [SMulCommClass G S S] (g : G) (x) :
    leftMulMatrix (g • b) x = leftMulMatrix b x := by
  ext
  simp_rw [leftMulMatrix_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, LinearMap.mul_apply',
    Basis.repr_smul, Basis.smul_apply, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_symm_apply, mul_smul_comm, inv_smul_smul]

variable {A M n : Type*} [Fintype n] [DecidableEq n]
  [CommSemiring A] [AddCommMonoid M] [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M]
  (bA : Basis m R A) (bM : Basis n A M)

lemma _root_.LinearMap.restrictScalars_toMatrix (f : M →ₗ[A] M) :
    (f.restrictScalars R).toMatrix (bA.smulTower' bM) (bA.smulTower' bM) =
      ((f.toMatrix bM bM).map (leftMulMatrix bA)).comp _ _ _ _ _ := by
  ext; simp [toMatrix, Algebra.leftMulMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply, mul_comm]

end Lmul

section LmulTower

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (b : Basis m R S) (c : Basis n S T)

theorem smulTower_leftMulMatrix (x) (ik jk) :
    leftMulMatrix (b.smulTower c) x ik jk =
      leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smulTower_apply,
    Basis.smulTower_repr, Finsupp.smul_apply, id.smul_eq_mul, LinearEquiv.map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']

theorem smulTower_leftMulMatrix_algebraMap (x : S) :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) = blockDiagonal fun _ ↦ leftMulMatrix b x := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [smulTower_leftMulMatrix, AlgHom.commutes, blockDiagonal_apply, algebraMap_matrix_apply]
  split_ifs with h <;> simp only at h <;> simp

theorem smulTower_leftMulMatrix_algebraMap_eq (x : S) (i j k) :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j := by
  rw [smulTower_leftMulMatrix_algebraMap, blockDiagonal_apply_eq]

theorem smulTower_leftMulMatrix_algebraMap_ne (x : S) (i j) {k k'} (h : k ≠ k') :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k') = 0 := by
  rw [smulTower_leftMulMatrix_algebraMap, blockDiagonal_apply_ne _ _ _ h]

end LmulTower

end Algebra

section

variable {R S : Type*} [CommSemiring R] {n : Type*} [DecidableEq n]
variable {M M₁ M₂ : Type*} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable [Semiring S] [Module S M₁] [Module S M₂] [SMulCommClass S R M₁] [SMulCommClass S R M₂]
variable [SMul R S] [IsScalarTower R S M₁] [IsScalarTower R S M₂]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def algEquivMatrix' [Fintype n] : Module.End R (n → R) ≃ₐ[R] Matrix n n R :=
  LinearMap.toMatrixAlgEquiv'

variable (R) in
/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
@[simps!] def LinearEquiv.algConj (e : M₁ ≃ₗ[S] M₂) : Module.End S M₁ ≃ₐ[R] Module.End S M₂ where
  __ := e.conjRingEquiv
  commutes' := fun _ ↦ by ext; change e.restrictScalars R _ = _; simp

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  (h.equivFun.algConj R).trans algEquivMatrix'

end

namespace Module.Basis

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module R M₁] [Module R M₂]
variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]
variable [DecidableEq ι] [DecidableEq ι₁]
variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- The standard basis of the space linear maps between two modules
induced by a basis of the domain and codomain.

If `M₁` and `M₂` are modules with basis `b₁` and `b₂` respectively indexed
by finite types `ι₁` and `ι₂`,
then `Basis.linearMap b₁ b₂` is the basis of `M₁ →ₗ[R] M₂` indexed by `ι₂ × ι₁`
where `(i, j)` indexes the linear map that sends `b j` to `b i`
and sends all other basis vectors to `0`. -/
@[simps! -isSimp repr_apply repr_symm_apply]
noncomputable
def linearMap (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) :
    Basis (ι₂ × ι₁) R (M₁ →ₗ[R] M₂) :=
  (Matrix.stdBasis R ι₂ ι₁).map (LinearMap.toMatrix b₁ b₂).symm

attribute [simp] linearMap_repr_apply

lemma linearMap_apply (ij : ι₂ × ι₁) :
    (b₁.linearMap b₂ ij) = (Matrix.toLin b₁ b₂) (Matrix.stdBasis R ι₂ ι₁ ij) := by
  simp [linearMap]

lemma linearMap_apply_apply (ij : ι₂ × ι₁) (k : ι₁) :
    (b₁.linearMap b₂ ij) (b₁ k) = if ij.2 = k then b₂ ij.1 else 0 := by
  have := Classical.decEq ι₂
  rw [linearMap_apply, Matrix.stdBasis_eq_single, Matrix.toLin_self]
  dsimp only [Matrix.single, of_apply]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The standard basis of the endomorphism algebra of a module
induced by a basis of the module.

If `M` is a module with basis `b` indexed by a finite type `ι`,
then `Basis.end b` is the basis of `Module.End R M` indexed by `ι × ι`
where `(i, j)` indexes the linear map that sends `b j` to `b i`
and sends all other basis vectors to `0`. -/
@[simps! -isSimp repr_apply repr_symm_apply]
noncomputable
abbrev «end» (b : Basis ι R M) : Basis (ι × ι) R (Module.End R M) :=
  b.linearMap b

attribute [simp] end_repr_apply

lemma end_apply (ij : ι × ι) : (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij) :=
  linearMap_apply b b ij

lemma end_apply_apply (ij : ι × ι) (k : ι) : (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0 :=
  linearMap_apply_apply b b ij k

end Module.Basis

section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/--
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-matrix whose entries
are `A`-linear maps `M → M`. In another word, we have`End(Mⁿ) ≅ Matₙₓₙ(End(M))` defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
@[simp]
def endVecRingEquivMatrixEnd :
    Module.End A (ι → M) ≃+* Matrix ι ι (Module.End A M) where
  toFun f i j :=
  { toFun := fun x ↦ f (Pi.single j x) i
    map_add' := fun x y ↦ by simp [Pi.single_add]
    map_smul' := fun x y ↦ by simp [Pi.single_smul] }
  invFun m :=
  { toFun := fun x i ↦ ∑ j, m i j (x j)
    map_add' := by intros; ext; simp [Finset.sum_add_distrib]
    map_smul' := by intros; ext; simp [Finset.smul_sum] }
  left_inv f := by
    ext i x j
    simp only [LinearMap.coe_mk, AddHom.coe_mk, coe_comp, coe_single, Function.comp_apply]
    rw [← Fintype.sum_apply, ← map_sum]
    exact congr_arg₂ _ (by aesop) rfl
  right_inv m := by ext; simp [Pi.single_apply, apply_ite]
  map_mul' f g := by
    ext
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, coeFn_sum,
      Finset.sum_apply]
    rw [← Fintype.sum_apply, ← map_sum]
    exact congr_arg₂ _ (by aesop) rfl
  map_add' f g := by ext; simp

/--
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-matrix whose entries
are `R`-linear maps `M → M`. In another word, we have`End(Mⁿ) ≅ Matₙₓₙ(End(M))` defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
@[simps!]
def endVecAlgEquivMatrixEnd :
    Module.End A (ι → M) ≃ₐ[R] Matrix ι ι (Module.End A M) where
  __ := endVecRingEquivMatrixEnd ι A M
  commutes' r := by
    ext
    simp only [endVecRingEquivMatrixEnd, RingEquiv.toEquiv_eq_coe, Module.algebraMap_end_eq_smul_id,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      LinearMap.smul_apply, id_coe, id_eq, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      LinearMap.coe_mk, AddHom.coe_mk, algebraMap_matrix_apply]
    split_ifs <;> rfl

end

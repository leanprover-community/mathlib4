/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Sesquilinear forms

This file defines an abbreviation for sesquilinear maps. More precisely, given a star ring `R`
and an `R`-module `M`, we define sesquilinear forms to be maps `f : M × M → R` satisfying

* `f (c • x + y) z = star c * (f x z) + f y z` and
* `f x (c • y + z) = c * (f x y) + f x z`.

This is spelled as `M →ₗ⋆[R] M →ₗ[R] R`, and abbreviated to `SesquilinForm R M`.

We define `SesquilinForm.toMatrix` and `SesquilinForm.ofMatrix` and prove that
`f : SesquilinForm R M` is symmetric (in the sense of `LinearMap.IsSymm`) if and only if
`f.toMatrix b` is Hermitian (in the sense of `Matrix.IsHermitian`) (for a certain basis `b`).
-/

open Module (Basis)
open Set LinearMap Finset

variable {R M n : Type*} [AddCommMonoid M] [CommSemiring R] [StarRing R] [Module R M]
    (b : Basis n R M)

variable (R M) in
/-- The type of sesquilinear forms, i.e. maps `f : M × M → R` which are antilinear in the first
coordinate and linear in the second coordinate. -/
abbrev SesquilinForm : Type _ := M →ₗ⋆[R] M →ₗ[R] R

namespace SesquilinForm

noncomputable section

/-- The matrix associated to a sesquilinear form in the basis `b`. -/
def toMatrix (f : SesquilinForm R M) : Matrix n n R :=
  LinearMap.toMatrix₂Aux R b b f

/-- The sesquilinear form associated to a matrix in the basis `b`. -/
def ofMatrix [Fintype n] [DecidableEq n] (A : Matrix n n R) : SesquilinForm R M :=
  (b.equivFun.arrowCongr (b.equivFun.arrowCongr (LinearEquiv.refl R R))).trans
    (LinearMap.toMatrixₛₗ₂' R) |>.symm A

@[simp]
lemma toMatrix_apply (f : SesquilinForm R M) (i j : n) : f.toMatrix b i j = f (b i) (b j) := by
  simp [toMatrix]

@[simp]
lemma ofMatrix_toMatrix [Fintype n] [DecidableEq n] (f : SesquilinForm R M) :
    ofMatrix b (f.toMatrix b) = f := by
  ext x y
  nth_rw 2 [← b.sum_repr x, ← b.sum_repr y]
  simp only [ofMatrix, LinearEquiv.trans_symm, toMatrixₛₗ₂'_symm, toMatrix, LinearEquiv.trans_apply,
    LinearEquiv.arrowCongr_symm_apply, Basis.equivFun_apply, LinearEquiv.refl_symm,
    Matrix.toLinearMapₛₗ₂'_apply, RingHom.id_apply, toMatrix₂Aux_apply, smul_eq_mul, map_sum,
    LinearEquiv.refl_apply, LinearMap.map_smulₛₗ, map_smul, coeFn_sum, Finset.sum_apply, smul_apply,
    mul_sum]
  rw [Finset.sum_comm]
  congr with i
  congr with j
  ring

@[simp]
lemma toMatrix_ofMatrix [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    toMatrix b (ofMatrix b A) = A := by
  ext i j
  simp only [ofMatrix, LinearEquiv.trans_symm, toMatrixₛₗ₂'_symm, LinearEquiv.trans_apply,
    toMatrix_apply, LinearEquiv.arrowCongr_symm_apply, Basis.equivFun_apply, Basis.repr_self,
    LinearEquiv.refl_symm, Matrix.toLinearMapₛₗ₂'_apply, RingHom.id_apply, smul_eq_mul, map_sum,
    LinearEquiv.refl_apply]
  convert Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_
  · symm
    convert Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_
    · simp
    · exact fun _ _ h ↦ by simp [h.symm]
  · exact fun _ _ h ↦ by simp [h.symm]

@[simp]
lemma ofMatrix_apply_basis [Fintype n] [DecidableEq n] (A : Matrix n n R) {i j : n} :
    ofMatrix b A (b i) (b j) = A i j := by
  nth_rw 2 [← toMatrix_ofMatrix b A]
  rw [toMatrix_apply]

lemma ofMatrix_apply [Fintype n] [DecidableEq n] (A : Matrix n n R) (x y : M) :
    ofMatrix b A x y = ∑ i, ∑ j, star (b.repr x i) • b.repr y j • A i j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm ((starRingEnd R) ((Basis.equivFun b) x _))
    ((RingHom.id R) ((Basis.equivFun b) y _)) (A _ _)

lemma dotProduct_toMatrix_mulVec [Fintype n] (f : SesquilinForm R M) (x y : n → R) :
    dotProduct (star x) ((f.toMatrix b).mulVec y) = f (b.equivFun.symm x) (b.equivFun.symm y) := by
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec, toMatrix_apply, mul_sum,
    Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, map_smul,
    coeFn_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  congr with
  congr with
  ring

lemma apply_eq_dotProduct_toMatrix_mulVec [Fintype n] (f : SesquilinForm R M) (x y : M) :
    dotProduct (star (b.repr x)) ((f.toMatrix b).mulVec (b.repr y)) = f x y := by
  nth_rw 2 [← b.sum_repr x, ← b.sum_repr y]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec, toMatrix_apply, mul_sum, map_sum,
    LinearMap.map_smulₛₗ, starRingEnd_apply, map_smul, coeFn_sum, Finset.sum_apply, smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  congr with
  congr with
  ring

lemma isSymm_iff_basis {f : SesquilinForm R M} (b : Basis n R M) :
    f.IsSymm ↔ (∀ i j, star (f (b i) (b j)) = f (b j) (b i)) where
  mp h _ _ := by simp [← starRingEnd_apply, h.eq]
  mpr h := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span R (Set.range b))
    rw [← hx, ← hy]
    simp only [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, map_smul, coeFn_sum,
      Finset.sum_apply, smul_apply, smul_eq_mul, mul_sum, map_mul, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

lemma isSymm_iff_isHermitian_toMatrix (f : SesquilinForm R M) :
    f.IsSymm ↔ (f.toMatrix b).IsHermitian := by
  simp_rw [isSymm_iff_basis b, Matrix.IsHermitian.ext_iff, toMatrix_apply]
  rw [forall_comm]

end

end SesquilinForm

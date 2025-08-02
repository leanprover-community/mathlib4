/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.SesquilinearForm.IsPosSemidef

/-!
# Continuous bilinear forms

Define an abbreviation for continuous bilinear forms.

## Main definitions

* `ContinuousBilinForm.toMatrix`: The matrix representing a continuous bilinear form on a
  finite dimensional space.
* `ContinuousBilinForm.ofMatrix`: The continuous bilinear form represented by a matrix.
* `ContinuousBilinForm.inner`: The inner product as a continuous bilinear form.

## Implementation notes

We choose to redefine `ContinuousBilinForm.toMatrix` on top of `LinearMap.BilinForm.toMatrix`
to allow for dot notation.

## Tags

continuous bilinear form
-/

open Module (Basis)

open scoped Matrix ComplexOrder

namespace ContinuousBilinForm

variable {𝕜 E n : Type*} [NormedAddCommGroup E] [RCLike 𝕜] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- The type of continuous bilinear forms. -/
abbrev _root_.ContinuousBilinForm := E →L⋆[𝕜] E →L[𝕜] 𝕜

variable (b : Basis n 𝕜 E) (f : ContinuousBilinForm 𝕜 E)

/-- The underlying bilinear form of a continuous bilinear form -/
def toSesquilinForm : SesquilinForm 𝕜 E where
  toFun x := f x
  map_add' x y := by simp
  map_smul' m x := by simp

@[simp]
lemma toSesquilinForm_apply (x y : E) : f.toSesquilinForm x y = f x y := rfl

section Matrix

section toMatrix

/-- A continuous bilinear map on a finite dimensional space can be represented by a matrix. -/
noncomputable def toMatrix : Matrix n n 𝕜 := f.toSesquilinForm.toMatrix b

lemma toMatrix_def : f.toMatrix b = f.toSesquilinForm.toMatrix b := rfl

@[simp]
lemma toMatrix_apply (i j : n) : f.toMatrix b i j = f (b i) (b j) := by
  simp [toMatrix]

variable [Fintype n] [DecidableEq n]

lemma dotProduct_toMatrix_mulVec (x y : n → 𝕜) :
    star x ⬝ᵥ (f.toMatrix b) *ᵥ y = f (b.equivFun.symm x) (b.equivFun.symm y) := by
  rw [toMatrix, SesquilinForm.dotProduct_toMatrix_mulVec, toSesquilinForm_apply]

lemma apply_eq_dotProduct_toMatrix_mulVec (x y : E) :
    star (b.repr x) ⬝ᵥ (f.toMatrix b) *ᵥ (b.repr y) = f x y := by
  rw [toMatrix, SesquilinForm.apply_eq_dotProduct_toMatrix_mulVec, toSesquilinForm_apply]

end toMatrix

section ofMatrix

variable [Fintype n] [DecidableEq n] (b : Basis n 𝕜 E) (M : Matrix n n 𝕜)

/-- The continuous bilinear form represented by a matrix. -/
noncomputable def ofMatrix : ContinuousBilinForm 𝕜 E :=
  haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis b
  letI f : E →ₗ⋆[𝕜] E →L[𝕜] 𝕜 :=
    { toFun x := (SesquilinForm.ofMatrix b M x).toContinuousLinearMap
      map_add' x y := by ext; simp
      map_smul' m x := by ext; simp }
  { toLinearMap := f
    cont := by
      let b := Basis.ofVectorSpace 𝕜 E
      have (x : E) : f.toFun x = ∑ i, star (b.equivFun x i) • (f (b i)) := by
        nth_rw 1 [← b.sum_repr x]
        simp
      change Continuous (fun x ↦ f.toFun x)
      simp_rw [this]
      refine continuous_finset_sum _ fun i _ ↦ (continuous_star.comp ?_).smul continuous_const
      exact ((LinearMap.proj i).comp b.equivFun.toLinearMap).continuous_of_finiteDimensional }

lemma ofMatrix_apply' (x y : E) : ofMatrix b M x y = SesquilinForm.ofMatrix b M x y := rfl

lemma ofMatrix_apply (x y : E) :
    ofMatrix b M x y = star (b.repr x) ⬝ᵥ M *ᵥ b.repr y := by
  simp only [ofMatrix_apply', SesquilinForm.ofMatrix_apply, RCLike.star_def, smul_eq_mul,
    dotProduct, Pi.star_apply, Matrix.mulVec, Finset.mul_sum]
  congr with
  congr with
  ring

lemma ofMatrix_basis (i j : n) : ofMatrix b M (b i) (b j) = M i j := by
  simp [ofMatrix_apply, Finsupp.single_eq_pi_single, ← Pi.single_star]

lemma toMatrix_ofMatrix : ofMatrix b (f.toMatrix b) = f := by
  ext x y
  rw [ofMatrix_apply, f.apply_eq_dotProduct_toMatrix_mulVec b]

lemma ofMatrix_toMatrix : (ofMatrix b M).toMatrix b = M := by
  ext i j
  rw [toMatrix_apply, ofMatrix_basis]

end ofMatrix

end Matrix

section IsPosSemidef

/-- `f.IsPosSemidef` is an abbreviation for `f.toSesquilinForm.IsPosSemidef`. -/
abbrev IsPosSemidef : Prop := SesquilinForm.IsPosSemidef f.toSesquilinForm

variable {f}

lemma isPosSemidef_def : f.IsPosSemidef ↔ SesquilinForm.IsPosSemidef f.toSesquilinForm := .rfl

lemma isPosSemidef_iff' : f.IsPosSemidef ↔ f.toSesquilinForm.IsSymm ∧ f.toSesquilinForm.IsPos :=
  isPosSemidef_def.trans SesquilinForm.isPosSemidef_iff

lemma isPosSemidef_iff : f.IsPosSemidef ↔ (∀ x y, star (f x y) = f y x) ∧ (∀ x, 0 ≤ f x x) := by
  simp_rw [isPosSemidef_iff', LinearMap.isSymm_def, SesquilinForm.isPos_def, toSesquilinForm_apply,
    starRingEnd_apply]

lemma isPosSemidef_iff_of_basis : f.IsPosSemidef ↔
    (∀ i j, star (f (b i) (b j)) = f (b j) (b i)) ∧ (∀ x, 0 ≤ f x x) := by
  simp_rw [isPosSemidef_iff', SesquilinForm.isSymm_iff_basis b, SesquilinForm.isPos_def,
    toSesquilinForm_apply]

variable [Fintype n] [DecidableEq n]

lemma isPosSemidef_iff_posSemidef_toMatrix :
    f.IsPosSemidef ↔ (f.toMatrix b).PosSemidef := by
  rw [f.isPosSemidef_def, SesquilinForm.isPosSemidef_iff_posSemidef_toMatrix b, toMatrix_def]

end IsPosSemidef

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

variable (𝕜 E) in
/-- The inner product as continuous bilinear form.
-/
protected noncomputable def inner : ContinuousBilinForm 𝕜 E :=
  letI f : SesquilinForm 𝕜 E := LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (fun x y ↦ ⟪x, y⟫_𝕜)
    inner_add_left
    (fun c m n ↦ inner_smul_left m n c)
    inner_add_right
    (fun c m n ↦ inner_smul_right m n c)
  f.mkContinuous₂ 1 fun x y ↦
    by simpa [f] using norm_inner_le_norm x y

@[simp]
lemma inner_apply (x y : E) : ContinuousBilinForm.inner 𝕜 E x y = ⟪x, y⟫_𝕜 := rfl

lemma isPosSemidef_inner : IsPosSemidef (.inner 𝕜 E) where
  eq := by simp
  nonneg x := by
    rw [toSesquilinForm_apply, inner_apply, RCLike.nonneg_iff]
    exact ⟨inner_self_nonneg, inner_self_im x⟩

variable [Fintype n] [DecidableEq n] (b : OrthonormalBasis n 𝕜 E)

lemma inner_toMatrix_eq_one : (ContinuousBilinForm.inner 𝕜 E).toMatrix b.toBasis = 1 := by
  ext i j
  simp [Matrix.one_apply, b.inner_eq_ite]

end Inner

end ContinuousBilinForm

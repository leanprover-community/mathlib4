/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The partial order on matrices

This file constructs the partial order and star ordered instances on matrices on `𝕜`.
This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices given by `x ≤ y := (y - x).PosSemidef`.
* `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: for a positive semi-definite matrix `A`,
we have `x⋆ A x = 0` iff `A x = 0`.
* `Matrix.PosDef.matrixInnerProductSpace`: the inner product on matrices induced by a
positive definite matrix `M`: `⟪x, y⟫ = (y * M * xᴴ).trace`.

## Implementation notes

Note that the partial order instance is scoped to `MatrixOrder`.
Please `open scoped MatrixOrder` to use this.
-/

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

open scoped ComplexOrder
open Matrix

namespace Matrix

section PartialOrder

/-- The preorder on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
abbrev instPreOrder : Preorder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

open MatrixOrder

lemma le_iff {A B : Matrix n n 𝕜} : A ≤ B ↔ (B - A).PosSemidef := Iff.rfl

lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosSemidef.nonneg

/-- The partial order on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
abbrev instPartialOrder : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    rw [← sub_eq_zero, ← h₂.trace_eq_zero_iff]
    have := neg_nonneg.mp <| trace_neg (A - B) ▸ neg_sub A B ▸ h₁.trace_nonneg
    exact le_antisymm this h₂.trace_nonneg

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

lemma instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_left_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

lemma instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero ℝ A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
      hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x |>.mp hx
    exact hA.posSemidef.eigenvalues_nonneg _

scoped[MatrixOrder] attribute [instance] instNonnegSpectrumClass

lemma instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_left fun A ↦
    ⟨fun hA ↦ by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ rfl⟩,
    fun ⟨A, hA⟩ => hA ▸ (posSemidef_conjTranspose_mul_self A).nonneg⟩

scoped[MatrixOrder] attribute [instance] instStarOrderedRing

end PartialOrder

open scoped MatrixOrder

namespace PosSemidef

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

/-- The positive semidefinite square root of a positive semidefinite matrix -/
@[deprecated CFC.sqrt (since := "2025-09-22")]
noncomputable def sqrt : Matrix n n 𝕜 :=
  hA.1.eigenvectorUnitary.1 * diagonal ((↑) ∘ (√·) ∘ hA.1.eigenvalues) *
  (star hA.1.eigenvectorUnitary : Matrix n n 𝕜)

@[deprecated CFC.sqrt_nonneg (since := "2025-09-22")]
lemma posSemidef_sqrt : PosSemidef (CFC.sqrt A) := CFC.sqrt_nonneg A |>.posSemidef

include hA

@[deprecated CFC.sq_sqrt (since := "2025-09-22")]
lemma sq_sqrt : (CFC.sqrt A) ^ 2 = A := CFC.sq_sqrt A

@[deprecated CFC.sqrt_mul_sqrt_self (since := "2025-09-22")]
lemma sqrt_mul_self : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A

@[deprecated CFC.sq_eq_sq_iff (since := "2025-09-24")]
lemma sq_eq_sq_iff {B : Matrix n n 𝕜} (hB : PosSemidef B) : A ^ 2 = B ^ 2 ↔ A = B :=
  CFC.sq_eq_sq_iff A B

@[deprecated (since := "2025-09-24")] alias ⟨eq_of_sq_eq_sq, _⟩ := CFC.sq_eq_sq_iff

@[deprecated CFC.sqrt_sq (since := "2025-09-22")]
lemma sqrt_sq : CFC.sqrt (A ^ 2) = A := CFC.sqrt_sq A

@[deprecated CFC.sqrt_eq_iff (since := "2025-09-23")]
lemma eq_sqrt_iff_sq_eq {B : Matrix n n 𝕜} (hB : PosSemidef B) : A = CFC.sqrt B ↔ A ^ 2 = B := by
  rw [eq_comm, CFC.sqrt_eq_iff B A hB.nonneg hA.nonneg, sq]

@[deprecated CFC.sqrt_eq_iff (since := "2025-09-23")]
lemma sqrt_eq_iff_eq_sq {B : Matrix n n 𝕜} (hB : PosSemidef B) : CFC.sqrt A = B ↔ A = B ^ 2 := by
  simpa [eq_comm, sq] using CFC.sqrt_eq_iff A B hA.nonneg hB.nonneg

@[deprecated CFC.sqrt_eq_zero_iff (since := "2025-09-22")]
lemma sqrt_eq_zero_iff : CFC.sqrt A = 0 ↔ A = 0 := CFC.sqrt_eq_zero_iff A

@[deprecated CFC.sqrt_eq_one_iff (since := "2025-09-23")]
lemma sqrt_eq_one_iff : CFC.sqrt A = 1 ↔ A = 1 := CFC.sqrt_eq_one_iff A

@[deprecated CFC.isUnit_sqrt_iff (since := "2025-09-22")]
lemma isUnit_sqrt_iff : IsUnit (CFC.sqrt A) ↔ IsUnit A := CFC.isUnit_sqrt_iff A

lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  rw [eq_comm, CFC.sqrt_eq_iff _ _  hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg, ← sq,
    inv_pow', CFC.sq_sqrt A]

end sqrtDeprecated

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
theorem dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero] at h ⊢
  rw [h, mulVec_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
theorem toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

end PosSemidef

/-- A matrix is positive semidefinite if and only if it has the form `Bᴴ * B` for some `B`. -/
@[deprecated CStarAlgebra.nonneg_iff_eq_star_mul_self (since := "2025-09-22")]
lemma posSemidef_iff_eq_conjTranspose_mul_self {A : Matrix n n 𝕜} :
    PosSemidef A ↔ ∃ (B : Matrix n n 𝕜), A = Bᴴ * B := by
  classical
  exact nonneg_iff_posSemidef (A := A) |>.eq ▸ CStarAlgebra.nonneg_iff_eq_star_mul_self

@[deprecated (since := "2025-05-07")]
alias posSemidef_iff_eq_transpose_mul_self := CStarAlgebra.nonneg_iff_eq_star_mul_self

theorem posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A ⊆ {a : 𝕜 | 0 ≤ a} := by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_setOf_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    simpa [h1.spectrum_eq_image_range] using @h2 (h1.eigenvalues i)

@[deprecated commute_iff_mul_nonneg (since := "2025-09-23")]
theorem PosSemidef.commute_iff {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Commute A B ↔ (A * B).PosSemidef := by
  classical
  exact nonneg_iff_posSemidef (A := A * B).eq ▸ commute_iff_mul_nonneg hA.nonneg hB.nonneg

/-- A positive semi-definite matrix is positive definite if and only if it is invertible. -/
@[grind =]
theorem PosSemidef.posDef_iff_isUnit [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) : x.PosDef ↔ IsUnit x := by
  refine ⟨fun h => h.isUnit, fun h => ⟨hx.1, fun v hv => ?_⟩⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_iff]
  contrapose! hv
  rw [← map_eq_zero_iff (f := (yᴴ * y).mulVecLin) (mulVec_injective_iff_isUnit.mpr h),
    mulVecLin_apply, ← mulVec_mulVec, hv, mulVec_zero]

theorem isStrictlyPositive_iff_posDef [DecidableEq n] {x : Matrix n n 𝕜} :
    IsStrictlyPositive x ↔ x.PosDef :=
  ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosDef.isStrictlyPositive

@[deprecated IsStrictlyPositive.commute_iff (since := "2025-09-26")]
theorem PosDef.commute_iff {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    Commute A B ↔ (A * B).PosDef := by
  classical
  rw [hA.isStrictlyPositive.commute_iff hB.isStrictlyPositive, isStrictlyPositive_iff_posDef]

@[deprecated IsStrictlyPositive.sqrt (since := "2025-09-26")]
lemma PosDef.posDef_sqrt [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) :
    PosDef (CFC.sqrt M) := hM.isStrictlyPositive.sqrt.posDef

section kronecker
variable {m : Type*} [Fintype m]

open scoped Kronecker

/-- The kronecker product of two positive semi-definite matrices is positive semi-definite. -/
theorem PosSemidef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef := by
  classical
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy.nonneg
  simpa [mul_kronecker_mul, ← conjTranspose_kronecker, star_eq_conjTranspose] using
    posSemidef_conjTranspose_mul_self _

open Matrix in
/-- The kronecker of two positive definite matrices is positive definite. -/
theorem PosDef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosDef) (hy : y.PosDef) : (x ⊗ₖ y).PosDef := by
  classical
  exact hx.posSemidef.kronecker hy.posSemidef |>.posDef_iff_isUnit.mpr <|
    hx.isUnit.kronecker hy.isUnit

end kronecker

/--
A matrix is positive definite if and only if it has the form `Bᴴ * B` for some invertible `B`.
-/
@[deprecated CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self (since := "2025-09-28")]
lemma posDef_iff_eq_conjTranspose_mul_self [DecidableEq n] {A : Matrix n n 𝕜} :
    PosDef A ↔ ∃ B : Matrix n n 𝕜, IsUnit B ∧ A = Bᴴ * B :=
  isStrictlyPositive_iff_posDef.symm.trans CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self

@[deprecated (since := "2025-08-07")] alias PosDef.posDef_iff_eq_conjTranspose_mul_self :=
  CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self

/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
noncomputable def PosDef.matrixNormedAddCommGroup {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (Matrix n n 𝕜) :=
  letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { inner x y := (y * M * xᴴ).trace
    conj_inner_symm _ _ := by
      simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
        conjTranspose_conjTranspose, hM.isHermitian.eq]
    re_inner_nonneg x := RCLike.nonneg_iff.mp
      (hM.posSemidef.mul_mul_conjTranspose_same x).trace_nonneg |>.1
    add_left := by simp [mul_add]
    smul_left := by simp
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      rw [← mul_assoc, ← conjTranspose_conjTranspose x, star_eq_conjTranspose, ← conjTranspose_mul,
        conjTranspose_conjTranspose, mul_assoc, trace_conjTranspose_mul_self_eq_zero_iff] at hx
      lift y to (Matrix n n 𝕜)ˣ using hy
      simpa [← mul_assoc] using congr(y⁻¹ * $hx) }
  this.toNormedAddCommGroup

/-- A positive definite matrix `M` induces an inner product on `Matrix n n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`. -/
def PosDef.matrixInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosDef) :
    letI : NormedAddCommGroup (Matrix n n 𝕜) := hM.matrixNormedAddCommGroup
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

end Matrix

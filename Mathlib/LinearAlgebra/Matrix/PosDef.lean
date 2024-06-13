/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Basic

#align_import linear_algebra.matrix.pos_def from "leanprover-community/mathlib"@"07992a1d1f7a4176c6d3f160209608be4e198566"

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms. Most results require `𝕜 = ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosDef` : a matrix `M : Matrix n n 𝕜` is positive definite if it is hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.
* `Matrix.PosSemidef` : a matrix `M : Matrix n n 𝕜` is positive semidefinite if it is hermitian
  and `xᴴMx` is nonnegative for all `x`.

## Main results

* `Matrix.posSemidef_iff_eq_transpose_mul_self` : a matrix `M : Matrix n n 𝕜` is positive
  semidefinite iff it has the form `Bᴴ * B` for some `B`.
* `Matrix.PosSemidef.sqrt` : the unique positive semidefinite square root of a positive semidefinite
  matrix. (See `Matrix.PosSemidef.eq_sqrt_of_sq_eq` for the proof of uniqueness.)
-/

open scoped ComplexOrder

namespace Matrix

variable {m n R 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
variable [RCLike 𝕜]
open scoped Matrix

/-!
## Positive semidefinite matrices
-/

/-- A matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian and `xᴴ * M * x` is
nonnegative for all `x`. -/
def PosSemidef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, 0 ≤ dotProduct (star x) (M *ᵥ x)
#align matrix.pos_semidef Matrix.PosSemidef

/-- A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegative. -/
lemma posSemidef_diagonal_iff [DecidableEq n] {d : n → R} :
    PosSemidef (diagonal d) ↔ (∀ i : n, 0 ≤ d i) := by
  refine ⟨fun ⟨_, hP⟩ i ↦ by simpa using hP (Pi.single i 1), ?_⟩
  refine fun hd ↦ ⟨isHermitian_diagonal_iff.2 fun i ↦ IsSelfAdjoint.of_nonneg (hd i), ?_⟩
  refine fun x ↦ Finset.sum_nonneg fun i _ ↦ ?_
  simpa only [mulVec_diagonal, mul_assoc] using conjugate_nonneg (hd i) _

namespace PosSemidef

theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1

theorem re_dotProduct_nonneg {M : Matrix n n 𝕜} (hM : M.PosSemidef) (x : n → 𝕜) :
    0 ≤ RCLike.re (dotProduct (star x) (M *ᵥ x)) :=
  RCLike.nonneg_iff.mp (hM.2 _) |>.1

lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A)
    {m : Type*} [Fintype m] (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
  constructor
  · exact isHermitian_conjTranspose_mul_mul B hA.1
  · intro x
    simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.2 (B *ᵥ x)

lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A)
    {m : Type*} [Fintype m] (B : Matrix m n R):
    PosSemidef (B * A * Bᴴ) := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m → n) :
    (M.submatrix e e).PosSemidef := by
  classical
  rw [(by simp : M = 1 * M * 1), submatrix_mul (he₂ := Function.bijective_id),
    submatrix_mul (he₂ := Function.bijective_id), submatrix_id_id]
  simpa only [conjTranspose_submatrix, conjTranspose_one] using
    conjTranspose_mul_mul_same hM (Matrix.submatrix 1 id e)
#align matrix.pos_semidef.submatrix Matrix.PosSemidef.submatrix

theorem transpose {M : Matrix n n R} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  refine ⟨IsHermitian.transpose hM.1, fun x => ?_⟩
  convert hM.2 (star x) using 1
  rw [mulVec_transpose, Matrix.dotProduct_mulVec, star_star, dotProduct_comm]

theorem conjTranspose {M : Matrix n n R} (hM : M.PosSemidef) : Mᴴ.PosSemidef := hM.1.symm ▸ hM

protected lemma zero : PosSemidef (0 : Matrix n n R) :=
  ⟨isHermitian_zero, by simp⟩

protected lemma one [DecidableEq n] : PosSemidef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x => by
    rw [one_mulVec]; exact Fintype.sum_nonneg fun i => star_mul_self_nonneg _⟩

protected lemma pow [DecidableEq n] {M : Matrix n n R} (hM : M.PosSemidef) (k : ℕ) :
    PosSemidef (M ^ k) :=
  match k with
  | 0 => .one
  | 1 => by simpa using hM
  | (k + 2) => by
    rw [pow_succ, pow_succ']
    simpa only [hM.isHermitian.eq] using (hM.pow k).mul_mul_conjTranspose_same M

protected lemma inv [DecidableEq n] {M : Matrix n n R} (hM : M.PosSemidef) : M⁻¹.PosSemidef := by
  by_cases h : IsUnit M.det
  · have := (conjTranspose_mul_mul_same hM M⁻¹).conjTranspose
    rwa [mul_nonsing_inv_cancel_right _ _ h, conjTranspose_conjTranspose] at this
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero

protected lemma zpow [DecidableEq n] {M : Matrix n n R} (hM : M.PosSemidef) (z : ℤ) :
    (M ^ z).PosSemidef := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosSemidef A) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  (hA.re_dotProduct_nonneg _).trans_eq (hA.1.eigenvalues_eq _).symm

section sqrt

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

/-- The positive semidefinite square root of a positive semidefinite matrix -/
noncomputable def sqrt : Matrix n n 𝕜 :=
  hA.1.eigenvectorUnitary.1 * diagonal ((↑) ∘ Real.sqrt ∘ hA.1.eigenvalues) *
  (star hA.1.eigenvectorUnitary : Matrix n n 𝕜)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Custom elaborator to produce output like `(_ : PosSemidef A).sqrt` in the goal view. -/
@[delab app.Matrix.PosSemidef.sqrt]
def delabSqrt : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOverApp 7 <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``Matrix.PosSemidef.sqrt 7
    let optionsPerPos ← withNaryArg 6 do
      return (← read).optionsPerPos.setBool (← getPos) `pp.proofs.withType true
    withTheReader Context ({· with optionsPerPos}) delab

lemma posSemidef_sqrt : PosSemidef hA.sqrt := by
  apply PosSemidef.mul_mul_conjTranspose_same
  refine posSemidef_diagonal_iff.mpr fun i ↦ ?_
  rw [Function.comp_apply, RCLike.nonneg_iff]
  constructor
  · simp only [RCLike.ofReal_re]
    exact Real.sqrt_nonneg _
  · simp only [RCLike.ofReal_im]

@[simp]
lemma sq_sqrt : hA.sqrt ^ 2 = A := by
  let C : Matrix n n 𝕜 := hA.1.eigenvectorUnitary
  let E := diagonal ((↑) ∘ Real.sqrt ∘ hA.1.eigenvalues : n → 𝕜)
  suffices C * (E * (star C * C) * E) * star C = A by
    rw [Matrix.PosSemidef.sqrt, pow_two]
    simpa only [← mul_assoc] using this
  have : E * E = diagonal ((↑) ∘ hA.1.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr! with v
    simp [← pow_two, ← RCLike.ofReal_pow, Real.sq_sqrt (hA.eigenvalues_nonneg v)]
  simpa [C, this] using hA.1.spectral_theorem.symm

@[simp]
lemma sqrt_mul_self : hA.sqrt * hA.sqrt = A := by rw [← pow_two, sq_sqrt]

lemma eq_of_sq_eq_sq {B : Matrix n n 𝕜} (hB : PosSemidef B) (hAB : A ^ 2 = B ^ 2) : A = B := by
  /- This is deceptively hard, much more difficult than the positive *definite* case. We follow a
  clever proof due to Koeber and Schäfer. The idea is that if `A ≠ B`, then `A - B` has a nonzero
  real eigenvalue, with eigenvector `v`. Then a manipulation using the identity
  `A ^ 2 - B ^ 2 = A * (A - B) + (A - B) * B` leads to the conclusion that
  `⟨v, A v⟩ + ⟨v, B v⟩ = 0`. Since `A, B` are positive semidefinite, both terms must be zero. Thus
  `⟨v, (A - B) v⟩ = 0`, but this is a nonzero scalar multiple of `⟨v, v⟩`, contradiction. -/
  by_contra h_ne
  let ⟨v, t, ht, hv, hv'⟩ := (hA.1.sub hB.1).exists_eigenvector_of_ne_zero (sub_ne_zero.mpr h_ne)
  have h_sum : 0 = t * (star v ⬝ᵥ A *ᵥ v + star v ⬝ᵥ B *ᵥ v) := calc
    0 = star v ⬝ᵥ (A ^ 2 - B ^ 2) *ᵥ v := by rw [hAB, sub_self, zero_mulVec, dotProduct_zero]
    _ = star v ⬝ᵥ A *ᵥ (A - B) *ᵥ v + star v ⬝ᵥ (A - B) *ᵥ B *ᵥ v := by
      rw [mulVec_mulVec, mulVec_mulVec, ← dotProduct_add, ← add_mulVec, mul_sub, sub_mul,
        add_sub, sub_add_cancel, pow_two, pow_two]
    _ = t * (star v ⬝ᵥ A *ᵥ v) + (star v) ᵥ* (A - B)ᴴ ⬝ᵥ B *ᵥ v := by
      rw [hv', mulVec_smul, dotProduct_smul, RCLike.real_smul_eq_coe_mul,
        dotProduct_mulVec _ (A - B), hA.1.sub hB.1]
    _ = t * (star v ⬝ᵥ A *ᵥ v + star v ⬝ᵥ B *ᵥ v) := by
      simp_rw [← star_mulVec, hv', mul_add, ← RCLike.real_smul_eq_coe_mul, ← smul_dotProduct]
      congr 2 with i
      simp only [Pi.star_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_mul, star_mul',
        RCLike.star_def, RCLike.conj_ofReal]
  replace h_sum : star v ⬝ᵥ A *ᵥ v + star v ⬝ᵥ B *ᵥ v = 0 := by
    rw [eq_comm, ← mul_zero (t : 𝕜)] at h_sum
    exact mul_left_cancel₀ (RCLike.ofReal_ne_zero.mpr ht) h_sum
  have h_van : star v ⬝ᵥ A *ᵥ v = 0 ∧ star v ⬝ᵥ B *ᵥ v = 0 := by
    refine ⟨le_antisymm ?_ (hA.2 v), le_antisymm ?_ (hB.2 v)⟩
    · rw [add_comm, add_eq_zero_iff_eq_neg] at h_sum
      simpa only [h_sum, neg_nonneg] using hB.2 v
    · simpa only [add_eq_zero_iff_eq_neg.mp h_sum, neg_nonneg] using hA.2 v
  have aux : star v ⬝ᵥ (A - B) *ᵥ v = 0 := by
    rw [sub_mulVec, dotProduct_sub, h_van.1, h_van.2, sub_zero]
  rw [hv', dotProduct_smul, RCLike.real_smul_eq_coe_mul, ← mul_zero ↑t] at aux
  exact hv <| Matrix.dotProduct_star_self_eq_zero.mp <| mul_left_cancel₀
    (RCLike.ofReal_ne_zero.mpr ht) aux

lemma sqrt_sq : (hA.pow 2 : PosSemidef (A ^ 2)).sqrt = A :=
  (hA.pow 2).posSemidef_sqrt.eq_of_sq_eq_sq hA (hA.pow 2).sq_sqrt

lemma eq_sqrt_of_sq_eq {B : Matrix n n 𝕜} (hB : PosSemidef B) (hAB : A ^ 2 = B) : A = hB.sqrt := by
  subst B
  rw [hA.sqrt_sq]

end sqrt

end PosSemidef

@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
#align matrix.pos_semidef_submatrix_equiv Matrix.posSemidef_submatrix_equiv

/-- The conjugate transpose of a matrix mulitplied by the matrix is positive semidefinite -/
theorem posSemidef_conjTranspose_mul_self (A : Matrix m n R) : PosSemidef (Aᴴ * A) := by
  refine ⟨isHermitian_transpose_mul_self _, fun x => ?_⟩
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

/-- A matrix multiplied by its conjugate transpose is positive semidefinite -/
theorem posSemidef_self_mul_conjTranspose (A : Matrix m n R) : PosSemidef (A * Aᴴ) := by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_transpose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-- A matrix is positive semidefinite if and only if it has the form `Bᴴ * B` for some `B`. -/
lemma posSemidef_iff_eq_transpose_mul_self {A : Matrix n n 𝕜} :
    PosSemidef A ↔ ∃ (B : Matrix n n 𝕜), A = Bᴴ * B := by
  classical
  refine ⟨fun hA ↦ ⟨hA.sqrt, ?_⟩, fun ⟨B, hB⟩ ↦ (hB ▸ posSemidef_conjTranspose_mul_self B)⟩
  simp_rw [← PosSemidef.sq_sqrt hA, pow_two]
  rw [hA.posSemidef_sqrt.1]

lemma IsHermitian.posSemidef_of_eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : IsHermitian A) (h : ∀ i : n, 0 ≤ hA.eigenvalues i) : PosSemidef A := by
  rw [hA.spectral_theorem]
  refine (posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  simpa using h

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
theorem PosSemidef.dotProduct_mulVec_zero_iff
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · obtain ⟨B, rfl⟩ := posSemidef_iff_eq_transpose_mul_self.mp hA
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero]
    intro h0
    rw [h0, mulVec_zero]
  · intro h0
    rw [h0, dotProduct_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
theorem PosSemidef.toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' A (star x) x = 0 ↔ Matrix.toLin' A x = 0 := by
  simpa only [toLinearMap₂'_apply', toLin'_apply] using hA.dotProduct_mulVec_zero_iff x

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M *ᵥ x)
#align matrix.pos_def Matrix.PosDef

namespace PosDef

theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1
#align matrix.pos_def.is_hermitian Matrix.PosDef.isHermitian

theorem re_dotProduct_pos {M : Matrix n n 𝕜} (hM : M.PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < RCLike.re (dotProduct (star x) (M *ᵥ x)) :=
  RCLike.pos_iff.mp (hM.2 _ hx) |>.1

theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef := by
  refine ⟨hM.1, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, zero_dotProduct, star_zero, RCLike.zero_re']
    exact le_rfl
  · exact le_of_lt (hM.2 x hx)
#align matrix.pos_def.pos_semidef Matrix.PosDef.posSemidef

theorem transpose {M : Matrix n n R} (hM : M.PosDef) : Mᵀ.PosDef := by
  refine ⟨IsHermitian.transpose hM.1, fun x hx => ?_⟩
  convert hM.2 (star x) (star_ne_zero.2 hx) using 1
  rw [mulVec_transpose, Matrix.dotProduct_mulVec, star_star, dotProduct_comm]
#align matrix.pos_def.transpose Matrix.PosDef.transpose

theorem of_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef := by
  refine ⟨hM, fun x hx => ?_⟩
  simp only [toQuadraticForm', QuadraticForm.PosDef, LinearMap.BilinForm.toQuadraticForm_apply,
    toLinearMap₂'_apply'] at hMq
  apply hMq x hx
#align matrix.pos_def_of_to_quadratic_form' Matrix.PosDef.of_toQuadraticForm'

theorem toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  simp only [Matrix.toQuadraticForm', LinearMap.BilinForm.toQuadraticForm_apply,
    toLinearMap₂'_apply']
  apply hM.2 x hx
#align matrix.pos_def_to_quadratic_form' Matrix.PosDef.toQuadraticForm'

/-- The eigenvalues of a positive definite matrix are positive -/
lemma eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosDef A) (i : n) : 0 < hA.1.eigenvalues i := by
  simp only [hA.1.eigenvalues_eq]
  exact hA.re_dotProduct_pos <| hA.1.eigenvectorBasis.orthonormal.ne_zero i

theorem det_pos [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) : 0 < det M := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hM.eigenvalues_pos i
#align matrix.pos_def.det_pos Matrix.PosDef.det_pos

end PosDef

end Matrix

namespace QuadraticForm

variable {n : Type*} [Fintype n]

theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← toQuadraticForm_associated ℝ Q,
    ← LinearMap.toMatrix₂'.left_inv ((associatedHom (R := ℝ) ℝ) Q)]
  exact hQ.toQuadraticForm'
#align quadratic_form.pos_def_of_to_matrix' QuadraticForm.posDef_of_toMatrix'

theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef := by
  rw [← toQuadraticForm_associated ℝ Q, ←
    LinearMap.toMatrix₂'.left_inv ((associatedHom (R := ℝ) ℝ) Q)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ
#align quadratic_form.pos_def_to_matrix' QuadraticForm.posDef_toMatrix'

end QuadraticForm

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
noncomputable abbrev NormedAddCommGroup.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
    { inner := fun x y => dotProduct (star x) (M *ᵥ y)
      conj_symm := fun x y => by
        dsimp only [Inner.inner]
        rw [star_dotProduct, starRingEnd_apply, star_star, star_mulVec, dotProduct_mulVec,
          hM.isHermitian.eq]
      nonneg_re := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact le_of_lt (hM.re_dotProduct_pos h)
      definite := fun x (hx : dotProduct _ _ = 0) => by
        by_contra! h
        simpa [hx, lt_irrefl] using hM.re_dotProduct_pos h
      add_left := by simp only [star_add, add_dotProduct, eq_self_iff_true, forall_const]
      smul_left := fun x y r => by
        simp only
        rw [← smul_eq_mul, ← smul_dotProduct, starRingEnd_apply, ← star_smul] }
#align matrix.normed_add_comm_group.of_matrix Matrix.NormedAddCommGroup.ofMatrix

/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
def InnerProductSpace.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (NormedAddCommGroup.ofMatrix hM) :=
  InnerProductSpace.ofCore _
#align matrix.inner_product_space.of_matrix Matrix.InnerProductSpace.ofMatrix

end Matrix

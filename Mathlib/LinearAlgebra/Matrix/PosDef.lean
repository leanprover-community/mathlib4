/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms. Most results require `𝕜 = ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosDef` : a matrix `M : Matrix n n 𝕜` is positive definite if it is hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.
* `Matrix.PosSemidef` : a matrix `M : Matrix n n 𝕜` is positive semidefinite if it is hermitian
  and `xᴴMx` is nonnegative for all `x`.

## Main results

* `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` : a matrix `M : Matrix n n 𝕜` is positive
  semidefinite iff it has the form `Bᴴ * B` for some `B`.
* `Matrix.posDef_iff_eq_conjTranspose_mul_self` : a matrix `M : Matrix n n 𝕜` is positive
  definite iff it has the form `Bᴴ * B` for some _invertible_ `B`.
* `Matrix.PosSemidef.sqrt` : the unique positive semidefinite square root of a positive semidefinite
  matrix. (See `Matrix.PosSemidef.eq_sqrt_of_sq_eq` for the proof of uniqueness.)
-/

open scoped ComplexOrder

namespace Matrix

variable {m n R 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [CommRing R] [PartialOrder R] [StarRing R]
variable [RCLike 𝕜]
open scoped Matrix

/-!
## Positive semidefinite matrices
-/

/-- A matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian and `xᴴ * M * x` is
nonnegative for all `x`. -/
def PosSemidef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x)

protected theorem PosSemidef.diagonal [StarOrderedRing R] [DecidableEq n] {d : n → R} (h : 0 ≤ d) :
    PosSemidef (diagonal d) :=
  ⟨isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i),
    fun x => by
      refine Fintype.sum_nonneg fun i => ?_
      simpa only [mulVec_diagonal, ← mul_assoc] using conjugate_nonneg (h i) _⟩

/-- A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegative. -/
lemma posSemidef_diagonal_iff [StarOrderedRing R] [DecidableEq n] {d : n → R} :
    PosSemidef (diagonal d) ↔ (∀ i : n, 0 ≤ d i) :=
  ⟨fun ⟨_, hP⟩ i ↦ by simpa using hP (Pi.single i 1), .diagonal⟩

namespace PosSemidef

theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1

theorem re_dotProduct_nonneg {M : Matrix n n 𝕜} (hM : M.PosSemidef) (x : n → 𝕜) :
    0 ≤ RCLike.re (star x ⬝ᵥ (M *ᵥ x)) :=
  RCLike.nonneg_iff.mp (hM.2 _) |>.1

lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A)
    {m : Type*} [Fintype m] (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
  constructor
  · exact isHermitian_conjTranspose_mul_mul B hA.1
  · intro x
    simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.2 (B *ᵥ x)

lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A)
    {m : Type*} [Fintype m] (B : Matrix m n R) :
    PosSemidef (B * A * Bᴴ) := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m → n) :
    (M.submatrix e e).PosSemidef := by
  classical
  rw [(by simp : M = 1 * M * 1), submatrix_mul (he₂ := Function.bijective_id),
    submatrix_mul (he₂ := Function.bijective_id), submatrix_id_id]
  simpa only [conjTranspose_submatrix, conjTranspose_one] using
    conjTranspose_mul_mul_same hM (Matrix.submatrix 1 id e)

theorem transpose {M : Matrix n n R} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  refine ⟨IsHermitian.transpose hM.1, fun x => ?_⟩
  convert hM.2 (star x) using 1
  rw [mulVec_transpose, dotProduct_mulVec, star_star, dotProduct_comm]

@[simp]
theorem _root_.Matrix.posSemidef_transpose_iff {M : Matrix n n R} : Mᵀ.PosSemidef ↔ M.PosSemidef :=
  ⟨(by simpa using ·.transpose), .transpose⟩

theorem conjTranspose {M : Matrix n n R} (hM : M.PosSemidef) : Mᴴ.PosSemidef := hM.1.symm ▸ hM

@[simp]
theorem _root_.Matrix.posSemidef_conjTranspose_iff {M : Matrix n n R} :
    Mᴴ.PosSemidef ↔ M.PosSemidef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

protected lemma zero : PosSemidef (0 : Matrix n n R) :=
  ⟨isHermitian_zero, by simp⟩

protected lemma one [StarOrderedRing R] [DecidableEq n] : PosSemidef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x => by
    rw [one_mulVec]; exact Fintype.sum_nonneg fun i => star_mul_self_nonneg _⟩

protected theorem natCast [StarOrderedRing R] [DecidableEq n] (d : ℕ) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_natCast _, fun x => by
    simp only [natCast_mulVec, dotProduct_smul]
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_nonneg (dotProduct_star_self_nonneg _) _⟩

protected theorem ofNat [StarOrderedRing R] [DecidableEq n] (d : ℕ) [d.AtLeastTwo] :
    PosSemidef (ofNat(d) : Matrix n n R) :=
  .natCast d

protected theorem intCast [StarOrderedRing R] [DecidableEq n] (d : ℤ) (hd : 0 ≤ d) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_intCast _, fun x => by
    simp only [intCast_mulVec, dotProduct_smul]
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_nonneg (dotProduct_star_self_nonneg _) hd⟩

@[simp]
protected theorem _root_.Matrix.posSemidef_intCast_iff
    [StarOrderedRing R] [DecidableEq n] [Nonempty n] [Nontrivial R] (d : ℤ) :
    PosSemidef (d : Matrix n n R) ↔ 0 ≤ d :=
  posSemidef_diagonal_iff.trans <| by simp

protected lemma pow [StarOrderedRing R] [DecidableEq n]
    {M : Matrix n n R} (hM : M.PosSemidef) (k : ℕ) :
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

protected lemma zpow [StarOrderedRing R] [DecidableEq n]
    {M : Matrix n n R} (hM : M.PosSemidef) (z : ℤ) :
    (M ^ z).PosSemidef := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv

protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    rw [add_mulVec, dotProduct_add]
    exact add_nonneg (hA.2 x) (hB.2 x)⟩

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosSemidef A) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  (hA.re_dotProduct_nonneg _).trans_eq (hA.1.eigenvalues_eq _).symm

theorem trace_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ A.trace := by
  classical
  simp [hA.isHermitian.trace_eq_sum_eigenvalues, ← map_sum,
    Finset.sum_nonneg (fun _ _ => hA.eigenvalues_nonneg _)]

theorem det_nonneg [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    0 ≤ M.det := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ ↦ by simpa using hM.eigenvalues_nonneg i

section sqrt

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

/-- The positive semidefinite square root of a positive semidefinite matrix -/
noncomputable def sqrt : Matrix n n 𝕜 :=
  hA.1.eigenvectorUnitary.1 * diagonal ((↑) ∘ (√·) ∘ hA.1.eigenvalues) *
  (star hA.1.eigenvectorUnitary : Matrix n n 𝕜)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Custom elaborator to produce output like `(_ : PosSemidef A).sqrt` in the goal view. -/
@[app_delab Matrix.PosSemidef.sqrt]
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
  let E := diagonal ((↑) ∘ (√·) ∘ hA.1.eigenvalues : n → 𝕜)
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

include hA in
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
  exact hv <| dotProduct_star_self_eq_zero.mp <| mul_left_cancel₀
    (RCLike.ofReal_ne_zero.mpr ht) aux

include hA in
lemma sq_eq_sq_iff {B : Matrix n n 𝕜} (hB : PosSemidef B) : A ^ 2 = B ^ 2 ↔ A = B :=
  ⟨eq_of_sq_eq_sq hA hB, fun h => h ▸ rfl⟩

lemma sqrt_sq : (hA.pow 2 : PosSemidef (A ^ 2)).sqrt = A :=
  (hA.pow 2).posSemidef_sqrt.eq_of_sq_eq_sq hA (hA.pow 2).sq_sqrt

include hA in
lemma eq_sqrt_iff_sq_eq {B : Matrix n n 𝕜} (hB : PosSemidef B) : A = hB.sqrt ↔ A ^ 2 = B :=
  ⟨fun h => h ▸ hB.sq_sqrt, fun h => by subst h; rw [hA.sqrt_sq]⟩

include hA in
lemma sqrt_eq_iff_eq_sq {B : Matrix n n 𝕜} (hB : PosSemidef B) : hA.sqrt = B ↔ A = B ^ 2 := by
  simpa [eq_comm] using eq_sqrt_iff_sq_eq hB hA

@[deprecated (since := "2025-05-07")] alias ⟨_, eq_sqrt_of_sq_eq⟩ := eq_sqrt_iff_sq_eq

@[simp]
lemma sqrt_eq_zero_iff : hA.sqrt = 0 ↔ A = 0 := by
  rw [sqrt_eq_iff_eq_sq _ .zero, zero_pow two_ne_zero]

@[simp]
lemma sqrt_eq_one_iff : hA.sqrt = 1 ↔ A = 1 := by
  rw [sqrt_eq_iff_eq_sq _ .one, one_pow]

@[simp]
lemma isUnit_sqrt_iff : IsUnit hA.sqrt ↔ IsUnit A := by
  conv_rhs => rw [← hA.sqrt_mul_self]
  rw [isUnit_mul_self_iff]

lemma inv_sqrt : hA.sqrt⁻¹ = hA.inv.sqrt := by
  rw [eq_sqrt_iff_sq_eq hA.posSemidef_sqrt.inv, sq, ← Matrix.mul_inv_rev, ← sq, sq_sqrt]

end sqrt

variable [DecidableEq n]

open UnitaryGroup in
theorem _root_.Matrix.UnitaryGroup.posSemidef_conjugate_iff'
    (U : unitaryGroup n R) (x : Matrix n n R) :
    PosSemidef ((star U : Matrix n n R) * x * (U : Matrix n n R)) ↔ x.PosSemidef := by
  simp_rw [PosSemidef, isHermitian_iff_isSelfAdjoint, isSelfAdjoint_unitary_conjugate_iff',
    and_congr_right_iff, ← mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec]
  exact fun h => ⟨fun H y => by simpa using H (star U *ᵥ y), fun H _ => H _⟩

theorem _root_.Matrix.UnitaryGroup.posSemidef_conjugate_iff
    (U : unitaryGroup n R) (x : Matrix n n R) :
    PosSemidef ((U : Matrix n n R) * x * (star U : Matrix n n R)) ↔ x.PosSemidef := by
  simpa using UnitaryGroup.posSemidef_conjugate_iff' (star U) _

open scoped Kronecker in
theorem kronecker [DecidableEq m] {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef := by
  rw [hx.1.spectral_theorem, hy.1.spectral_theorem]
  simp_rw [mul_kronecker_mul, star_eq_conjTranspose, ← conjTranspose_kronecker,
   ← star_eq_conjTranspose]
  have huu (U₁ U₂) : (⟨_, kronecker_mem_unitary (Subtype.mem U₁) (Subtype.mem U₂)⟩
    : unitaryGroup (n × m) 𝕜).1 = U₁ ⊗ₖ U₂ := rfl
  rw [← huu hx.1.eigenvectorUnitary hy.1.eigenvectorUnitary,
    UnitaryGroup.posSemidef_conjugate_iff, diagonal_kronecker_diagonal, posSemidef_diagonal_iff]
  exact fun _ => mul_nonneg (RCLike.ofReal_nonneg.mpr <| hx.eigenvalues_nonneg _)
    (RCLike.ofReal_nonneg.mpr <| hy.eigenvalues_nonneg _)

end PosSemidef

@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

/-- The conjugate transpose of a matrix multiplied by the matrix is positive semidefinite -/
theorem posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (Aᴴ * A) := by
  refine ⟨isHermitian_transpose_mul_self _, fun x => ?_⟩
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

/-- A matrix multiplied by its conjugate transpose is positive semidefinite -/
theorem posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (A * Aᴴ) := by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

theorem trace_conjTranspose_mul_self_eq_zero_iff {A : Matrix m n 𝕜} :
    (Aᴴ * A).trace = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hA := posSemidef_conjTranspose_mul_self A
  classical
  simpa [hA.isHermitian.trace_eq_sum_eigenvalues, Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => RCLike.ofReal_nonneg.mpr <| hA.eigenvalues_nonneg _),
    ← conjTranspose_mul_self_eq_zero, ← hA.isHermitian.eigenvalues_eq_zero_iff, funext_iff] using h

theorem trace_mul_conjTranspose_self_eq_zero_iff {A : Matrix m n 𝕜} :
    (A * Aᴴ).trace = 0 ↔ A = 0 := by
  simpa using trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)

lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_transpose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-- A matrix is positive semidefinite if and only if it has the form `Bᴴ * B` for some `B`. -/
lemma posSemidef_iff_eq_conjTranspose_mul_self {A : Matrix n n 𝕜} :
    PosSemidef A ↔ ∃ (B : Matrix n n 𝕜), A = Bᴴ * B := by
  classical
  refine ⟨fun hA ↦ ⟨hA.sqrt, ?_⟩, fun ⟨B, hB⟩ ↦ (hB ▸ posSemidef_conjTranspose_mul_self B)⟩
  simp_rw [← PosSemidef.sq_sqrt hA, pow_two]
  rw [hA.posSemidef_sqrt.1]

@[deprecated (since := "2025-05-07")]
alias posSemidef_iff_eq_transpose_mul_self := posSemidef_iff_eq_conjTranspose_mul_self

/-- A Hermitian matrix is positive semi-definite if and only if its eigenvalues are non-negative. -/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : IsHermitian A) : PosSemidef A ↔ 0 ≤ hA.eigenvalues := by
  refine ⟨fun h => h.eigenvalues_nonneg, fun h => ?_⟩
  rw [hA.spectral_theorem]
  refine (posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  simpa using h

@[deprecated (since := "2025-08-17")] alias ⟨_, IsHermitian.posSemidef_of_eigenvalues_nonneg⟩ :=
  IsHermitian.posSemidef_iff_eigenvalues_nonneg

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
theorem PosSemidef.dotProduct_mulVec_zero_iff
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · obtain ⟨B, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hA
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero]
    intro h0
    rw [h0, mulVec_zero]
  · intro h0
    rw [h0, dotProduct_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
theorem PosSemidef.toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x)

namespace PosDef

theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1

theorem re_dotProduct_pos {M : Matrix n n 𝕜} (hM : M.PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ (M *ᵥ x)) :=
  RCLike.pos_iff.mp (hM.2 _ hx) |>.1

theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef := by
  refine ⟨hM.1, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, zero_dotProduct, star_zero]
    exact le_rfl
  · exact le_of_lt (hM.2 x hx)

theorem transpose {M : Matrix n n R} (hM : M.PosDef) : Mᵀ.PosDef := by
  refine ⟨IsHermitian.transpose hM.1, fun x hx => ?_⟩
  convert hM.2 (star x) (star_ne_zero.2 hx) using 1
  rw [mulVec_transpose, dotProduct_mulVec, star_star, dotProduct_comm]

@[simp]
theorem transpose_iff {M : Matrix n n R} : Mᵀ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.transpose), .transpose⟩

protected theorem diagonal [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    {d : n → R} (h : ∀ i, 0 < d i) :
    PosDef (diagonal d) :=
  ⟨isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i).le,
    fun x hx => by
      refine Fintype.sum_pos ?_
      simp_rw [mulVec_diagonal, ← mul_assoc, Pi.lt_def]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨fun i => conjugate_nonneg (h i).le _,
        i, conjugate_pos (h _) (isRegular_of_ne_zero hi)⟩⟩

@[simp]
theorem _root_.Matrix.posDef_diagonal_iff
    [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] [Nontrivial R] {d : n → R} :
    PosDef (diagonal d) ↔ ∀ i, 0 < d i := by
  refine ⟨fun h i => ?_, .diagonal⟩
  have := h.2 (Pi.single i 1)
  simp_rw [mulVec_single_one, ← Pi.single_star, star_one, single_dotProduct, one_mul,
    col_apply, diagonal_apply_eq, Function.ne_iff] at this
  exact this ⟨i, by simp⟩

protected theorem one [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] :
    PosDef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x hx => by simpa only [one_mulVec, dotProduct_star_self_pos_iff]⟩

protected theorem natCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) (hd : d ≠ 0) :
    PosDef (d : Matrix n n R) :=
  ⟨isHermitian_natCast _, fun x hx => by
    simp only [natCast_mulVec, dotProduct_smul]
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_pos (dotProduct_star_self_pos_iff.mpr hx) hd⟩

@[simp]
theorem _root_.Matrix.posDef_natCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : ℕ} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
  posDef_diagonal_iff.trans <| by simp

protected theorem ofNat [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) [d.AtLeastTwo] :
    PosDef (ofNat(d) : Matrix n n R) :=
  .natCast d (NeZero.ne _)

protected theorem intCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℤ) (hd : 0 < d) :
    PosDef (d : Matrix n n R) :=
  ⟨isHermitian_intCast _, fun x hx => by
    simp only [intCast_mulVec, dotProduct_smul]
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_pos (dotProduct_star_self_pos_iff.mpr hx) hd⟩

@[simp]
theorem _root_.Matrix.posDef_intCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : ℤ} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
  posDef_diagonal_iff.trans <| by simp

protected lemma add_posSemidef [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosSemidef) : (A + B).PosDef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    rw [add_mulVec, dotProduct_add]
    exact add_pos_of_pos_of_nonneg (hA.2 x hx) (hB.2 x)⟩

protected lemma posSemidef_add [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosDef) : (A + B).PosDef :=
  add_comm A B ▸ hB.add_posSemidef hA

protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosDef) : (A + B).PosDef :=
  hA.add_posSemidef hB.posSemidef

lemma conjTranspose_mul_mul_same {A : Matrix n n R} {B : Matrix n m R} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) :
    (Bᴴ * A * B).PosDef := by
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul _ hA.1, fun x hx => ?_⟩
  have : B *ᵥ x ≠ 0 := fun h => hx <| hB.eq_iff' (mulVec_zero _) |>.1 h
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.2 _ this

lemma mul_mul_conjTranspose_same {A : Matrix n n R} {B : Matrix m n R} (hA : A.PosDef)
    (hB : Function.Injective B.vecMul) :
    (B * A * Bᴴ).PosDef := by
  replace hB := star_injective.comp <| hB.comp star_injective
  simp_rw [Function.comp_def, star_vecMul, star_star] at hB
  simpa using hA.conjTranspose_mul_mul_same (B := Bᴴ) hB

theorem conjTranspose_mul_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
    (hA : Function.Injective A.mulVec) :
    PosDef (Aᴴ * A) := by
  classical
  simpa using conjTranspose_mul_mul_same .one hA

theorem conjTranspose {M : Matrix n n R} (hM : M.PosDef) : Mᴴ.PosDef := hM.1.symm ▸ hM

@[simp]
theorem _root_.Matrix.posDef_conjTranspose_iff {M : Matrix n n R} : Mᴴ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

theorem of_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticMap'.PosDef) : M.PosDef := by
  refine ⟨hM, fun x hx => ?_⟩
  simp only [toQuadraticMap', QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply,
    toLinearMap₂'_apply'] at hMq
  apply hMq x hx

theorem toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticMap'.PosDef := by
  intro x hx
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    toLinearMap₂'_apply']
  apply hM.2 x hx

/-- The eigenvalues of a positive definite matrix are positive -/
lemma eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosDef A) (i : n) : 0 < hA.1.eigenvalues i := by
  simp only [hA.1.eigenvalues_eq]
  exact hA.re_dotProduct_pos <| hA.1.eigenvectorBasis.orthonormal.ne_zero i

/-- A Hermitian matrix is positive-definite if and only if its eigenvalues are positive. -/
lemma _root_.Matrix.IsHermitian.posDef_iff_eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i := by
  refine ⟨fun h => h.eigenvalues_pos, fun h => ?_⟩
  rw [hA.spectral_theorem]
  refine (posDef_diagonal_iff.mpr <| by simpa using h).mul_mul_conjTranspose_same ?_
  rw [vecMul_injective_iff_isUnit, ← unitary.val_toUnits_apply]
  exact Units.isUnit _

theorem trace_pos [Nonempty n] {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < A.trace := by
  classical
  simp [hA.isHermitian.trace_eq_sum_eigenvalues, ← map_sum,
    Finset.sum_pos (fun _ _ => hA.eigenvalues_pos _)]

theorem det_pos [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) : 0 < det M := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hM.eigenvalues_pos i

section Field
variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]

theorem isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : IsUnit M := by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : ∃ a ≠ 0, M *ᵥ a = 0 := by
    obtain ⟨a, b, ha⟩ := Function.not_injective_iff.mp <| mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, ha, mulVec_sub]⟩
  simpa [ha2] using hM.2 _ ha

protected theorem inv [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : M⁻¹.PosDef := by
  have := hM.mul_mul_conjTranspose_same (B := M⁻¹) ?_
  · let _ := hM.isUnit.invertible
    simpa using this.conjTranspose
  · simp only [Matrix.vecMul_injective_iff_isUnit, isUnit_nonsing_inv_iff, hM.isUnit]

@[simp]
theorem _root_.Matrix.posDef_inv_iff [DecidableEq n] {M : Matrix n n K} :
    M⁻¹.PosDef ↔ M.PosDef :=
  ⟨fun h =>
    letI := (Matrix.isUnit_nonsing_inv_iff.1 <| h.isUnit).invertible
    Matrix.inv_inv_of_invertible M ▸ h.inv, (·.inv)⟩

end Field

lemma posDef_sqrt [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) :
    PosDef hM.posSemidef.sqrt := by
  apply PosDef.mul_mul_conjTranspose_same
  · rw [posDef_diagonal_iff]
    simpa using hM.eigenvalues_pos
  · apply Matrix.vecMul_injective_of_isUnit
    convert (Group.isUnit _).map (unitaryGroup n 𝕜).subtype

/--
A matrix is positive definite if and only if it has the form `Bᴴ * B` for some invertible `B`.
-/
lemma _root_.Matrix.posDef_iff_eq_conjTranspose_mul_self [DecidableEq n] {A : Matrix n n 𝕜} :
    PosDef A ↔ ∃ B : Matrix n n 𝕜, IsUnit B ∧ A = Bᴴ * B := by
  refine ⟨fun hA ↦ ⟨_, hA.posDef_sqrt.isUnit, ?_⟩, fun ⟨B, hB, hA⟩ ↦ (hA ▸ ?_)⟩
  · simp [hA.posDef_sqrt.isHermitian.eq]
  · exact conjTranspose_mul_self _ (mulVec_injective_of_isUnit hB)

@[deprecated (since := "07-08-2025")] alias posDef_iff_eq_conjTranspose_mul_self :=
  Matrix.posDef_iff_eq_conjTranspose_mul_self

/-- A positive semi-definite matrix is positive definite if and only if it is invertible. -/
@[grind =]
theorem _root_.Matrix.PosSemidef.posDef_iff_isUnit [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) : x.PosDef ↔ IsUnit x := by
  refine ⟨fun h => h.isUnit, fun h => ⟨hx.1, fun v hv => ?_⟩⟩
  obtain ⟨y, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hx
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, ← star_mulVec, ← dotProduct_mulVec,
    dotProduct_star_self_pos_iff]
  contrapose! hv
  rw [← map_eq_zero_iff (f := (yᴴ * y).mulVecLin) (mulVec_injective_iff_isUnit.mpr h),
    mulVecLin_apply, ← mulVec_mulVec, hv, mulVec_zero]

open UnitaryGroup in
theorem _root_.Matrix.UnitaryGroup.posDef_conjugate_iff' [DecidableEq n]
    (U : unitaryGroup n R) {x : Matrix n n R} :
    PosDef ((star U : Matrix n n R) * x * (U : Matrix n n R)) ↔ x.PosDef := by
  simp_rw [PosDef, isHermitian_iff_isSelfAdjoint, isSelfAdjoint_unitary_conjugate_iff',
    and_congr_right_iff, ← mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose,
    ← star_mulVec, ← dotProduct_mulVec]
  refine fun h => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · simpa [UnitaryGroup.toLinearEquiv] using
      h _ (map_ne_zero_iff _ (UnitaryGroup.toLinearEquiv U⁻¹).injective |>.mpr hx)
  · simpa [UnitaryGroup.toLinearEquiv] using
      h _ (map_ne_zero_iff _ (UnitaryGroup.toLinearEquiv U).injective |>.mpr hx)

theorem _root_.Matrix.UnitaryGroup.posDef_conjugate_iff [DecidableEq n]
    (U : unitaryGroup n R) {x : Matrix n n R} :
    PosDef ((U : Matrix n n R) * x * (star U : Matrix n n R)) ↔ x.PosDef := by
  simpa using UnitaryGroup.posDef_conjugate_iff' (star U)

open scoped Kronecker in
theorem kronecker [DecidableEq n] [DecidableEq m] {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosDef) (hy : y.PosDef) : (x ⊗ₖ y).PosDef := by
  rw [hx.1.spectral_theorem, hy.1.spectral_theorem]
  simp_rw [mul_kronecker_mul, star_eq_conjTranspose, ← conjTranspose_kronecker,
   ← star_eq_conjTranspose]
  have huu (U₁ U₂) : (⟨_, kronecker_mem_unitary (Subtype.mem U₁) (Subtype.mem U₂)⟩
    : unitaryGroup (n × m) 𝕜).1 = U₁ ⊗ₖ U₂ := rfl
  rw [← huu hx.1.eigenvectorUnitary hy.1.eigenvectorUnitary,
    UnitaryGroup.posDef_conjugate_iff, diagonal_kronecker_diagonal, posDef_diagonal_iff]
  exact fun _ => mul_pos (RCLike.ofReal_pos.mpr <| hx.eigenvalues_pos _)
    (RCLike.ofReal_pos.mpr <| hy.eigenvalues_pos _)

end PosDef

end Matrix

namespace QuadraticForm

open QuadraticMap

variable {n : Type*} [Fintype n]

theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← toQuadraticMap_associated ℝ Q,
    ← (LinearMap.toMatrix₂' ℝ).left_inv ((associatedHom (R := ℝ) ℝ) Q)]
  exact hQ.toQuadraticForm'

theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef := by
  rw [← toQuadraticMap_associated ℝ Q, ←
    (LinearMap.toMatrix₂' ℝ).left_inv ((associatedHom (R := ℝ) ℝ) Q)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ

end QuadraticForm

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
noncomputable abbrev NormedAddCommGroup.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
    { inner := fun x y => (M *ᵥ y) ⬝ᵥ star x
      conj_inner_symm := fun x y => by
        rw [dotProduct_comm, star_dotProduct, starRingEnd_apply, star_star,
          star_mulVec, dotProduct_comm (M *ᵥ y), dotProduct_mulVec, hM.isHermitian.eq]
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (dotProduct_comm _ (M *ᵥ x) ▸ hM.re_dotProduct_pos h).le
      definite := fun x (hx : _ ⬝ᵥ _ = 0) => by
        by_contra! h
        simpa [hx, lt_irrefl, dotProduct_comm] using hM.re_dotProduct_pos h
      add_left := by simp only [star_add, dotProduct_add, forall_const]
      smul_left := fun x y r => by
        rw [← smul_eq_mul, ← dotProduct_smul, starRingEnd_apply, ← star_smul] }

/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
def InnerProductSpace.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (NormedAddCommGroup.ofMatrix hM).toSeminormedAddCommGroup :=
  InnerProductSpace.ofCore _

end Matrix

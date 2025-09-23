/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms. Most results require `𝕜 = ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosDef` : a matrix `M : Matrix n n 𝕜` is positive definite if it is Hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.
* `Matrix.PosSemidef` : a matrix `M : Matrix n n 𝕜` is positive semidefinite if it is Hermitian
  and `xᴴMx` is nonnegative for all `x`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices
* `Matrix.instStarOrderedRing`: the star ordered ring instance on matrices
* `Matrix.posDef_iff_eq_conjTranspose_mul_self`: a matrix `M : Matrix n n 𝕜` is positive
  definite iff it has the form `Bᴴ * B` for some _invertible_ `B`.
-/

open scoped ComplexOrder

namespace Matrix

variable {m n R R' 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [Ring R] [PartialOrder R] [StarRing R]
variable [CommRing R'] [PartialOrder R'] [StarRing R']
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

theorem transpose {M : Matrix n n R'} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  refine ⟨IsHermitian.transpose hM.1, fun x => ?_⟩
  convert hM.2 (star x) using 1
  rw [mulVec_transpose, dotProduct_mulVec, star_star, dotProduct_comm]

@[simp]
theorem _root_.Matrix.posSemidef_transpose_iff {M : Matrix n n R'} : Mᵀ.PosSemidef ↔ M.PosSemidef :=
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
    rw [natCast_mulVec, Nat.cast_smul_eq_nsmul, dotProduct_smul]
    exact nsmul_nonneg (dotProduct_star_self_nonneg _) _⟩

protected theorem ofNat [StarOrderedRing R] [DecidableEq n] (d : ℕ) [d.AtLeastTwo] :
    PosSemidef (ofNat(d) : Matrix n n R) :=
  .natCast d

protected theorem intCast [StarOrderedRing R] [DecidableEq n] (d : ℤ) (hd : 0 ≤ d) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_intCast _, fun x => by
    rw [intCast_mulVec, Int.cast_smul_eq_zsmul, dotProduct_smul]
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

protected lemma inv [DecidableEq n] {M : Matrix n n R'} (hM : M.PosSemidef) : M⁻¹.PosSemidef := by
  by_cases h : IsUnit M.det
  · have := (conjTranspose_mul_mul_same hM M⁻¹).conjTranspose
    rwa [mul_nonsing_inv_cancel_right _ _ h, conjTranspose_conjTranspose] at this
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero

protected lemma zpow [StarOrderedRing R'] [DecidableEq n]
    {M : Matrix n n R'} (hM : M.PosSemidef) (z : ℤ) :
    (M ^ z).PosSemidef := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv

protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    rw [add_mulVec, dotProduct_add]
    exact add_nonneg (hA.2 x) (hB.2 x)⟩

protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulMono α R] {x : Matrix n n R}
    (hx : x.PosSemidef) {a : α} (ha : 0 ≤ a) : (a • x).PosSemidef := by
  refine ⟨IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha) hx.1, fun y => ?_⟩
  simp only [smul_mulVec, dotProduct_smul]
  exact smul_nonneg ha (hx.2 _)

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

section trace
-- TODO: move these results to an earlier file

variable {R : Type*} [PartialOrder R] [NonUnitalRing R]
  [StarRing R] [StarOrderedRing R] [NoZeroDivisors R]

theorem trace_conjTranspose_mul_self_eq_zero_iff {A : Matrix m n R} :
    (Aᴴ * A).trace = 0 ↔ A = 0 := by
  rw [← star_vec_dotProduct_vec, dotProduct_star_self_eq_zero, vec_eq_zero_iff]

theorem trace_mul_conjTranspose_self_eq_zero_iff {A : Matrix m n R} :
    (A * Aᴴ).trace = 0 ↔ A = 0 := by
  simpa using trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)

end trace

lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_transpose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-- A Hermitian matrix is positive semi-definite if and only if its eigenvalues are non-negative. -/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : IsHermitian A) : PosSemidef A ↔ 0 ≤ hA.eigenvalues := by
  refine ⟨fun h => h.eigenvalues_nonneg, fun h => ?_⟩
  rw [hA.spectral_theorem]
  refine (posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  simpa using h

@[deprecated (since := "2025-08-17")] alias ⟨_, IsHermitian.posSemidef_of_eigenvalues_nonneg⟩ :=
  IsHermitian.posSemidef_iff_eigenvalues_nonneg

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

section PartialOrder

open scoped ComplexOrder

instance [AddLeftMono R] : Preorder (Matrix n n R) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

lemma le_iff [AddLeftMono R] {A B : Matrix n n R} : A ≤ B ↔ (B - A).PosSemidef := Iff.rfl

lemma nonneg_iff [AddLeftMono R] {A : Matrix n n R} :
    0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨_, PosSemidef.nonneg⟩ := nonneg_iff

instance : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    have foo := neg_sub A B ▸ h₁.trace_nonneg
    rw [trace_neg, neg_nonneg] at foo
    have : (A - B).trace = 0 := le_antisymm foo h₂.trace_nonneg
    classical
    rw [← sub_eq_zero, ← h₂.isHermitian.eigenvalues_eq_zero_iff]
    ext i
    rw [h₂.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum] at this
    norm_cast at this
    rw [← (Finset.univ (α := n)).sum_const_zero, eq_comm,
      Finset.sum_eq_sum_iff_of_le (by simpa using h₂.eigenvalues_nonneg)] at this
    exact this i (by simp) |>.symm

instance : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_left_eq_sub]

instance : NonnegSpectrumClass ℝ (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    rw [nonneg_iff, posSemidef_iff_isHermitian_and_spectrum_nonneg] at hA
    simp only [quasispectrum_eq_spectrum_union_zero ℝ A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    simpa using @hA.2 (x : 𝕜) hx

instance : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_left fun A ↦
    ⟨fun hA ↦ by
      have := QuasispectrumRestricts.nnreal_of_nonneg hA
      rw [nonneg_iff] at hA
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian this
      exact ⟨X, by rw [hX.star_eq]⟩,
    fun ⟨A, hA⟩ => by
      rw [nonneg_iff, hA, star_eq_conjTranspose]
      exact posSemidef_conjTranspose_mul_self A⟩

end PartialOrder

namespace PosSemidef

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

/-- The positive semidefinite square root of a positive semidefinite matrix -/
@[deprecated CFC.sqrt (since := "2025-09-22")]
noncomputable def sqrt : Matrix n n 𝕜 :=
  hA.1.eigenvectorUnitary.1 * diagonal ((↑) ∘ (√·) ∘ hA.1.eigenvalues) *
  (star hA.1.eigenvectorUnitary : Matrix n n 𝕜)

@[deprecated CFC.sqrt_nonneg (since := "2025-09-22")]
lemma posSemidef_sqrt : PosSemidef (CFC.sqrt A) := nonneg_iff.mp (CFC.sqrt_nonneg A)

include hA in
@[deprecated CFC.sq_sqrt (since := "2025-09-22")]
lemma sq_sqrt : (CFC.sqrt A) ^ 2 = A := CFC.sq_sqrt A hA.nonneg

include hA in
@[deprecated CFC.sqrt_mul_sqrt_self (since := "2025-09-22")]
lemma sqrt_mul_self : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg

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

include hA in
@[deprecated CFC.sqrt_sq (since := "2025-09-22")]
lemma sqrt_sq : CFC.sqrt (A ^ 2) = A := CFC.sqrt_sq A hA.nonneg

include hA in
lemma eq_sqrt_iff_sq_eq {B : Matrix n n 𝕜} (hB : PosSemidef B) : A = CFC.sqrt B ↔ A ^ 2 = B := by
  rw [eq_comm, CFC.sqrt_eq_iff B A hB.nonneg hA.nonneg, sq]

include hA in
lemma sqrt_eq_iff_eq_sq {B : Matrix n n 𝕜} (hB : PosSemidef B) : CFC.sqrt A = B ↔ A = B ^ 2 := by
  simpa [eq_comm] using eq_sqrt_iff_sq_eq hB hA

@[deprecated (since := "2025-05-07")] alias ⟨_, eq_sqrt_of_sq_eq⟩ := eq_sqrt_iff_sq_eq

include hA in
@[deprecated CFC.sqrt_eq_zero_iff (since := "2025-09-22")]
lemma sqrt_eq_zero_iff : CFC.sqrt A = 0 ↔ A = 0 := CFC.sqrt_eq_zero_iff A hA.nonneg

include hA in
@[simp]
lemma sqrt_eq_one_iff : CFC.sqrt A = 1 ↔ A = 1 := by
  rw [sqrt_eq_iff_eq_sq hA .one, one_pow]

include hA in
@[deprecated CFC.isUnit_sqrt_iff (since := "2025-09-22")]
lemma isUnit_sqrt_iff : IsUnit (CFC.sqrt A) ↔ IsUnit A := CFC.isUnit_sqrt_iff A hA.nonneg

include hA in
lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  have := hA.nonneg
  rw [eq_sqrt_iff_sq_eq (nonneg_iff.mp (CFC.sqrt_nonneg A)).inv hA.inv, sq, ← mul_inv_rev, ← sq,
    CFC.sq_sqrt A]

end sqrtDeprecated

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
theorem dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  classical
  constructor
  · obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose,
      vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero]
    intro h0
    rw [h0, mulVec_zero]
  · intro h0
    rw [h0, dotProduct_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
theorem toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

end PosSemidef

/-- A matrix is positive semidefinite if and only if it has the form `Bᴴ * B` for some `B`. -/
@[deprecated CStarAlgebra.nonneg_iff_eq_star_mul_self (since := "2025-09-22")]
lemma posSemidef_iff_eq_conjTranspose_mul_self [DecidableEq n] {A : Matrix n n 𝕜} :
    PosSemidef A ↔ ∃ (B : Matrix n n 𝕜), A = Bᴴ * B :=
  nonneg_iff (A := A) |>.eq ▸ CStarAlgebra.nonneg_iff_eq_star_mul_self

@[deprecated (since := "2025-05-07")]
alias posSemidef_iff_eq_transpose_mul_self := posSemidef_iff_eq_conjTranspose_mul_self

theorem PosSemidef.commute_iff [DecidableEq n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Commute A B ↔ (A * B).PosSemidef := by
  classical
  rw [hA.isHermitian.commute_iff hB.isHermitian]
  refine ⟨fun hAB => posSemidef_iff_isHermitian_and_spectrum_nonneg.mpr ⟨hAB, ?_⟩,
    fun h => h.isHermitian⟩
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have {s t} (u : Set 𝕜) (h : u ⊆ t := by simp) : s \ u ⊆ t \ u ↔ s ⊆ t := by
    rw [Set.diff_subset_iff, Set.union_diff_cancel h]
  rw [← mul_assoc, mul_assoc _ x, ← this {0}]
  calc
    _ = spectrum 𝕜 ((x * yᴴ)ᴴ * (x * yᴴ)) \ {0} := by
      simp_rw [spectrum.nonzero_mul_comm _ y, conjTranspose_mul, conjTranspose_conjTranspose,
        mul_assoc, star_eq_conjTranspose]
    _ ⊆ {x : 𝕜 | 0 ≤ x} \ {0} := by
      rw [this {0}]
      exact posSemidef_iff_isHermitian_and_spectrum_nonneg.mp
        (posSemidef_conjTranspose_mul_self _) |>.2

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
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

theorem transpose {M : Matrix n n R'} (hM : M.PosDef) : Mᵀ.PosDef := by
  refine ⟨IsHermitian.transpose hM.1, fun x hx => ?_⟩
  convert hM.2 (star x) (star_ne_zero.2 hx) using 1
  rw [mulVec_transpose, dotProduct_mulVec, star_star, dotProduct_comm]

@[simp]
theorem transpose_iff {M : Matrix n n R'} : Mᵀ.PosDef ↔ M.PosDef :=
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
    rw [natCast_mulVec, Nat.cast_smul_eq_nsmul, dotProduct_smul]
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
    rw [intCast_mulVec, Int.cast_smul_eq_zsmul, dotProduct_smul]
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

protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulStrictMono α R]
    {x : Matrix n n R} (hx : x.PosDef) {a : α} (ha : 0 < a) : (a • x).PosDef := by
  refine ⟨IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha.le) hx.1, fun y hy => ?_⟩
  simp only [smul_mulVec, dotProduct_smul]
  exact smul_pos ha (hx.2 _ hy)

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

/-- A positive semi-definite matrix is positive definite if and only if it is invertible. -/
@[grind =]
theorem _root_.Matrix.PosSemidef.posDef_iff_isUnit [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) : x.PosDef ↔ IsUnit x := by
  refine ⟨fun h => h.isUnit, fun h => ⟨hx.1, fun v hv => ?_⟩⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_iff]
  contrapose! hv
  rw [← map_eq_zero_iff (f := (yᴴ * y).mulVecLin) (mulVec_injective_iff_isUnit.mpr h),
    mulVecLin_apply, ← mulVec_mulVec, hv, mulVec_zero]

theorem commute_iff {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    Commute A B ↔ (A * B).PosDef := by
  classical
  rw [hA.posSemidef.commute_iff hB.posSemidef]
  exact ⟨fun h => h.posDef_iff_isUnit.mpr <| hA.isUnit.mul hB.isUnit, fun h => h.posSemidef⟩

lemma posDef_sqrt [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) :
    PosDef (CFC.sqrt M) := by
  rw [(nonneg_iff.mp (CFC.sqrt_nonneg M)).posDef_iff_isUnit]
  exact CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg |>.mpr hM.isUnit

/--
A matrix is positive definite if and only if it has the form `Bᴴ * B` for some invertible `B`.
-/
lemma _root_.Matrix.posDef_iff_eq_conjTranspose_mul_self [DecidableEq n] {A : Matrix n n 𝕜} :
    PosDef A ↔ ∃ B : Matrix n n 𝕜, IsUnit B ∧ A = Bᴴ * B := by
  refine ⟨fun hA ↦ ⟨_, hA.posDef_sqrt.isUnit, ?_⟩, fun ⟨B, hB, hA⟩ ↦ (hA ▸ ?_)⟩
  · simp [hA.posDef_sqrt.isHermitian.eq, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  · exact conjTranspose_mul_self _ (mulVec_injective_of_isUnit hB)

@[deprecated (since := "07-08-2025")] alias posDef_iff_eq_conjTranspose_mul_self :=
  Matrix.posDef_iff_eq_conjTranspose_mul_self

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

/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
noncomputable def PosDef.matrixNormedAddCommGroup {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (Matrix n n 𝕜) :=
  letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { inner x y := (y * M * xᴴ).trace
    conj_inner_symm _ _ := by
      simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
        conjTranspose_conjTranspose, hM.isHermitian.eq]
    re_inner_nonneg x := by
      classical
      obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
      simpa [mul_assoc] using RCLike.nonneg_iff.mp
        (posSemidef_conjTranspose_mul_self (y * xᴴ)).trace_nonneg |>.1
    add_left := by simp [mul_add]
    smul_left := by simp
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hM
      rw [← mul_assoc, ← conjTranspose_conjTranspose x, ← conjTranspose_mul,
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

/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.
In `Mathlib/Analysis/Matrix/Order.lean`, positive semi-definiteness is used to define the partial
order on matrices on `ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosSemidef` : a matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian
  and `xᴴMx` is nonnegative for all `x`.
* `Matrix.PosDef` : a matrix `M : Matrix n n R` is positive definite if it is Hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.

## Main results

* `Matrix.PosSemidef.fromBlocks₁₁` and `Matrix.PosSemidef.fromBlocks₂₂`: If a matrix `A` is
  positive definite, then `[A B; Bᴴ D]` is positive semidefinite if and only if `D - Bᴴ A⁻¹ B` is
  positive semidefinite.
* `Matrix.PosDef.isUnit`: A positive definite matrix in a field is invertible.
-/

@[expose] public section

-- TODO:
-- assert_not_exists MonoidAlgebra
assert_not_exists NormedGroup

open Matrix

namespace Matrix

variable {m n R R' : Type*}
variable [Fintype m] [Fintype n]
variable [Ring R] [PartialOrder R] [StarRing R]
variable [CommRing R'] [PartialOrder R'] [StarRing R']

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
      simpa only [mulVec_diagonal, ← mul_assoc] using star_left_conjugate_nonneg (h i) _⟩

/-- A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegative. -/
lemma posSemidef_diagonal_iff [StarOrderedRing R] [DecidableEq n] {d : n → R} :
    PosSemidef (diagonal d) ↔ (∀ i : n, 0 ≤ d i) :=
  ⟨fun ⟨_, hP⟩ i ↦ by simpa using hP (Pi.single i 1), .diagonal⟩

namespace PosSemidef

theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1

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

lemma diag_nonneg {A : Matrix n n R} (hA : A.PosSemidef) {i : n} : 0 ≤ A i i := by
  classical simpa [trace] using hA.2 <| Pi.single i 1

lemma trace_nonneg [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef) : 0 ≤ A.trace :=
  Fintype.sum_nonneg fun _ ↦ hA.diag_nonneg

end PosSemidef

@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

/-- The conjugate transpose of a matrix multiplied by the matrix is positive semidefinite -/
theorem posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (Aᴴ * A) := by
  refine ⟨isHermitian_conjTranspose_mul_self _, fun x => ?_⟩
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

/-- A matrix multiplied by its conjugate transpose is positive semidefinite -/
theorem posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (A * Aᴴ) := by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

theorem posSemidef_sum {ι : Type*} [AddLeftMono R]
    {x : ι → Matrix n n R} (s : Finset ι) (h : ∀ i ∈ s, PosSemidef (x i)) :
    PosSemidef (∑ i ∈ s, x i) := by
  refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi |>.1, fun y => ?_⟩
  simp [sum_mulVec, dotProduct_sum, Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

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

section conjugate
variable [DecidableEq n] {U x : Matrix n n R}

/-- For an invertible matrix `U`, `star U * x * U` is positive semi-definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.star_left_conjugate_nonneg_iff` for a similar statement for star-ordered rings. -/
theorem IsUnit.posSemidef_star_left_conjugate_iff (hU : IsUnit U) :
    PosSemidef (star U * x * U) ↔ x.PosSemidef := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conjTranspose_mul_mul_same _⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

/-- For an invertible matrix `U`, `U * x * star U` is positive semi-definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.star_right_conjugate_nonneg_iff` for a similar statement for star-ordered rings. -/
theorem IsUnit.posSemidef_star_right_conjugate_iff (hU : IsUnit U) :
    PosSemidef (U * x * star U) ↔ x.PosSemidef := by
  simpa using hU.star.posSemidef_star_left_conjugate_iff

end conjugate

/-- The matrix `vecMulVec a (star a)` is always positive semi-definite. -/
theorem posSemidef_vecMulVec_self_star [StarOrderedRing R] (a : n → R) :
    (vecMulVec a (star a)).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose]

/-- The matrix `vecMulVec (star a) a` is always postive semi-definite. -/
theorem posSemidef_vecMulVec_star_self [StarOrderedRing R] (a : n → R) :
    (vecMulVec (star a) a).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self]

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
      exact ⟨fun i => star_left_conjugate_nonneg (h i).le _,
        i, star_left_conjugate_pos (h _) (isRegular_of_ne_zero hi)⟩⟩

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

theorem _root_.Matrix.posDef_sum {ι : Type*} [AddLeftMono R] {A : ι → Matrix m m R}
    {s : Finset ι} (hs : s.Nonempty) (hA : ∀ i ∈ s, (A i).PosDef) : (∑ i ∈ s, A i).PosDef := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i hi hins H =>
      rw [Finset.sum_insert hins]
      by_cases h : ¬ hi.Nonempty
      · simp_all
      · exact PosDef.add (hA _ <| Finset.mem_insert_self i hi) <|
          H (not_not.mp h) fun _ _hi => hA _ (Finset.mem_insert_of_mem _hi)

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

theorem mul_conjTranspose_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
    (hA : Function.Injective A.vecMul) :
    PosDef (A * Aᴴ) := by
  classical
  simpa using mul_mul_conjTranspose_same .one hA

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

lemma diag_pos [Nontrivial R] {A : Matrix n n R} (hA : A.PosDef) {i : n} : 0 < A i i := by
  classical simpa [trace] using hA.2 <| Pi.single i 1

lemma trace_pos [Nontrivial R] [IsOrderedCancelAddMonoid R] [Nonempty n] {A : Matrix n n R}
    (hA : A.PosDef) : 0 < A.trace :=
  Finset.sum_pos (fun _ _ ↦ hA.diag_pos) Finset.univ_nonempty

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

section conjugate
variable [DecidableEq n] {x U : Matrix n n R}

/-- For an invertible matrix `U`, `star U * x * U` is positive definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.isStrictlyPositive_star_left_conjugate_iff'` for a similar statement for star-ordered
rings. For matrices, positive definiteness is equivalent to strict positivity when the underlying
field is `ℝ` or `ℂ` (see `Matrix.isStrictlyPositive_iff_posDef`). -/
theorem _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff (hU : IsUnit U) :
    PosDef (star U * x * U) ↔ x.PosDef := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conjTranspose_mul_mul_same <| mulVec_injective_of_isUnit hU⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (Units.isUnit U⁻¹))
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

/-- For an invertible matrix `U`, `U * x * star U` is positive definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.isStrictlyPositive_star_right_conjugate_iff` for a similar statement for star-ordered
rings. For matrices, positive definiteness is equivalent to strict positivity when the underlying
field is `ℝ` or `ℂ` (see `Matrix.isStrictlyPositive_iff_posDef`). -/
theorem _root_.Matrix.IsUnit.posDef_star_right_conjugate_iff (hU : IsUnit U) :
    PosDef (U * x * star U) ↔ x.PosDef := by
  simpa using hU.star.posDef_star_left_conjugate_iff

end conjugate

section SchurComplement

variable [StarOrderedRing R']

theorem fromBlocks₁₁ [DecidableEq m] {A : Matrix m m R'}
    (B : Matrix m n R') (D : Matrix n n R') (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  rw [PosSemidef, IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => ⟨h.1, fun x => ?_⟩
    have := h.2 (-((A⁻¹ * B) *ᵥ x) ⊕ᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply hA.posSemidef.2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply h.2

theorem fromBlocks₂₂ [DecidableEq n] (A : Matrix m m R')
    (B : Matrix m n R') {D : Matrix n n R'} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef := by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert fromBlocks₁₁ Bᴴ A hD <;> simp

end SchurComplement

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

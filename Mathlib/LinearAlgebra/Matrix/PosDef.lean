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
variable [Ring R] [PartialOrder R] [StarRing R]
variable [CommRing R'] [PartialOrder R'] [StarRing R']

/-!
## Positive semidefinite matrices
-/

/-- A matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian and `xᴴ * M * x` is
nonnegative for all `x` of finite support. -/
def PosSemidef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ ∀ x : n →₀ R, 0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

protected theorem PosSemidef.diagonal [StarOrderedRing R] [DecidableEq n] {d : n → R} (h : 0 ≤ d) :
    PosSemidef (diagonal d) where
  left := isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i)
  right x := by
    -- TODO: positivity
    refine Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ ?_
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]

/-- A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegative. -/
@[simp] lemma posSemidef_diagonal_iff [StarOrderedRing R] [DecidableEq n] {d : n → R} :
    PosSemidef (diagonal d) ↔ ∀ i, 0 ≤ d i :=
  ⟨fun ⟨_, hP⟩ i ↦ by simpa using hP (.single i 1), .diagonal⟩

namespace PosSemidef

theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1

theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m → n) :
    (M.submatrix e e).PosSemidef := by
  refine ⟨hM.1.submatrix _, fun x ↦ ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 <| x.mapDomain e

theorem transpose {M : Matrix n n R'} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM.2 (Finsupp.mapRange star (star_zero R') x)

@[simp]
theorem _root_.Matrix.posSemidef_transpose_iff {M : Matrix n n R'} : Mᵀ.PosSemidef ↔ M.PosSemidef :=
  ⟨.transpose, .transpose⟩

theorem conjTranspose {M : Matrix n n R} (hM : M.PosSemidef) : Mᴴ.PosSemidef := hM.1.symm ▸ hM

@[simp]
theorem _root_.Matrix.posSemidef_conjTranspose_iff {M : Matrix n n R} :
    Mᴴ.PosSemidef ↔ M.PosSemidef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    simpa [mul_add, add_mul] using add_nonneg (hA.2 x) (hB.2 x)⟩

protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulMono α R] {x : Matrix n n R}
    (hx : x.PosSemidef) {a : α} (ha : 0 ≤ a) : (a • x).PosSemidef := by
  refine ⟨IsSelfAdjoint.smul (.of_nonneg ha) hx.1, fun y => ?_⟩
  simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hx.2 _)

protected lemma zero : PosSemidef (0 : Matrix n n R) := ⟨isHermitian_zero, by simp⟩

protected lemma one [StarOrderedRing R] [DecidableEq n] : PosSemidef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]⟩

protected theorem natCast [StarOrderedRing R] [DecidableEq n] (d : ℕ) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_natCast _, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_natCast', star_left_conjugate_nonneg, *]⟩

protected theorem ofNat [StarOrderedRing R] [DecidableEq n] (d : ℕ) [d.AtLeastTwo] :
    PosSemidef (ofNat(d) : Matrix n n R) :=
  .natCast d

protected theorem intCast [StarOrderedRing R] [DecidableEq n] (d : ℤ) (hd : 0 ≤ d) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_intCast _, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_intCast', star_left_conjugate_nonneg, *]⟩

@[simp]
protected theorem _root_.Matrix.posSemidef_intCast_iff
    [StarOrderedRing R] [DecidableEq n] [Nonempty n] [Nontrivial R] (d : ℤ) :
    PosSemidef (d : Matrix n n R) ↔ 0 ≤ d := by simp [← diagonal_intCast']

lemma diag_nonneg {A : Matrix n n R} (hA : A.PosSemidef) {i : n} : 0 ≤ A i i := by
  simpa using hA.2 <| .single i 1

end PosSemidef

@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

theorem posSemidef_sum {ι : Type*} [AddLeftMono R]
    {x : ι → Matrix n n R} (s : Finset ι) (h : ∀ i ∈ s, PosSemidef (x i)) :
    PosSemidef (∑ i ∈ s, x i) := by
  refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi |>.1, fun y => ?_⟩
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ ⦃x : n →₀ R⦄, x ≠ 0 → 0 < x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

namespace PosDef

theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1

theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef :=
  ⟨hM.1, fun x ↦ by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩

theorem transpose {M : Matrix n n R'} (hM : M.PosDef) : Mᵀ.PosDef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
      hM.2 (x := x.mapRange star (star_zero R'))

@[simp]
theorem transpose_iff {M : Matrix n n R'} : Mᵀ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.transpose), .transpose⟩

protected theorem diagonal [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    {d : n → R} (h : ∀ i, 0 < d i) :
    PosDef (diagonal d) where
  left := isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i).le
  right x hx := by
    refine Finsupp.sum_pos' (fun _ _ ↦ Finsupp.sum_nonneg ?_) ?_
    · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
    obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
    refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
      apply_ite, star_left_conjugate_nonneg (h _).le,
      star_left_conjugate_pos (h i), isRegular_of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

@[simp]
theorem _root_.Matrix.posDef_diagonal_iff
    [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] [Nontrivial R] {d : n → R} :
    PosDef (diagonal d) ↔ ∀ i, 0 < d i :=
  ⟨fun h i => by simpa using h.2 (x := .single i 1), .diagonal⟩

@[simp, nontriviality]
theorem of_subsingleton (h : Subsingleton R) (M : Matrix n n R) : M.PosDef :=
  ⟨.of_subsingleton, fun _ hx ↦ (hx <| Subsingleton.elim ..).elim⟩

protected theorem one [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] :
    PosDef (1 : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun i ↦ zero_lt_one' R

protected theorem natCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) (hd : d ≠ 0) :
    PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

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
    PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

@[simp]
theorem _root_.Matrix.posDef_intCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : ℤ} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
  posDef_diagonal_iff.trans <| by simp

protected lemma add_posSemidef [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosSemidef) : (A + B).PosDef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hA.2 (x := x) hx) (hB.2 x)⟩

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
  simpa [← Finsupp.smul_sum] using smul_pos ha (hx.2 hy)

theorem conjTranspose {M : Matrix n n R} (hM : M.PosDef) : Mᴴ.PosDef := hM.1.symm ▸ hM

@[simp]
theorem _root_.Matrix.posDef_conjTranspose_iff {M : Matrix n n R} : Mᴴ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

lemma diag_pos [Nontrivial R] {A : Matrix n n R} (hA : A.PosDef) {i : n} : 0 < A i i := by
  classical simpa [trace] using hA.2 (x := Finsupp.single i 1)

end PosDef

/-!
## Finite positive semidefinite matrices
-/

variable [Fintype n] [Fintype m]

/-- A finite matrix `M : Matrix n n R` is positive semidefinite iff it is
Hermitian and `xᴴ * M * x` is nonnegative for all `x`. -/
theorem posSemidef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosSemidef ↔ M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
  simp [PosSemidef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc]

namespace PosSemidef

@[simp]
theorem dotProduct_mulVec_nonneg {M : Matrix n n R} (hM : M.PosSemidef) :
    ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := (posSemidef_iff_dotProduct_mulVec.mp hM).2

lemma of_dotProduct_mulVec_nonneg {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef :=
  posSemidef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

omit [Fintype m] in variable [Finite m] in
lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
  have := Fintype.ofFinite m
  refine of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_mul B hA.1) fun x ↦ ?_
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      hA.dotProduct_mulVec_nonneg (B *ᵥ x)

omit [Fintype m] in variable [Finite m] in
lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix m n R) :
    PosSemidef (B * A * Bᴴ) := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

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

lemma trace_nonneg [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef) : 0 ≤ A.trace :=
  Fintype.sum_nonneg fun _ ↦ hA.diag_nonneg

end PosSemidef

omit [Fintype n] in variable [Finite n] in
/-- The conjugate transpose of a matrix multiplied by the matrix is positive semidefinite -/
theorem posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (Aᴴ * A) := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_self _) fun x => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

omit [Fintype m] in variable [Finite m] in
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

omit [Fintype n] [Fintype m] in variable [Finite n] [Finite m] in
/-- The matrix `vecMulVec a (star a)` is always positive semi-definite. -/
theorem posSemidef_vecMulVec_self_star [StarOrderedRing R] (a : n → R) :
    (vecMulVec a (star a)).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose]

omit [Fintype n] in variable [Finite n] in
/-- The matrix `vecMulVec (star a) a` is always positive semi-definite. -/
theorem posSemidef_vecMulVec_star_self [StarOrderedRing R] (a : n → R) :
    (vecMulVec (star a) a).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self]

/-!
## Finite Positive definite matrices
-/

theorem posDef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosDef ↔ M.IsHermitian ∧ ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x) := by
  have (x : n →₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 ↦ Finsupp.coe_eq_zero.mpr h1,fun h2 ↦ Finsupp.coe_eq_zero.mp h2⟩
  simp [PosDef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

namespace PosDef

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
@[simp]
lemma dotProduct_mulVec_pos {M : Matrix n n R} (hM : M.PosDef) {x} (hx : x ≠ 0) :
    0 < star x ⬝ᵥ (M *ᵥ x) := (posDef_iff_dotProduct_mulVec.mp hM).2 hx

lemma of_dotProduct_mulVec_pos {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x)) : M.PosDef :=
  posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

lemma conjTranspose_mul_mul_same {A : Matrix n n R} {B : Matrix n m R} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) :
    (Bᴴ * A * B).PosDef := by
  refine of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_mul _ hA.1) fun x hx => ?_
  have : B *ᵥ x ≠ 0 := fun h => hx <| hB.eq_iff' (mulVec_zero _) |>.1 h
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.dotProduct_mulVec_pos this

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

theorem of_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticMap'.PosDef) : M.PosDef := by
  refine of_dotProduct_mulVec_pos hM fun x hx ↦ ?_
  simp only [toQuadraticMap', QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply,
    toLinearMap₂'_apply'] at hMq
  apply hMq x hx

theorem toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticMap'.PosDef := by
  intro x hx
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    toLinearMap₂'_apply']
  apply hM.dotProduct_mulVec_pos hx

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
  simpa [ha2] using hM.dotProduct_mulVec_pos ha

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

omit [Fintype n] in variable [Finite n] in
theorem fromBlocks₁₁ [DecidableEq m] {A : Matrix m m R'}
    (B : Matrix m n R') (D : Matrix n n R') (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  have := Fintype.ofFinite n
  rw [posSemidef_iff_dotProduct_mulVec, IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => .of_dotProduct_mulVec_nonneg h.1 fun x => ?_
    have := h.2 (-((A⁻¹ * B) *ᵥ x) ⊕ᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply (posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply (posSemidef_iff_dotProduct_mulVec.mp h).2

omit [Fintype m] in variable [Finite m] in
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

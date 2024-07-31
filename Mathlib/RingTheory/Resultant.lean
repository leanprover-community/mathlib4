import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.CC
import Mathlib.Tactic.SlimCheck

variable {R : Type*}

open BigOperators Polynomial Matrix

section general

/-
We define the Sylvester matrix for two lists. Given P = [a_0, a_1 ,... , a_n] and Q = [b_0, b_1 ,... , b_m]
the Sylvester matrix has size (m + n) × (m + n) and it's given by
    | a_0 0    ...  b_0 0   ... 0 |
    | a_1 a_0  ...  b_1 b_0 ... 0 |
     ....
-/

/-
def sylvester_matrix_list (P Q : List R) :
    Matrix (Fin ((Q.length - 1)  + (P.length - 1))) (Fin ((Q.length - 1) + (P.length - 1))) R :=
  Matrix.of fun i j ↦
  (if hj : j < (Q.length - 1)
    then (if hji : (j : ℕ) ≤ i ∧ (i ≤ j + (P.length - 1)) then P[(i : ℕ) - j]'(Nat.sub_lt_left_of_lt_add hji.1 sorry) else 0)
    else (if hji : (j : ℕ) ≤ i + (Q.length - 1) ∧ (i : ℕ) ≤ j then Q[i + (Q.length - 1) - j]'sorry else 0 ))
-/

variable {m n : ℕ}

def Finsupp.ofList {R : Type*} [DecidableEq R] [Zero R] (xs : List R) : ℕ →₀ R where
  toFun := (fun i => xs.getD i 0)
  support := (Finset.range xs.length).filter (fun i => xs.getD i 0 ≠ 0)
  mem_support_toFun a := by
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    apply List.getD_eq_default

def Polynomial.ofList {R : Type*} [Semiring R] [DecidableEq R] (xs : List R) : R[X] :=
  ⟨Finsupp.ofList xs⟩

/-- Rotate a vector, shifting it `i` indices to the right.

For example, `vecRotate ![1, 2, 3] 1 = ![3, 1, 2]`.
-/
def vecRotate (P : Fin n → R) (i : Fin n) : Fin n → R := fun j ↦ P (j - i)

example : vecRotate ![1, 2, 3] 1 = ![3, 1, 2] := by decide

/-- Resize a vector, adding `x` to the end if it needs to be longer, or cutting of the final
entries if it needs to be shorter. -/
def Fin.pad (P : Fin n → R) (x : R) : Fin m → R
  | ⟨i, _⟩ => if h : i < n then P ⟨i, h⟩ else x

lemma Fin.pad_of_lt (P : Fin n → R) (x : R) (i : Fin m)
    (h : (i : ℕ) < n) : Fin.pad P x i = P ⟨i, h⟩ := by
  simp [pad, h]

lemma Fin.pad_of_ge (P : Fin n → R) (x : R) (i : Fin m)
    (h : n ≤ (i : ℕ)) : Fin.pad P x i = x := by
  simp [pad, not_lt_of_ge h]

@[simp] lemma Fin.pad_cast {a} (P : Fin a → R) (h : n = a) :
    Fin.pad (m := m) (P ∘ Fin.cast h) = Fin.pad P := by
  subst h
  simp

@[simp] lemma Fin.pad_finCongr {a} (P : Fin a → R) (h : n = a) :
    Fin.pad (m := m) (P ∘ finCongr h) = Fin.pad P := by
  subst h
  simp

section Zero

variable [Zero R]

/-- `sylvesterVec P i` is the vector `P` with `i` zeros appended to the left and `m - i` zeros to the right. -/
def sylvesterVec (P : Fin (n + 1) → R) (i : Fin m) : Fin (n + m) → R :=
  vecRotate (Fin.pad P 0) ((i.castAdd _).cast (add_comm _ _))

lemma sylvesterVec_apply (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m)) :
    sylvesterVec P i j = Fin.pad P 0 (j - ((i.castAdd _).cast (add_comm _ _))) :=
  rfl

@[simp] theorem Fin.castAdd_zero_right [NeZero m] [NeZero (m + n)] :
    (castAdd n 0 : Fin (m + n)) = 0 := rfl

@[simp]
lemma sylvesterVec_zero [NeZero m] (P : Fin (n + 1) → R) (j : Fin (n + m)) :
    sylvesterVec P 0 j = Fin.pad P 0 j := by
  have : NeZero (m + n) := ⟨(Nat.add_pos_left (NeZero.pos _) _).ne'⟩
  have : NeZero (n + m) := ⟨(Nat.add_pos_right _ (NeZero.pos _)).ne'⟩
  rw [sylvesterVec_apply, Fin.castAdd_zero_right, Fin.cast_zero, sub_zero j]

lemma sylvesterVec_cast {a} (P : Fin (a + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h : n + 1 = a + 1) :
    sylvesterVec (P ∘ Fin.cast h) i j = sylvesterVec P i (j.cast (by simpa using h)) := by
  have : n = a := Nat.succ_injective h
  subst this
  simp

lemma sylvesterVec_of_lt (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h : (j : ℕ) < i) : sylvesterVec P i j = 0 := by
  rw [sylvesterVec_apply, Fin.pad_of_ge]
  · rw [Nat.succ_le, Fin.coe_sub_iff_lt.mpr h, Fin.coe_cast, Fin.coe_castAdd, add_right_comm _ m,
        Nat.add_sub_assoc i.prop.le, add_assoc]
    simp

lemma sylvesterVec_of_ge_of_le (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h₁ : (i : ℕ) ≤ j) (h₂ : (j : ℕ) - i ≤ n) :
    sylvesterVec P i j = P ⟨(j : ℕ) - i, Nat.lt_succ.mpr h₂⟩ := by
  rw [sylvesterVec_apply, Fin.pad_of_lt]
  · congr
    rw [Fin.coe_sub_iff_le.mpr h₁, Fin.coe_cast, Fin.coe_castAdd]
  · rwa [Nat.lt_succ, Fin.coe_sub_iff_le.mpr h₁, Fin.coe_cast, Fin.coe_castAdd]

lemma sylvesterVec_of_ge_of_gt (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h₁ : (i : ℕ) ≤ j) (h₂ : n < (j : ℕ) - i) : sylvesterVec P i j = 0 := by
  rw [sylvesterVec_apply, Fin.pad_of_ge]
  · rwa [Nat.succ_le, Fin.coe_sub_iff_le.mpr h₁, Fin.coe_cast, Fin.coe_castAdd]

lemma sylvesterVec_cases (P : R → Prop) (h0 : P 0) {f : Fin (n + 1) → R} (hf : ∀ i, P (f i)) :
    ∀ i (j : Fin (n + m)), P (sylvesterVec f i j) := by
  intro i j
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    rwa [sylvesterVec_of_lt _ _ _ h]
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) n
    case inl h₂ =>
      rw [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
      apply hf
    case inr h₂ =>
      rwa [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]

example : sylvesterVec (m := 3) ![1, 2, 3] 1 = ![0, 1, 2, 3, 0] := by decide
example : sylvesterVec (m := 3) ![1, 2, 3] 2 = ![0, 0, 1, 2, 3] := by decide

/-
def sylvesterBlock (P : Fin (n + 1) → R) : Matrix (Fin m) (Fin (n + m)) R :=
  Matrix.of (sylvesterVec P)
-/

end Zero

variable [CommRing R] [Nontrivial R]

@[simp] lemma vecRotate_smul (a : R) (P : Fin n → R) (i) :
    vecRotate (a • P) i = a • vecRotate P i := by
  ext j
  simp [vecRotate]

@[simp] lemma Fin.pad_smul {a : R} (P : Fin n → R) (x : R) :
    Fin.pad (m := m) (a • P) (a * x) = a • Fin.pad P x := by
  ext ⟨i, hi⟩
  simp only [Fin.pad, Pi.smul_apply]
  split_ifs <;> simp

@[simp] lemma Fin.pad_smul_zero {a : R} (P : Fin n → R) :
    Fin.pad (m := m) (a • P) 0 = a • Fin.pad P 0 := by
  rw [← Fin.pad_smul, mul_zero]

lemma sylvesterVec_smul (a : R) (P : Fin (n + 1) → R) :
    sylvesterVec (m := m) (n := n) (a • P) = a • sylvesterVec P := by
  ext i j
  simp only [sylvesterVec, Pi.smul_apply, Fin.pad_smul_zero, vecRotate_smul]

def sylvesterMatrixVec (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  (Matrix.of (Fin.addCases (fun i j ↦ sylvesterVec P i (j.cast (add_comm _ _))) (sylvesterVec Q)))ᵀ

@[simp]
lemma sylvesterMatrixVec_zero (P Q : Fin 1 → R) :
    sylvesterMatrixVec P Q = !![] := by ext i; apply finZeroElim i

@[simp]
lemma sylvesterMatrixVec_one (P Q : Fin 2 → R) :
    sylvesterMatrixVec P Q = !![P 0, Q 0; P 1, Q 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] lemma sylvesterMatrixVec_comp_cast (a b) (P : Fin (a + 1) → R) (Q : Fin (b + 1) → R)
    (h₁ : n + 1 = a + 1) (h₂ : m + 1 = b + 1) (h : b + a = m + n := by simp) :
    sylvesterMatrixVec (P ∘ Fin.cast h₁) (Q ∘ Fin.cast h₂) =
      Matrix.reindex (finCongr h) (finCongr h) (sylvesterMatrixVec P Q) := by
  have := Nat.succ_injective h₁
  subst this
  have := Nat.succ_injective h₂
  subst this
  simp

@[simp] lemma finAddFlip_symm {m n : ℕ} :
  (finAddFlip (m := m) (n := n)).symm = finAddFlip := by ext i; simp [finAddFlip]

def sylvesterMatrixVec_swap (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    sylvesterMatrixVec P Q =
      Matrix.reindex (finCongr (add_comm _ _)) finAddFlip (sylvesterMatrixVec Q P) := by
  ext i j
  rw [sylvesterMatrixVec, transpose_apply, of_apply, sylvesterMatrixVec, reindex_apply,
      submatrix_apply, transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left, finAddFlip_symm, finAddFlip_apply_castAdd, Fin.addCases_right,
        finCongr_symm, finCongr_apply]
  · rw [Fin.addCases_right, finAddFlip_symm, finAddFlip_apply_natAdd, Fin.addCases_left,
        finCongr_symm, finCongr_apply, Fin.cast_trans, Fin.cast_eq_self]

@[simp]
lemma sylvesterMatrixVec_smul (a : R) (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    sylvesterMatrixVec P (a • Q) = Matrix.of (fun (i j : Fin (m + n)) => (Fin.addCases (fun _ => 1) (fun _ => a) j) * sylvesterMatrixVec P Q i j) := by
  ext i j
  induction j using Fin.addCases <;>
    simp only [sylvesterMatrixVec, Matrix.transpose_apply, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Pi.natCast_def, one_mul, sylvesterVec_smul, Pi.smul_apply, smul_eq_mul]

@[simp]
lemma smul_sylvesterMatrixVec (a : R) (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    sylvesterMatrixVec (a • P) Q = Matrix.of (fun (i j : Fin (m + n)) => (Fin.addCases (fun _ => a) (fun _ => 1) j) * sylvesterMatrixVec P Q i j) := by
  ext i j
  induction j using Fin.addCases <;>
    simp only [sylvesterMatrixVec, Matrix.transpose_apply, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Pi.natCast_def, one_mul, sylvesterVec_smul, Pi.smul_apply, smul_eq_mul]

/-
#eval sylvesterMatrixVec ![1, 2, 3] ![4, 5, 6]
#eval have _ : Zero String := ⟨"0"⟩; sylvesterMatrixVec !["p4", "p3", "p2", "p1", "p0"] !["q3", "q2", "q1", "q0"]

/- The resultant is the determinant of this matrix. -/

def resultant_list (P Q : List R) := det (sylvester_matrix_list P Q)

example : sylvester_matrix_list (R := ℤ) [1, 1, 2, 3] [1, 2, 3] =
  sylvesterMatrixVec (R := ℤ) ![1, 1, 2, 3] ![1, 2, 3] := by decide

set_option maxRecDepth 10000 in
example :
  det (sylvester_matrix_list (R := ℤ) [1, 1, 2, 3] [1, 2, 3]) =
    det (sylvesterMatrixVec (R := ℤ) ![1, 1, 2, 3] ![1, 2, 3]) := by decide
-/

/-
def sylvester_matrix_poly (n m : ℕ) (P Q : Polynomial R) :=
  let LQ := List.ofFn (fun (i : Fin (m + 1)) ↦ Q.coeff i )
  let LP := List.ofFn (fun (i : Fin (n + 1)) ↦ P.coeff i )
  sylvester_matrix_list LP LQ
-/

def Polynomial.toVec (P : Polynomial R) : Fin (P.natDegree + 1) → R
  | ⟨i, _⟩ => P.coeff i

@[simp] lemma Polynomial.toVec_mk (P : Polynomial R) (i : ℕ) (hi) :
  P.toVec ⟨i, hi⟩ = P.coeff i := rfl

@[simp] lemma Polynomial.toVec_C (x : R) : toVec (C x) = fun _ => x := by
  ext ⟨i, hi⟩
  rw [natDegree_C, zero_add] at hi
  rcases hi with (_ | ⟨⟨⟩⟩)
  rw [toVec_mk, coeff_C_zero]

@[simp] lemma Polynomial.toVec_X : toVec (X : R[X]) = (![0, 1] ∘ Fin.cast (by rw [natDegree_X])) := by
  ext ⟨i, hi⟩
  rw [natDegree_X] at hi
  rcases hi with (_ | ⟨_ | ⟨⟨⟩⟩⟩)
  · simp
  · rw [toVec_mk, coeff_X_zero]
    simp

@[simp] lemma Polynomial.toVec_X_add_C (x : R) :
    toVec (X + C x) = ![x, 1] ∘ Fin.cast (by simp) := by
  ext ⟨i, hi⟩
  rw [natDegree_X_add_C, Nat.lt_succ] at hi
  rcases hi with (_ | ⟨(_ | ⟨⟩)⟩) <;>
    rw [toVec_mk] <;>
    simp

@[simp] lemma Polynomial.toVec_C_mul [NoZeroDivisors R] (x : R) (hx : x ≠ 0) (P : R[X]) :
    toVec (C x * P) = (x • toVec P) ∘ Fin.cast (by simp [natDegree_C_mul hx]) := by
  ext ⟨_, _⟩
  simp

/--
We define the sylvester matrix for polynomials P and Q and natural number n m as the
Sylvester matrix for the lists [P.coeff 0, P.coeff 1, ... , P.coeff n] and
[Q.coeff 0, Q.coeff 1, ... , Q.coeff m]
-/
def Polynomial.sylvesterMatrix (P Q : Polynomial R) :
    Matrix (Fin (P.natDegree + Q.natDegree)) (Fin (P.natDegree + Q.natDegree)) R :=
  sylvesterMatrixVec Q.toVec P.toVec -- (Fin.pad P.toVec 0) (Fin.pad Q.toVec 0)

lemma Polynomial.sylvesterMatrix_C (P : Polynomial R) (x : R) :
    P.sylvesterMatrix (C x) = diagonal (fun _ => x) := by
  ext i j
  rw [sylvesterMatrix, sylvesterMatrixVec, diagonal, of_apply, transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  swap
  · rw [natDegree_C] at j
    rcases j with ⟨_, ⟨⟩⟩
  rw [Fin.addCases_left]
  split_ifs with h
  · simp [h, sylvesterVec_of_ge_of_le]
  · obtain (h | h) := lt_or_gt_of_ne h
    · rw [sylvesterVec_of_lt _ _ _ h]
    · rw [sylvesterVec_of_ge_of_gt _ _ _ h.le]
      simpa using h

lemma Polynomial.C_sylvesterMatrix (x : R) (Q : Polynomial R) :
    (C x).sylvesterMatrix Q = diagonal (fun _ => x) := by
  ext i j
  rw [sylvesterMatrix, sylvesterMatrixVec, diagonal, of_apply, transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [natDegree_C] at j
    rcases j with ⟨_, ⟨⟩⟩
  rw [Fin.addCases_right]
  split_ifs with h
  · simp [h, sylvesterVec_of_ge_of_le]
  · obtain (h | h) := lt_or_gt_of_ne h <;>
      simp only [Fin.lt_def, Fin.coe_natAdd, natDegree_C, zero_add] at h
    · rw [sylvesterVec_of_lt _ _ _ h]
    · rw [sylvesterVec_of_ge_of_gt _ _ _ h.le]
      simpa using h

@[simp] lemma Fin.mk_zero' [NeZero m] (h : 0 < m) : (⟨0, h⟩ : Fin m) = 0 := rfl

@[simp] lemma Fin.natAdd_zero_right [NeZero m] [NeZero (n + m)] :
    Fin.natAdd n (0 : Fin m) = ⟨n, lt_add_of_pos_right _ (NeZero.pos _)⟩ := rfl

/-
lemma Polynomial.sylvesterMatrix_X (P : Polynomial R) :
    P.sylvesterMatrix X =
      Matrix.reindex (finCongr (by rw [natDegree_X])) (finCongr (by rw [natDegree_X])) (Matrix.of (vecCons P.toVec sorry)) := by
  have : NeZero (X : R[X]).natDegree := ⟨by simp⟩
  have : NeZero (P.natDegree + (X : R[X]).natDegree) := ⟨by simp⟩
  ext i j
  rw [sylvesterMatrix, toVec_X, sylvesterMatrixVec, transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun ⟨j, hj⟩ => ?_) j
  swap
  · rw [Fin.addCases_right]
    rw [natDegree_X] at hj
    rcases hj with (⟨⟩|⟨⟨⟩⟩)
    have : Fin.natAdd P.natDegree (0 : Fin (X : R[X]).natDegree) =
      finCongr (by simp) (Fin.last P.natDegree) := by ext; rfl
    rw [Fin.mk_zero', sylvesterVec_zero, this, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.of_apply]
    sorry
  sorry
-/

-- #eval Polynomial.sylvesterMatrix (Polynomial.ofList [(1 : ℤ), 2, 3]) (Polynomial.ofList [4, 5, 6])

/- We define the resultant as the determinant of the previous matrix. -/
def Polynomial.resultant (P Q : Polynomial R) := det (Polynomial.sylvesterMatrix P Q)

lemma Matrix.det_submatrix {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    (e f : m ≃ n) (M : Matrix n n R) :
    (M.submatrix e f).det = Equiv.Perm.sign (e.symm.trans f) * M.det := by
  rw [← det_permute', ← det_submatrix_equiv_self e, submatrix_submatrix]
  congr
  ext i j
  simp

@[simp] lemma finCongr_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) :
    (finCongr hab).trans (finCongr hbc) = finCongr (hab.trans hbc) := rfl

/-- Evaluate the resultant in terms of the Sylvester matrix.

There is an extra cast which helps fight dependent type theory hell if the the degree of `P` and `Q`
are known constants.
-/
lemma resultant_eq_det_sylvesterMatrixVec_cast (P Q : Polynomial R)
    (hP : P.natDegree = m) (hQ : Q.natDegree = n) :
    P.resultant Q =
      Matrix.det (sylvesterMatrixVec
        (Q.toVec ∘ Fin.cast (congr_arg Nat.succ hQ.symm))
        (P.toVec ∘ Fin.cast (congr_arg Nat.succ hP.symm))) := by
  rw [resultant, sylvesterMatrix, sylvesterMatrixVec_comp_cast _ _ _ _ _ _ (by rw [hP, hQ])]
  simp [det_submatrix]

/-
lemma lists_length_add (n m : ℕ) (P Q : Polynomial R):
  ((List.ofFn (fun (i : Fin (m + 1)) ↦ Q.coeff i )).length - 1)  + ((List.ofFn (fun (i : Fin (n + 1)) ↦ P.coeff i )).length - 1) = m + n := by 
    simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, List.length_cons, List.length_ofFn, ge_iff_le,


def sylvester_matrix_poly' (n m : ℕ) (P Q : Polynomial R) : Matrix (Fin (m + n)) (Fin (m + n)) R := 
  Matrix.reindex (finCongr (lists_length_add R n m P Q)) (finCongr (lists_length_add R n m P Q)) (sylvester_matrix_poly R n m P Q)

/- If P.natDegree < n  and Q.natDegree < m then the resultant in size (n, m) is zero.  -/

lemma resultant_zero_of_degree_gt (n m : ℕ) (P Q : Polynomial R) (h1 : P.natDegree < n) (h2 : Q.natDegree < m) : 
    resultant_poly R n m P Q = 0 := by
  sorry
-/

/-- R[X]_n is notation for the submodule of polynomials of degree strictly less than n. -/
local notation:9000 R "[x]_" n =>  Polynomial.degreeLT R n

section degreeLT

variable (R)

/-- Basis for R[X]_n given by the `X^i` with `i < n`. -/
noncomputable def Polynomial.degreeLT.basis (n : ℕ) : Basis (Fin n) R R[x]_n :=
  Basis.ofEquivFun (Polynomial.degreeLTEquiv R n)

lemma degreeLT_X_pow_mem {n : ℕ} (i : Fin n) : X ^ i.val ∈ R[x]_n := by
  simp only [Polynomial.mem_degreeLT, Polynomial.degree_X_pow, Nat.cast_lt, Fin.is_lt]

lemma Polynomial.degreeLT.basis_apply (n : ℕ) (i : Fin n) :
    Polynomial.degreeLT.basis R n i = ⟨X ^ i.val, degreeLT_X_pow_mem R i⟩ := by
  ext
  simp only [Polynomial.degreeLT.basis, degreeLTEquiv, Basis.coe_ofEquivFun,
    LinearEquiv.coe_symm_mk]
  rw [Finset.sum_eq_single i (by aesop) (by aesop),
      Function.update_same, Polynomial.monomial_one_right_eq_X_pow]

@[simp] lemma Polynomial.degreeLT.basis_val (n : ℕ) (i : Fin n) :
    (Polynomial.degreeLT.basis R n i : R[X]) = X ^ i.val :=
  congr_arg _ (Polynomial.degreeLT.basis_apply R n i)

@[simp] lemma Polynomial.degreeLT.basis_repr {n} (P : R[x]_n) (i : Fin n) :
    (degreeLT.basis R n).repr P i = (P : R[X]).coeff i :=
  Basis.ofEquivFun_repr_apply _ _ _

instance : Module.Finite R R[x]_n :=
  Module.Finite.of_basis (degreeLT.basis _ _)

/-
noncomputable def basis_polyLT_prod' (m n : ℕ) : Basis ((Fin m) ⊕ (Fin n)) R ((R[x]_m) × (R[x]_n)) :=
  Basis.prod (Polynomial.degreeLT.basis R m) (Polynomial.degreeLT.basis R n)
-/

/-- Basis for R[X]_m × R[X]_n. -/
noncomputable def Polynomial.degreeLT.basis_prod (m n : ℕ) : Basis (Fin (m + n)) R ((R[x]_m) × (R[x]_n)) :=
  ((Polynomial.degreeLT.basis R m).prod (Polynomial.degreeLT.basis R n)).reindex finSumFinEquiv

@[simp] lemma Polynomial.degreeLT.basis_prod_castAdd (m n : ℕ) (i : Fin m) :
    basis_prod R m n (Fin.castAdd n i) = (⟨X ^ i.val, degreeLT_X_pow_mem R i⟩, 0) := by
  rw [basis_prod, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd]
  ext
  · rw [Basis.prod_apply_inl_fst, basis_apply]
  · rw [Basis.prod_apply_inl_snd]

@[simp] lemma Polynomial.degreeLT.basis_prod_natAdd (m n : ℕ) (i : Fin n) :
    basis_prod R m n (Fin.natAdd m i) = (0, ⟨X ^ i.val, degreeLT_X_pow_mem R i⟩) := by
  rw [basis_prod, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
  ext
  · rw [Basis.prod_apply_inr_fst]
  · rw [Basis.prod_apply_inr_snd, basis_apply]

noncomputable def Polynomial.degreeLT.addLinearEquiv {n m : ℕ} :
    (R[x]_(n + m)) ≃ₗ[R] (R[x]_n) × (R[x]_m) :=
  Basis.equiv (Polynomial.degreeLT.basis _ _) (Polynomial.degreeLT.basis_prod _ _ _) (Equiv.refl _)

end degreeLT

@[aesop unsafe 50%]
theorem Polynomial.degree_add_lt_of_degree_lt {p q : R[X]} {n : ℕ}
    (hp : degree p < n) (hq : degree q < n) :
    degree (p + q) < n :=
  (degree_add_le p q).trans_lt <| max_lt hp hq

@[aesop unsafe 50%]
theorem Polynomial.degree_mul_lt_of_lt_left {p q : R[X]} {a : WithBot ℕ} {b : ℕ}
    (hp : degree p < a) (hq : degree q ≤ b) :
    degree (p * q) < a + b :=
  (degree_mul_le _ _).trans_lt (WithBot.add_lt_add_of_lt_of_le WithBot.coe_ne_bot hp hq)

@[aesop unsafe 50%]
theorem Polynomial.degree_mul_lt_of_lt_right {p q : R[X]} {a : ℕ} {b : WithBot ℕ}
    (hp : degree p ≤ a) (hq : degree q < b) :
    degree (p * q) < a + b :=
  (degree_mul_le _ _).trans_lt (WithBot.add_lt_add_of_le_of_lt WithBot.coe_ne_bot hp hq)

lemma Polynomial.mul_left_mem_degreeLT {n} (p q : R[X]) (hp : degree p ≤ m) (hq : q ∈ R[x]_n) :
    p * q ∈ R[x]_(m + n) := by
  rw [Polynomial.mem_degreeLT] at *
  exact Polynomial.degree_mul_lt_of_lt_right hp hq

lemma Polynomial.mul_left_mem_degreeLT' {n} (p q : R[X]) (hp : degree p ≤ m) (hq : q ∈ R[x]_n) :
    p * q ∈ R[x]_(n + m) := by
  rw [add_comm]
  exact Polynomial.mul_left_mem_degreeLT _ _ ‹_› ‹_›

lemma Polynomial.mul_right_mem_degreeLT {m} (p q : R[X]) (hp : p ∈ R[x]_m) (hq : degree q ≤ n) :
    p * q ∈ R[x]_(m + n) := by
  rw [Polynomial.mem_degreeLT] at *
  exact Polynomial.degree_mul_lt_of_lt_left hp hq

lemma Polynomial.mul_right_mem_degreeLT' {m} (p q : R[X]) (hp : p ∈ R[x]_m) (hq : degree q ≤ n) :
    p * q ∈ R[x]_(n + m) := by
  rw [add_comm]
  exact Polynomial.mul_right_mem_degreeLT _ _ ‹_› ‹_›

/-- If `P.degree ≤ n` and `Q.degree ≤ m`, and `(a, b) ∈ R[X]_m × R[X]_n`, then `P * a + Q * b`
is in `R[X]_(m + n)`.  -/
lemma sylvester_map_mem_aux {n m : ℕ} {P Q : Polynomial R}
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (a : R[x]_m) (b : R[x]_n) :
    P * a.val + Q * b.val ∈ R[x]_(m + n) := by
  apply add_mem
  · exact mul_left_mem_degreeLT' _ _ hP a.prop
  · exact mul_left_mem_degreeLT _ _ hQ b.prop

/-- We define the linear map R[X]_m × R[X]_n → R[X]_{m + n}
    with (a, b) ↦ P * a + Q * b.  -/
@[simps]
noncomputable def sylvesterMap {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) :
    ((R[x]_m) × (R[x]_n)) →ₗ[R] (R[x]_(m + n)) where
  toFun := fun (a, b) ↦ ⟨P * a.val + Q * b.val, sylvester_map_mem_aux hP hQ a b⟩
  map_add' x y := by
    ext
    push_cast
    congr 1
    ring
  map_smul' r a := by
    ext
    simp

@[simp] lemma sylvesterMap_C_mul {n m : ℕ} (a : R) (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (hQ' : (C a * Q).degree ≤ m := by simp [hQ]) :
    sylvesterMap P (C a * Q) hP hQ' =
      (sylvesterMap P Q hP hQ) ∘ₗ (LinearMap.prod (LinearMap.fst _ _ _) (a • LinearMap.snd _ _ _)) := by
  ext ⟨x, y⟩
  · simp [sylvesterMap]
  · simp [sylvesterMap, mul_assoc]

@[simp] lemma sylvesterMap_X_pow_zero {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (i : Fin m) :
    sylvesterMap P Q hP hQ (⟨X ^ (i : ℕ), degreeLT_X_pow_mem R i⟩, 0) =
      ⟨P * X ^ (i : ℕ), mul_left_mem_degreeLT' _ _ hP (degreeLT_X_pow_mem R i)⟩ := by
  simp [sylvesterMap]

@[simp] lemma sylvesterMap_zero_X_pow {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (i : Fin n) :
    sylvesterMap P Q hP hQ (0, ⟨X ^ (i : ℕ), degreeLT_X_pow_mem R i⟩) =
      ⟨Q * X ^ (i : ℕ), mul_left_mem_degreeLT _ _ hQ (degreeLT_X_pow_mem R i)⟩ := by
  simp [sylvesterMap]

/-- The Sylvester matrix is equal to the Sylvester map as a matrix in basis (1, .., X^(m-1); 1, ..., X^(n-1)) and (1, ..., X^(m+n-1)). 
-/
lemma sylvesterMap_toMatrix (P Q : Polynomial R) :
    LinearMap.toMatrix
      (Polynomial.degreeLT.basis_prod R P.natDegree Q.natDegree)
      (Polynomial.degreeLT.basis R (P.natDegree + Q.natDegree))
      (sylvesterMap Q P degree_le_natDegree degree_le_natDegree) =
     Polynomial.sylvesterMatrix P Q := by
  ext i j
  rw [sylvesterMatrix, LinearMap.toMatrix_apply, sylvesterMatrixVec, transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left, Polynomial.degreeLT.basis_prod_castAdd, sylvesterMap_X_pow_zero,
        degreeLT.basis_repr, Subtype.coe_mk, coeff_mul_X_pow']
    split_ifs with h₁
    · by_cases h₂ : (i : ℕ) - j ≤ Q.natDegree
      · rw [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂, toVec_mk, Fin.coe_cast]
      · rw [not_le] at h₂
        rw [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂, coeff_eq_zero_of_natDegree_lt]
        assumption
    · rw [sylvesterVec_of_lt]
      simpa using h₁
  · rw [Fin.addCases_right, Polynomial.degreeLT.basis_prod_natAdd, sylvesterMap_zero_X_pow,
        degreeLT.basis_repr, Subtype.coe_mk, coeff_mul_X_pow']
    split_ifs with h₁
    · by_cases h₂ : (i : ℕ) - j ≤ P.natDegree
      · rw [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂, toVec_mk]
      · rw [not_le] at h₂
        rw [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂, coeff_eq_zero_of_natDegree_lt]
        assumption
    · rw [sylvesterVec_of_lt]
      simpa using h₁

@[simp]
lemma LinearMap.det_toMatrix_eq {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (c : Basis ι R N) :
    det (toMatrix b c f) = LinearMap.det (f ∘ₗ (c.equiv b (Equiv.refl _)).toLinearMap) := by
  rw [← LinearMap.det_toMatrix c, toMatrix_comp _ b, toMatrix_basis_equiv, mul_one]

lemma resultant_eq_det_sylvesterMap (P Q : Polynomial R) :
    P.resultant Q =
      LinearMap.det ((sylvesterMap Q P degree_le_natDegree degree_le_natDegree) ∘ₗ
        (Polynomial.degreeLT.addLinearEquiv R).toLinearMap) := by
  rw [resultant, ← sylvesterMap_toMatrix, degreeLT.addLinearEquiv,
      LinearMap.det_toMatrix_eq]

variable {K : Type*} [Field K]

lemma LinearMap.det_eq_zero_iff_bot_lt_ker {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M]
    (f : M →ₗ[K] M) : LinearMap.det f = 0 ↔ ⊥ < ker f := by
  refine ⟨LinearMap.bot_lt_ker_of_det_eq_zero, fun hf => ?_⟩
  rw [bot_lt_iff_ne_bot, ne_eq, ← isUnit_iff_ker_eq_bot] at hf
  contrapose! hf
  rw [← isUnit_iff_ne_zero, ← LinearMap.det_toMatrix (Module.Free.chooseBasis K M)] at hf
  let e := LinearEquiv.ofIsUnitDet hf
  refine ⟨⟨e, e.symm, ?_, ?_⟩, ?_⟩
    <;>
  · ext
    simp
    try { simp [e] }

lemma LinearMap.det_eq_zero_iff_range_lt_top {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M]
    (f : M →ₗ[K] M) : LinearMap.det f = 0 ↔ range f < ⊤ := by
  rw [LinearMap.det_eq_zero_iff_bot_lt_ker, lt_top_iff_ne_top, ne_eq, ← isUnit_iff_range_eq_top,
      bot_lt_iff_ne_bot, ne_eq, ← isUnit_iff_ker_eq_bot]

lemma resultant_eq_zero_iff {P Q : K[X]} :
    P.resultant Q = 0 ↔
      ∃ a : K[x]_Q.natDegree, ∃ b : K[x]_P.natDegree, (a ≠ 0 ∨ b ≠ 0) ∧ P * a + Q * b = 0 := by
  simp only [resultant_eq_det_sylvesterMap, LinearMap.det_eq_zero_iff_bot_lt_ker,
      SetLike.lt_iff_le_and_exists, bot_le, LinearMap.mem_ker, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Submodule.mem_bot,
      AddSubmonoid.mk_eq_zero, exists_and_right, true_and, ne_eq]
  constructor
  · rintro ⟨ab, hfab, hab0⟩
    have hab0 := mt (degreeLT.addLinearEquiv K).map_eq_zero_iff.mp hab0
    set ab := degreeLT.addLinearEquiv _ ab with ab_eq
    obtain ⟨a, b⟩ := ab
    refine ⟨b, a, ?_, ?_⟩
    · simpa [-not_and, Classical.not_and_iff_or_not_not, or_comm] using hab0
    · simpa [sylvesterMap, add_comm] using hfab
  · rintro ⟨a, b, hab0, hfab⟩
    refine ⟨(degreeLT.addLinearEquiv _).symm (b, a), ?_, ?_⟩
    · simpa [sylvesterMap, add_comm] using hfab
    · simpa [-not_and, Classical.not_and_iff_or_not_not, or_comm] using hab0

lemma resultant_ne_zero_iff {P Q : K[X]} :
    P.resultant Q ≠ 0 ↔
      ∀ a : K[x]_Q.natDegree, ∀ b : K[x]_P.natDegree, P * a + Q * b = 0 → a = 0 ∧ b = 0 := by
  simpa [-Subtype.exists, -not_and, not_and']
    using not_iff_not.mpr (resultant_eq_zero_iff (P := P) (Q := Q))

lemma Polynomial.IsRoot.X_sub_C_dvd {P : R[X]} {x : R} (hP : IsRoot P x) :
    X - C x ∣ P := by simpa [hP.eq_zero] using X_sub_C_dvd_sub_C_eval (a := x) (p := P)

@[simp] lemma finAddFlip_zero_zero : finAddFlip (m := 0) (n := 0) = Equiv.refl _ := by
  ext i
  apply finZeroElim i

lemma sign_finAddFlip :
    Equiv.Perm.sign ((finCongr (add_comm m n)).trans finAddFlip) = (-1) ^ (n * m) := by
  sorry

@[simp] lemma resultant_C (P : Polynomial R) (x : R) :
    P.resultant (C x) = x ^ P.natDegree := by
  rw [resultant, sylvesterMatrix_C, det_diagonal, Fin.prod_const, natDegree_C, add_zero]

@[simp] lemma C_resultant (Q : Polynomial R) (x : R) :
    (C x).resultant Q = x ^ Q.natDegree := by
  rw [resultant, C_sylvesterMatrix, det_diagonal, Fin.prod_const, natDegree_C, zero_add]

@[simp] lemma resultant_zero (P : Polynomial R) (hP : P.natDegree ≠ 0) :
    P.resultant 0 = 0 := by
  rw [← map_zero C, resultant_C, zero_pow hP]

@[simp] lemma zero_resultant (Q : Polynomial R) (hQ : Q.natDegree ≠ 0) :
    resultant 0 Q = 0 := by
  rw [← map_zero C, C_resultant, zero_pow hQ]

@[simp] lemma zero_resultant_zero :
    (0 : R[X]).resultant 0 = 1 := by
  rw [← map_zero C, resultant_C, natDegree_C, pow_zero]

@[simp] lemma resultant_one (P : Polynomial R) :
    P.resultant 1 = 1 := by
  rw [← C.map_one, resultant_C, one_pow]

@[simp] lemma one_resultant (Q : Polynomial R) :
    resultant 1 Q = 1 := by
  rw [← C.map_one, C_resultant, one_pow]

@[simp] lemma X_add_C_resultant_X_add_C (x y : R) :
    (X + C x).resultant (X + C y) = y - x := by
  rw [resultant, sylvesterMatrix, toVec_X_add_C, toVec_X_add_C, sylvesterMatrixVec_comp_cast _ _,
      Matrix.det_reindex_self, sylvesterMatrixVec_one]
  simp

/-- Note the condition `hPQ`: if `P` and `Q` are both constant polynomials,
their resultant is equal to `1` but we would have to write `1 = P * 0 + Q * 0` because of the
degree restrictions. -/
lemma resultant_eq_comb (P Q : K[X]) (hPQ : 0 < P.natDegree + Q.natDegree):
    ∃ a : K[x]_Q.natDegree, ∃ b : K[x]_P.natDegree,
      P * a + Q * b = C (Polynomial.resultant P Q) := by
  by_cases h0 : P.resultant Q = 0
  · obtain ⟨a, b, _hab0, hpq⟩ := resultant_eq_zero_iff.mp h0
    exact ⟨a, b, by simp [h0, hpq]⟩
  have : Function.Surjective (sylvesterMap Q P degree_le_natDegree degree_le_natDegree) := by
    apply Function.Surjective.of_comp
    rwa [resultant_eq_det_sylvesterMap, LinearMap.det_eq_zero_iff_range_lt_top, lt_top_iff_ne_top,
      ne_eq, not_not, LinearMap.range_eq_top, LinearMap.coe_comp] at h0
  obtain ⟨⟨a, b⟩, hab⟩ := this ⟨C (P.resultant Q),
          mem_degreeLT.mpr (by rw [degree_C h0]; exact_mod_cast hPQ)⟩
  refine ⟨b, a, ?_⟩
  simpa [Subtype.ext_iff, add_comm] using hab

/-
@[simp] lemma resultant_X (P : Polynomial R) (x : R) :
    P.resultant X = _ := by
  rw [resultant, sylvesterMatrix_X]
-/

lemma resultant_swap (P Q : Polynomial R) :
    P.resultant Q = (-1) ^ (P.natDegree * Q.natDegree) * Q.resultant P := by
  rw [resultant, sylvesterMatrix, resultant, sylvesterMatrix, sylvesterMatrixVec_swap,
      reindex_apply, det_submatrix]
  simp [sign_finAddFlip]

@[simp] lemma Fin.cast_rfl : Fin.cast (rfl : m = m) = id := rfl

@[simp] lemma finCongr_trans_finCongr {m n o} (h₁ : m = n) (h₂ : n = o) :
  (finCongr h₁).trans (finCongr h₂) = finCongr (h₁.trans h₂) := rfl

lemma C_mul_resultant [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hQ : Q.natDegree ≠ 0) :
    (C a * P).resultant Q = a ^ Q.natDegree * P.resultant Q := by
  by_cases ha : a = 0
  · rw [ha, map_zero, zero_mul, zero_resultant _ hQ, zero_pow hQ, zero_mul]
  · rw [resultant, sylvesterMatrix, toVec_C_mul _ ha, Pi.smul_comp, sylvesterMatrixVec_smul,
        det_mul_row, resultant, sylvesterMatrix]
    congr 1
    · simp only [Fin.prod_univ_add, Fin.addCases_left, Finset.prod_const_one, one_mul,
          Fin.addCases_right, Fin.prod_const]
    · have : P.natDegree = (C a * P).natDegree := by rw [natDegree_C_mul ha]
      rw [← Function.comp_id Q.toVec, ← Fin.cast_rfl,
          sylvesterMatrixVec_comp_cast _ _ _ _ _ _ (by rw [this]),
          reindex_apply, det_submatrix, Fin.cast_rfl, Function.comp_id]
      simp

lemma C_mul_resultant' [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hQ : Q.natDegree ≠ 0) (h : Q.natDegree = n) :
    (C a * P).resultant Q = a ^ n * P.resultant Q := by
  rw [C_mul_resultant, h]
  · assumption

lemma resultant_C_mul [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hP : P.natDegree ≠ 0) :
    P.resultant (C a * Q) = a ^ P.natDegree * P.resultant Q := by
  by_cases ha : a = 0
  · simp [ha, resultant_zero, hP]
  rw [resultant_swap, C_mul_resultant _ _ _ hP, resultant_swap P Q, natDegree_C_mul ha,
      mul_left_comm]

lemma resultant_C_mul' [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hP : P.natDegree ≠ 0) (h : m = P.natDegree) :
    P.resultant (C a * Q) = a ^ m * P.resultant Q := by
  rw [resultant_C_mul, h]
  · assumption

/-
lemma X_mul_resultant [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hP : P.natDegree ≠ 0) (hQ : Q.natDegree ≠ 0) :
    (X * P).resultant Q = P.resultant Q := by
  by_cases ha : a = 0
  · rw [ha, map_zero, zero_mul, zero_resultant _ hQ, zero_pow hQ, zero_mul]
  · rw [resultant, sylvesterMatrix, toVec_C_mul _ ha, Pi.smul_comp, sylvesterMatrixVec_smul,
        det_mul_row, resultant, sylvesterMatrix]
    congr 1
    · simp only [Fin.prod_univ_add, Fin.addCases_left, Finset.prod_const_one, one_mul,
          Fin.addCases_right, Fin.prod_const]
    · sorry
-/

lemma resultant_eq_zero_of_root {P Q : K[X]} {x : K} (hP0 : P ≠ 0)
    (hP : IsRoot P x) (hQ : IsRoot Q x) :
    P.resultant Q = 0 := by
  obtain ⟨a, rfl⟩ := hP.X_sub_C_dvd
  obtain ⟨b, rfl⟩ := hQ.X_sub_C_dvd
  have ha : a ≠ 0 := right_ne_zero_of_mul hP0
  by_cases hb : b = 0
  · rw [hb, mul_zero, resultant_zero]
    · rw [natDegree_mul (monic_X_sub_C _).ne_zero ha, natDegree_X_sub_C,
          add_comm]
      exact Nat.succ_ne_zero a.natDegree
  refine resultant_eq_zero_iff.mpr
    ⟨⟨b, mem_degreeLT.mpr (degree_le_natDegree.trans_lt ?_)⟩,
     ⟨-a, mem_degreeLT.mpr (degree_le_natDegree.trans_lt ?_)⟩,
     by simp [hb], ?_⟩
  · rw [natDegree_mul (monic_X_sub_C _).ne_zero hb, natDegree_X_sub_C, add_comm, Nat.cast_lt]
    · exact Nat.lt_succ_self _
  · rw [natDegree_mul (monic_X_sub_C _).ne_zero ha, natDegree_X_sub_C, natDegree_neg, add_comm,
        Nat.cast_lt]
    · exact Nat.lt_succ_self _
  · simp [mul_right_comm]

/-
lemma mul_resultant (P P' Q : Polynomial R) :
    (P * P').resultant Q = P.resultant Q * P'.resultant Q := by
  rw [resultant, sylvesterMatrix, resultant, sylvesterMatrix, resultant, sylvesterMatrix, det_mul]
-/

/-- A polynomial function in `ι` arguments is one that can be given as evaluating a MvPolynomial. -/
def IsPolynomial {ι R : Type*} [CommSemiring R] (f : (ι → R) → R) : Prop :=
  ∃ p : MvPolynomial ι R, ∀ x, f x = MvPolynomial.eval x p

lemma IsPolynomial.const {ι : Type*} (x : R) :
    IsPolynomial (fun (_ : ι → R) => x) :=
  ⟨MvPolynomial.C x, fun _ => (MvPolynomial.eval_C _).symm⟩

lemma IsPolynomial.apply_const {ι : Type*} (i : ι) :
    IsPolynomial (fun (x : ι → R) => x i) :=
  ⟨MvPolynomial.X i, fun _ => (MvPolynomial.eval_X _).symm⟩

lemma IsPolynomial.comp {ι κ : Type*} {f : (ι → R) → R} (s : ι → κ):
    IsPolynomial f → IsPolynomial (fun x => f (x ∘ s)) := by
  rintro ⟨f, f_eq⟩
  exact ⟨MvPolynomial.rename s f, by simp [f_eq, MvPolynomial.eval_rename]⟩

lemma IsPolynomial.add {ι : Type*} {f g : (ι → R) → R} :
    IsPolynomial f → IsPolynomial g → IsPolynomial (fun (x : ι → R) => f x + g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f + g, by simp [f_eq, g_eq]⟩

@[to_additive existing]
lemma IsPolynomial.mul {ι : Type*} {f g : (ι → R) → R} :
    IsPolynomial f → IsPolynomial g → IsPolynomial (fun (x : ι → R) => f x * g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f * g, by simp [f_eq, g_eq]⟩

lemma IsPolynomial.sum {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsPolynomial (f i)) (s : Finset m) :
    IsPolynomial (fun x => ∑ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.sum_empty]
    apply IsPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

@[to_additive existing]
lemma IsPolynomial.prod {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsPolynomial (f i)) (s : Finset m) :
    IsPolynomial (fun x => ∏ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.prod_empty]
    apply IsPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

/-- The determinant as a multivariate polynomial in the matrix entries. -/
noncomputable def MvPolynomial.det {ι : Type*} [DecidableEq ι] [Fintype ι] :
    MvPolynomial (ι × ι) R :=
  ∑ σ : Equiv.Perm ι, C (Equiv.Perm.sign σ : R) * ∏ (i : ι), X (σ i, i)

lemma MvPolynomial.eval_det {ι : Type*} [DecidableEq ι] [Fintype ι] (M : Matrix ι ι R) :
    MvPolynomial.eval (fun ij => M ij.1 ij.2) MvPolynomial.det = M.det := by
  simp [MvPolynomial.det, Matrix.det_apply, Units.smul_def]

@[simp]
lemma MvPolynomial.eval_det' {ι : Type*} [DecidableEq ι] [Fintype ι] (M : ι × ι → R) :
    MvPolynomial.eval M MvPolynomial.det = (Matrix.of fun i j => M (i, j)).det := by
  simp [MvPolynomial.det, Matrix.det_apply, Units.smul_def]

lemma IsPolynomial.det {m ι : Type*} [DecidableEq m] [Fintype m]
    (f : m → m → (ι → R) → R) (h : ∀ i j, IsPolynomial (f i j)) :
    IsPolynomial (fun x => Matrix.det (Matrix.of (fun i j => f i j x))) := by
  simp only [det_apply, of_apply, Units.smul_def, zsmul_eq_mul]
  apply IsPolynomial.sum
  intro σ
  exact (IsPolynomial.const (Equiv.Perm.sign σ : R)).mul (.prod _ (fun _ => h _ _) _)

/-- A symmetric polynomial function in `ι` arguments is one that can be given as evaluating a
symmetric MvPolynomial. -/
def IsSymmPolynomial {ι R : Type*} [CommSemiring R] (f : (ι → R) → R) : Prop :=
  ∃ p : MvPolynomial ι R, ∀ x, f x = MvPolynomial.eval x p ∧ p.IsSymmetric

lemma IsSymmPolynomial.toIsPolynomial {ι R : Type*} [CommSemiring R] {f : (ι → R) → R} :
    IsSymmPolynomial f → IsPolynomial f := by
  rintro ⟨P, hP⟩
  exact ⟨P, fun x => (hP x).1⟩

lemma IsSymmPolynomial.const {ι : Type*} (x : R) :
    IsSymmPolynomial (fun (_ : ι → R) => x) :=
  ⟨MvPolynomial.C x, fun _ => ⟨(MvPolynomial.eval_C _).symm, MvPolynomial.IsSymmetric.C _⟩⟩

lemma IsSymmPolynomial.eval_esymm {ι : Type*} [Fintype ι] :
    IsSymmPolynomial (fun (x : ι → R) => MvPolynomial.eval x (MvPolynomial.esymm _ _ n)) :=
  ⟨MvPolynomial.esymm _ _ n, fun _ => ⟨rfl, MvPolynomial.esymm_isSymmetric _ _ _⟩⟩

lemma IsSymmPolynomial.esymm {ι : Type*} [Fintype ι] :
    ∀ i, IsSymmPolynomial (fun (x : ι → R) => (Multiset.map x Finset.univ.val).esymm i) := by
  intro i
  refine ⟨MvPolynomial.esymm _ _ i, fun _ => ⟨?_, MvPolynomial.esymm_isSymmetric _ _ _⟩⟩
  rw [← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe,
      MvPolynomial.aeval_esymm_eq_multiset_esymm]

lemma IsSymmPolynomial.add {ι : Type*} {f g : (ι → R) → R} :
    IsSymmPolynomial f → IsSymmPolynomial g → IsSymmPolynomial (fun (x : ι → R) => f x + g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f + g, fun i => ⟨by simp [f_eq, g_eq], MvPolynomial.IsSymmetric.add (f_eq i).2 (g_eq i).2⟩⟩

@[to_additive existing]
lemma IsSymmPolynomial.mul {ι : Type*} {f g : (ι → R) → R} :
    IsSymmPolynomial f → IsSymmPolynomial g → IsSymmPolynomial (fun (x : ι → R) => f x * g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f * g, fun i => ⟨by simp [f_eq, g_eq], MvPolynomial.IsSymmetric.mul (f_eq i).2 (g_eq i).2⟩⟩

lemma IsSymmPolynomial.sum {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsSymmPolynomial (f i)) (s : Finset m) :
    IsSymmPolynomial (fun x => ∑ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.sum_empty]
    apply IsSymmPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

@[to_additive existing]
lemma IsSymmPolynomial.prod {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsSymmPolynomial (f i)) (s : Finset m) :
    IsSymmPolynomial (fun x => ∏ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.prod_empty]
    apply IsSymmPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

lemma IsSymmPolynomial.det {m ι : Type*} [DecidableEq m] [Fintype m]
    (f : m → m → (ι → R) → R) (h : ∀ i j, IsSymmPolynomial (f i j)) :
    IsSymmPolynomial (fun x => Matrix.det (Matrix.of (fun i j => f i j x))) := by
  simp only [det_apply, of_apply, Units.smul_def, zsmul_eq_mul]
  apply IsSymmPolynomial.sum
  intro σ
  exact (IsSymmPolynomial.const (Equiv.Perm.sign σ : R)).mul (.prod _ (fun _ => h _ _) _)

/-- If the coefficients of `f` is given by polynomial functions, so is its Sylvester matrix. -/
theorem IsPolynomial.sylvesterVec {ι : Type*} {m n : ℕ} {f : (ι → R) → (Fin (m + 1) → R)}
    (hf : ∀ i, IsPolynomial (fun x => (f x) i)) :
    ∀ i (j : Fin (m + n)), IsPolynomial (fun x => sylvesterVec (f x) i j) := by
  intro i j
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    simp only [sylvesterVec_of_lt _ _ _ h]
    apply IsPolynomial.const
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) m
    case inl h₂ =>
      simp only [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
      apply hf
    case inr h₂ =>
      simp only [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]
      apply IsPolynomial.const

/-- If the coefficients of `f` is given by polynomial functions, so is its Sylvester matrix. -/
theorem IsSymmPolynomial.sylvesterVec {ι : Type*} {m n : ℕ} {f : (ι → R) → (Fin (m + 1) → R)}
    (hf : ∀ i, IsSymmPolynomial (fun x => (f x) i)) :
    ∀ i (j : Fin (m + n)), IsSymmPolynomial (fun x => sylvesterVec (f x) i j) := by
  intro i j
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    simp only [sylvesterVec_of_lt _ _ _ h]
    apply IsSymmPolynomial.const
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) m
    case inl h₂ =>
      simp only [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
      apply hf
    case inr h₂ =>
      simp only [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]
      apply IsSymmPolynomial.const

/-- If the coefficients of `f` and `g` are given by polynomial functions, so is their resultant.

Note that we have to be a bit tricky here: a priori the degree of `f x` and `g x` can change
as a function of `x`, so suddenly we could get a completely different Sylvester matrix.
Thus we need to assume the degree remains constant in terms of `x`.
-/
theorem IsSymmPolynomial.resultant {ι : Type*} {m n : ℕ} {f g : (ι → R) → R[X]}
    (hdegf : ∀ x, (f x).natDegree = m) (hdegg : ∀ x, (g x).natDegree = n)
    (hf : ∀ i, IsSymmPolynomial (fun x => coeff (f x) i)) (hg : ∀ i, IsSymmPolynomial (fun x => coeff (g x) i)) :
    IsSymmPolynomial (fun x => (f x).resultant (g x)) := by
  conv =>
    congr
    · ext x
      rw [resultant_eq_det_sylvesterMatrixVec_cast _ _ (hdegf x) (hdegg x),
          sylvesterMatrixVec]
      · skip
  simp only [det_transpose]
  refine IsSymmPolynomial.det _ (fun i j => Fin.addCases (fun i => ?_) (fun i => ?_) i)
  · simp only [Fin.addCases_left]
    apply IsSymmPolynomial.sylvesterVec
    intro i
    apply hg
  · simp only [Fin.addCases_right]
    apply IsSymmPolynomial.sylvesterVec
    intro i
    apply hf

@[simp] lemma Polynomial.leadingCoeff_prod_X_sub_C {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i in s, (X - C (t i))).leadingCoeff = 1 :=
  (leadingCoeff_prod' _ _ (by simp)).trans (by simp)

@[simp] lemma Polynomial.leadingCoeff_C_mul_prod_X_sub_C
    {σ : Type*} (t : σ → R) (s : Finset σ) (x : R) :
    (C x * ∏ i in s, (X - C (t i))).leadingCoeff = x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [leadingCoeff_mul', leadingCoeff_prod'] <;>
    simp [hx0]

@[simp] lemma Polynomial.natDegree_prod_X_sub_C [Nontrivial R] {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i in s, (X - C (t i))).natDegree = s.card :=
  (natDegree_prod' _ _ (by simp)).trans (by simp)

@[simp] lemma Polynomial.natDegree_C_mul_prod_X_sub_C
    {σ : Type*} (t : σ → R) (s : Finset σ) {x : R} (hx0 : x ≠ 0) :
    (C x * ∏ i in s, (X - C (t i))).natDegree = s.card := by
  rw [natDegree_mul', natDegree_prod'] <;>
    simp [hx0]

@[simp] lemma Polynomial.natDegree_C_mul_prod_X_sub_C_le
    {σ : Type*} (t : σ → R) (s : Finset σ) (x : R) :
    (C x * ∏ i in s, (X - C (t i))).natDegree ≤ s.card := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (natDegree_C_mul_prod_X_sub_C _ _ hx0).le

@[simp] lemma Polynomial.prod_X_sub_C_ne_zero [Nontrivial R] {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i in s, (X - C (t i))) ≠ 0 :=
  leadingCoeff_ne_zero.mp (by simp)

@[simp] lemma Polynomial.C_mul_prod_X_sub_C_ne_zero
    {σ : Type*} (t : σ → R) (s : Finset σ) {x : R} (hx0 : x ≠ 0) :
    (C x * ∏ i in s, (X - C (t i))) ≠ 0 :=
  leadingCoeff_ne_zero.mp (by simpa)

@[simp] lemma Polynomial.coeff_prod_X_sub_C_card {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i in s, (X - C (t i))).coeff s.card = 1 := by
  simpa only [leadingCoeff, natDegree_prod_X_sub_C] using leadingCoeff_prod_X_sub_C t s

lemma Polynomial.coeff_C_mul_prod_X_sub_C_card
    {σ : Type*} (t : σ → R) (s : Finset σ) (x : R) :
    (C x * ∏ i in s, (X - C (t i))).coeff s.card = x := by
  simp

lemma Polynomial.splits_prod_X_sub_C
    {σ : Type*} (t : σ → K) (s : Finset σ) :
    Splits (RingHom.id K) (∏ i in s, (X - C (t i))) :=
  splits_prod _ (fun _ _ => splits_X_sub_C _)

lemma Polynomial.splits_C_mul_prod_X_sub_C
    {σ : Type*} (t : σ → K) (s : Finset σ) (x : K) :
    Splits (RingHom.id K) (C x * ∏ i in s, (X - C (t i))) :=
  splits_mul _ (splits_C _ _) (splits_prod_X_sub_C _ _)

@[simp] lemma Polynomial.roots_prod_X_sub_C'
    {σ : Type*} (t : σ → K) (s : Finset σ) :
    (∏ i in s, (X - C (t i))).roots = s.val.map t := by
  simp only [roots_prod _ _ (Monic.ne_zero (monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))),
    roots_X_sub_C, Multiset.bind_singleton]

@[simp] lemma Polynomial.roots_C_mul_prod_X_sub_C'
    {σ : Type*} (t : σ → K) (s : Finset σ) {x : K} (hx0 : x ≠ 0) :
    (C x * ∏ i in s, (X - C (t i))).roots = s.val.map t := by
  rw [roots_C_mul _ hx0, roots_prod_X_sub_C']

lemma Polynomial.isRoot_X_sub_C {x y : R} :
    IsRoot (X - C x) y ↔ x = y := by
  simp [sub_eq_zero, eq_comm]

lemma Polynomial.isRoot_prod_X_sub_C [IsDomain R]
    {σ : Type*} {t : σ → R} {s : Finset σ} {x : R} :
    IsRoot (∏ i in s, (X - C (t i))) x ↔ ∃ i ∈ s, x = t i := by
  simp only [isRoot_prod, isRoot_X_sub_C, eq_comm]

@[simp] lemma Polynomial.isRoot_C_mul_prod_X_sub_C [IsDomain R]
    {σ : Type*} {t : σ → K} {s : Finset σ} {x y : K} :
    IsRoot (C x * ∏ i in s, (X - C (t i))) y ↔ x = 0 ∨ ∃ i ∈ s, y = t i := by
  rw [IsRoot, eval_mul, mul_eq_zero, eval_C, ← IsRoot, isRoot_prod_X_sub_C]

/-- The coefficients of a polynomial are a symmetric polynomial function in its roots. -/
lemma Polynomial.coeff_isSymmPolynomial_roots {ι : Type*} [Fintype ι] (x : K) :
    ∀ i, IsSymmPolynomial (fun t => (C x * ∏ i : ι, (X - C (t i))).coeff i) := by
  intro i
  by_cases hx0 : x = 0
  · simpa [hx0] using IsSymmPolynomial.const 0

  cases le_or_gt i (Fintype.card ι)
  case neg.inr h =>
    conv =>
      congr
      ext t
      rw [coeff_eq_zero_of_natDegree_lt ((natDegree_C_mul_prod_X_sub_C _ _ hx0).trans_lt h)]
    apply IsSymmPolynomial.const
  case neg.inl h =>
    conv =>
      congr
      ext t
      rw [coeff_eq_esymm_roots_of_splits (splits_C_mul_prod_X_sub_C t _ x)
            (h.trans_eq (natDegree_C_mul_prod_X_sub_C t _ hx0).symm)]
    refine IsSymmPolynomial.mul (.mul ?_ ?_) ?_
    · simp only [leadingCoeff_C_mul_prod_X_sub_C]
      apply IsSymmPolynomial.const
    · simp only [natDegree_C_mul_prod_X_sub_C _ _ hx0]
      apply IsSymmPolynomial.const
    · simp_rw [roots_C_mul_prod_X_sub_C' _ _ hx0, natDegree_C_mul_prod_X_sub_C _ _ hx0]
      apply IsSymmPolynomial.esymm

/-- The resultant of a polynomial is a symmetric polynomial function in its roots. -/
lemma Polynomial.resultant_isSymmPolynomial_left {ι : Type*} [Fintype ι]
    (Q : K[X]) (x : K) :
    IsSymmPolynomial (fun t => (C x * ∏ i : ι, (X - C (t i))).resultant Q) := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, zero_mul]
    by_cases hQ0 : Q.natDegree = 0
    · obtain ⟨y, rfl⟩ := natDegree_eq_zero.mp hQ0
      simp_rw [resultant_C, natDegree_zero, pow_zero]
      apply IsSymmPolynomial.const
    simp_rw [zero_resultant _ hQ0]
    apply IsSymmPolynomial.const
  refine IsSymmPolynomial.resultant (m := Fintype.card ι) ?_ (fun _ => rfl)
      (Polynomial.coeff_isSymmPolynomial_roots x)
      (fun i => IsSymmPolynomial.const _)
  · intro tu
    simp [hx0]

/-- The resultant of a polynomial is a symmetric polynomial function in its roots. -/
lemma Polynomial.resultant_isSymmPolynomial_right {ι : Type*} [Fintype ι]
    (P : K[X]) (x : K) :
    IsSymmPolynomial (fun t => P.resultant (C x * ∏ i : ι, (X - C (t i)))) := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, zero_mul]
    by_cases hP0 : P.natDegree = 0
    · obtain ⟨y, rfl⟩ := natDegree_eq_zero.mp hP0
      simp_rw [C_resultant, natDegree_zero, pow_zero]
      apply IsSymmPolynomial.const
    simp_rw [resultant_zero _ hP0]
    apply IsSymmPolynomial.const
  simp_rw [resultant_swap P]
  refine .mul ?_ (Polynomial.resultant_isSymmPolynomial_left _ _)
  convert IsSymmPolynomial.const (ι := ι) ((-1) ^ (P.natDegree * Fintype.card ι) : K)
  · simp [hx0]

/-- If the coefficients of `P` and `Q` are given by polynomial functions, so is their resultant.

Note that we have to be a bit tricky here: a priori the degree of `P x` and `Q x` can change
as a function of `x`, so suddenly we could get a completely different Sylvester matrix.
Thus we need to assume the degree remains constant in terms of `x`.
-/
theorem IsPolynomial.resultant {ι κ : Type*} {m n : ℕ} {P : (ι → R) → R[X]} {Q : (κ → R) → R[X]}
    (hdegP : ∀ x, (P x).natDegree = m) (hdegQ : ∀ x, (Q x).natDegree = n)
    (hf : ∀ i, IsPolynomial (fun x => coeff (P x) i)) (hg : ∀ i, IsPolynomial (fun x => coeff (Q x) i)) :
    IsPolynomial (fun (xy : ι ⊕ κ → R) => (P (xy ∘ Sum.inl)).resultant (Q (xy ∘ Sum.inr))) := by
  conv =>
    congr
    · ext xy
      rw [resultant_eq_det_sylvesterMatrixVec_cast _ _ (hdegP _) (hdegQ _),
          sylvesterMatrixVec]
      · skip
  simp only [det_transpose]
  refine IsPolynomial.det _ (fun i j => Fin.addCases (fun i => ?_) (fun i => ?_) i)
  · simp only [Fin.addCases_left]
    exact IsPolynomial.sylvesterVec (fun i => IsPolynomial.comp _ (hg _)) _ _
  · simp only [Fin.addCases_right]
    exact IsPolynomial.sylvesterVec (fun i => IsPolynomial.comp _ (hf _)) _ _

/-- The resultant of two polynomials is a polynomial function in their roots. -/
lemma Polynomial.resultant_isPolynomial_roots {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : K) :
    IsPolynomial (fun tu =>
      (C x * ∏ i : ι, (X - C (tu (Sum.inl i)))).resultant
      (C y * ∏ i : κ, (X - C (tu (Sum.inr i))))) := by
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · simpa [hx0, hy0] using IsPolynomial.const 1
    · obtain (hκ | hκ) := isEmpty_or_nonempty κ
      · simpa [hx0, hκ] using IsPolynomial.const 1
      convert IsPolynomial.const (0 : K)
      rw [hx0, map_zero, zero_mul, zero_resultant]
      · rw [natDegree_C_mul_prod_X_sub_C _ _ hy0]
        exact Fintype.card_pos.ne'
  by_cases hy0 : y = 0
  · obtain (hι | hι) := isEmpty_or_nonempty ι
    · simpa [hy0, hι] using IsPolynomial.const 1
    convert IsPolynomial.const (0 : K)
    rw [hy0, map_zero, zero_mul, resultant_zero]
    · rw [natDegree_C_mul_prod_X_sub_C _ _ hx0]
      exact Fintype.card_pos.ne'
  exact IsPolynomial.resultant
    (P := fun t => C x * ∏ i : ι, (X - C (t i)))
    (Q := fun u => C y * ∏ i : κ, (X - C (u i)))
    (fun _ => natDegree_C_mul_prod_X_sub_C _ _ hx0)
    (fun _ => natDegree_C_mul_prod_X_sub_C _ _ hy0)
    (fun i => (Polynomial.coeff_isSymmPolynomial_roots _ i).toIsPolynomial)
    (fun i => (Polynomial.coeff_isSymmPolynomial_roots _ i).toIsPolynomial)

theorem zero_of_eval_zero' [IsDomain R] {σ : Type*} (f : σ → R) (hf : (Set.range f).Infinite)
    (p : R[X]) (h : ∀ x, p.eval (f x) = 0) : p = 0 := by
  classical
  by_contra hp
  have : Infinite (Set.range f) := hf.to_subtype
  refine @Fintype.false (Set.range f) _ ?_
  exact ⟨(p.roots.toFinset).subtype _, fun ⟨x, hx⟩ => by
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
    exact Finset.mem_subtype.mpr (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _)))⟩

/-- If an `MvPolynomial` evaluates to zero everywhere on an infinite domain, it is zero. -/
lemma MvPolynomial.zero_of_eval_zero_aux [IsDomain R] [Infinite R]
    (p : MvPolynomial (Fin n) R) (h : ∀ x, MvPolynomial.eval x p = 0) : p = 0 := by
  induction n
  case zero =>
    rw [MvPolynomial.eq_C_of_isEmpty p] at h ⊢
    simp only [algHom_C, algebraMap_eq, eval_C, forall_const] at h
    simp [h]
  case succ n ih =>
    apply (MvPolynomial.finSuccEquiv R n).injective
    rw [map_zero]
    apply zero_of_eval_zero' MvPolynomial.C (Set.infinite_range_of_injective (C_injective _ _))
    refine fun x => ih _ (fun xs => ?_)
    rw [← h (Fin.cons x xs), MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map,
        ← Polynomial.eval₂_hom, MvPolynomial.eval_C]

/-- If an `MvPolynomial` is zero on all points of an infinite domain, they are equal. -/
lemma MvPolynomial.zero_of_eval_zero {σ : Type*} [IsDomain R] [Infinite R]
    (p : MvPolynomial σ R) (h : ∀ x, MvPolynomial.eval x p = 0) : p = 0 := by
  obtain ⟨n, f, hf, q, rfl⟩ := MvPolynomial.exists_fin_rename p
  by_cases hn : n = 0
  · subst hn
    rw [MvPolynomial.eq_C_of_isEmpty q] at h ⊢
    simp only [algHom_C, algebraMap_eq, eval_C, forall_const] at h
    simp [h]
  have : NeZero n := ⟨hn⟩
  rw [MvPolynomial.zero_of_eval_zero_aux q (?_), map_zero]
  intro x
  specialize h (x ∘ f.invFun)
  simp [eval_rename] at h
  convert h
  ext
  rw [Function.comp_apply, Function.comp_apply, Function.leftInverse_invFun hf]

/-- If two `MvPolynomial`s evaluate the same all points of an infinite domain, they are equal. -/
lemma MvPolynomial.eq_of_eval_eq {σ : Type*} [IsDomain R] [Infinite R]
    (p q : MvPolynomial σ R) (h : ∀ x, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q :=
  sub_eq_zero.mp (zero_of_eval_zero _ (fun i => by rw [eval_sub, h, sub_eq_zero]))

lemma MvPolynomial.X_sub_X_dvd_of_rename_eq_zero [IsDomain R]
    {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ R)
    {i j : σ} (h : rename (Function.update id i j) P = 0) :
    X i - X j ∣ P := by
  by_cases hij : i = j
  · rw [hij, Function.update_eq_self_iff.mpr, rename_id] at h
    rw [h]
    apply dvd_zero
    · rfl
  -- This is a bit of annoying work because we don't have division with remainder
  -- for MvPolynomials yet.
  let τ : Type _ := { x : σ // x ≠ i }
  have hτ : ∀ x : τ, (x : σ) ≠ i := fun x => x.2
  let e : σ ≃ Option τ :=
  { toFun := fun k => if h : k = i then none else some ⟨k, h⟩,
    invFun := fun o => Option.elim o i Subtype.val,
    left_inv := fun k => by by_cases h : k = i <;> simp [h]
    right_inv := fun o => by cases o <;> simp [hτ] }
  have ei : e i = none := dif_pos rfl
  have e_ne_i : ∀ {a} (h : a ≠ i), e a = some ⟨a, h⟩ := fun h => dif_neg h
  have ej : e j = some ⟨j, Ne.symm hij⟩ := e_ne_i _
  rw [← map_dvd_iff ((MvPolynomial.renameEquiv R e).trans (MvPolynomial.optionEquivLeft R τ))]
  simp only [map_sub, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, ei,
    Option.elim_none, ej, ne_eq, Option.elim_some, optionEquivLeft_X_some, optionEquivLeft_X_none]
  apply dvd_iff_isRoot.mpr (rename_injective _ Subtype.val_injective _)
  -- Found this rewrite by exploration; there's no useful explanation I can offer for why it works.
  rw [map_zero, ← h, optionEquivLeft_apply, aeval_def, MvPolynomial.polynomial_eval_eval₂,
      eval₂_rename, ← aeval_X_left_apply (rename _ P), aeval_def, algebraMap_eq, eval₂_rename]
  refine (eval₂_comp_left _ _ _ _).trans ?_
  congr
  · ext x
    simp
  · ext a
    by_cases hai : a = i
    · simp [hai, ei]
    simp [e_ne_i, hai]

lemma MvPolynomial.X_sub_X_dvd_of_eval_eq_zero [IsDomain R] [Infinite R]
    {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ R)
    {i j : σ} (h : ∀ f, f i = f j → eval f P = 0) :
    X i - X j ∣ P := by
  apply MvPolynomial.X_sub_X_dvd_of_rename_eq_zero
  apply MvPolynomial.zero_of_eval_zero
  intro f
  specialize h (Function.update f i (f j)) ?_
  · by_cases hij : j = i
    · subst hij
      simp
    rw [Function.update_same, Function.update_noteq hij]
  rwa [eval_rename, Function.comp_update, Function.comp_id]

theorem MvPolynomial.isHomogeneous_of_add_left {σ : Type*} {p q : MvPolynomial σ R}
    (hq : IsHomogeneous q n) (hpq : IsHomogeneous (p + q) n) :
    IsHomogeneous p n := by
  simpa using hpq.sub hq

theorem MvPolynomial.isHomogeneous_of_add_right {σ : Type*} {p q : MvPolynomial σ R}
    (hp : IsHomogeneous p n) (hpq : IsHomogeneous (p + q) n) :
    IsHomogeneous q n := by
  simpa using hpq.sub hp

lemma Finset.disjoint_iff_not_mem_of_mem {α : Type*} {s t : Finset α} :
    Disjoint s t ↔ ∀ {x}, x ∈ s → ¬ x ∈ t :=
  ⟨fun h x hs ht => not_mem_empty _ (h (x := {x})
    (singleton_subset_iff.mpr hs)
    (singleton_subset_iff.mpr ht)
    (mem_singleton_self _)),
   fun h _ hs ht _ hx => (h (hs hx) (ht hx)).elim⟩

lemma Finset.disjoint_iff_not_mem_or_not_mem {α : Type*} {s t : Finset α} :
    Disjoint s t ↔ ∀ {x}, x ∉ s ∨ x ∉ t :=
  Finset.disjoint_iff_not_mem_of_mem.trans (forall_congr' (fun _ => imp_iff_or_not.trans or_comm))

theorem MvPolynomial.isWeightedHomogeneous_left_of_add_of_disjoint {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R}
    (hpq : IsWeightedHomogeneous w (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsWeightedHomogeneous w p n := by
  intro d hd
  apply hpq
  suffices coeff d q = 0 by rwa [coeff_add, this, add_zero]
  exact not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp hsupp
    (mem_support_iff.mpr hd))

theorem MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R}
    (hpq : IsWeightedHomogeneous w (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsWeightedHomogeneous w q n :=
  isWeightedHomogeneous_left_of_add_of_disjoint (by rwa [add_comm]) (by rwa [disjoint_comm])

theorem MvPolynomial.isHomogeneous_left_of_add_of_disjoint {σ : Type*} {p q : MvPolynomial σ R}
    (hpq : IsHomogeneous (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsHomogeneous p n := by
  intro d hd
  apply hpq
  suffices coeff d q = 0 by rwa [coeff_add, this, add_zero]
  exact not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp hsupp
    (mem_support_iff.mpr hd))

theorem MvPolynomial.isHomogeneous_right_of_add_of_disjoint {σ : Type*} {p q : MvPolynomial σ R}
    (hpq : IsHomogeneous (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsHomogeneous q n :=
  isHomogeneous_left_of_add_of_disjoint (by rwa [add_comm]) (by rwa [disjoint_comm])

lemma MvPolynomial.isWeightedHomogeneous_zero_iff {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R}
    (hw : NonTorsionWeight w) :
    IsWeightedHomogeneous w p 0 ↔ ∃ a, p = C a := by
  constructor
  · intro h
    use constantCoeff p
    ext i
    by_cases hi : i = 0
    · simp [hi, constantCoeff]
    · classical
      rw [IsWeightedHomogeneous.coeff_eq_zero h, coeff_C, if_neg (Ne.symm hi)]
      · contrapose! hi
        ext j
        rw [weightedDegree_eq_zero_iff hw] at hi
        apply hi
  · rintro ⟨a, rfl⟩
    exact isWeightedHomogeneous_C _ _

lemma MvPolynomial.isHomogeneous_zero_iff {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p 0 ↔ ∃ a, p = C a := by
  constructor
  · intro h
    use constantCoeff p
    ext i
    by_cases hi : i = 0
    · simp [hi, constantCoeff]
    · classical
      rw [IsHomogeneous.coeff_eq_zero h, coeff_C, if_neg (Ne.symm hi)]
      · contrapose! hi
        ext j
        rw [← weightedDegree_one, weightedDegree_eq_zero_iff] at hi
        apply hi
        · refine nonTorsionWeight_of (fun _ => one_ne_zero)
  · rintro ⟨a, rfl⟩
    exact isHomogeneous_C _ _

lemma MvPolynomial.isWeightedHomogeneous_C_iff {σ : Type*} {a : R} {w : σ → ℕ} :
    IsWeightedHomogeneous w (C (σ := σ) a) n ↔ a = 0 ∨ n = 0 := by
  constructor
  · rw [or_iff_not_imp_left]
    intro h ha
    exact h.inj_right ((map_ne_zero_iff _ (C_injective _ _)).mpr ha) (isWeightedHomogeneous_C _ _)
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact isWeightedHomogeneous_zero _ _ _
    · exact isWeightedHomogeneous_C _ _

lemma MvPolynomial.isHomogeneous_C_iff {σ : Type*} {a : R} :
    IsHomogeneous (C (σ := σ) a) n ↔ a = 0 ∨ n = 0 := by
  constructor
  · rw [or_iff_not_imp_left]
    intro h ha
    exact h.inj_right (isHomogeneous_C _ _) ((map_ne_zero_iff _ (C_injective _ _)).mpr ha)
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_C _ _

lemma MvPolynomial.isHomogeneous_monomial_iff {σ : Type*} {x : σ →₀ ℕ} {a : R} :
    IsHomogeneous (monomial x a) n ↔ a = 0 ∨ n = degree x := by
  constructor
  · rw [or_iff_not_imp_left]
    intro h ha
    exact h.inj_right (isHomogeneous_monomial _ rfl) (mt monomial_eq_zero.mp ha)
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ rfl

lemma MvPolynomial.coeff_zero_mul {σ : Type*} {p q : MvPolynomial σ R} :
    coeff 0 (p * q) = coeff 0 p * coeff 0 q := by
  classical
  rw [coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton]

lemma MvPolynomial.X_mul_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : MvPolynomial.X i * p = MvPolynomial.X i * q) : p = q := by
  ext d
  have := congr_arg (coeff (Finsupp.single i 1 + d)) h
  simpa [coeff_X_mul, coeff_X_mul] using this

lemma MvPolynomial.mul_X_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : p * MvPolynomial.X i = q * MvPolynomial.X i) : p = q := by
  ext d
  have := congr_arg (coeff (d + Finsupp.single i 1)) h
  rwa [coeff_mul_X, coeff_mul_X] at this

lemma MvPolynomial.coeff_mul_X_pow {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff (m + Finsupp.single i n) (p * MvPolynomial.X i ^ n) =
      MvPolynomial.coeff m p := by
  simp [X_pow_eq_monomial, coeff_mul_monomial']

lemma MvPolynomial.coeff_X_pow_mul {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff (m + Finsupp.single i n) (MvPolynomial.X i ^ n * p) =
      MvPolynomial.coeff m p := by
  simp [X_pow_eq_monomial, coeff_monomial_mul']

lemma MvPolynomial.coeff_X_pow_mul' {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff m (MvPolynomial.X i ^ n * p) =
      if n ≤ m i then MvPolynomial.coeff (m - Finsupp.single i n) p else 0 := by
  simp [X_pow_eq_monomial, coeff_monomial_mul']

lemma MvPolynomial.coeff_mul_X_pow' {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff m (p * MvPolynomial.X i ^ n) =
      if n ≤ m i then MvPolynomial.coeff (m - Finsupp.single i n) p else 0 := by
  simp [X_pow_eq_monomial, coeff_mul_monomial']

lemma MvPolynomial.X_mul_pow_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : MvPolynomial.X i ^ n * p = MvPolynomial.X i ^ n * q) : p = q := by
  ext d
  have := congr_arg (coeff (Finsupp.single i n + d)) h
  simpa [coeff_X_pow_mul', coeff_X_pow_mul'] using this

lemma MvPolynomial.mul_X_pow_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : p * MvPolynomial.X i ^ n = q * MvPolynomial.X i ^ n) : p = q := by
  ext d
  have := congr_arg (coeff (Finsupp.single i n + d)) h
  simpa [coeff_mul_X_pow', coeff_mul_X_pow'] using this

lemma MvPolynomial.X_mul_eq_C_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ} {a : R} :
    MvPolynomial.X i * p = MvPolynomial.C a ↔ a = 0 ∧ p = 0 := by
  classical
  by_cases hp : p = 0
  · rw [hp, eq_comm, mul_zero, map_eq_zero_iff _ (C_injective _ _)]
    simp
  simp only [hp, and_false, iff_false]
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hp
  intro hxi
  have := congr_arg (coeff (Finsupp.single i 1 + d)) hxi
  rw [coeff_X_mul, coeff_C, if_neg (Ne.symm (Finsupp.ne_iff.mpr ⟨i, by simp⟩))] at this
  contradiction

lemma MvPolynomial.mul_X_eq_C_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ} {a : R} :
    p * MvPolynomial.X i = MvPolynomial.C a ↔ a = 0 ∧ p = 0 := by
  rw [mul_comm, X_mul_eq_C_iff]

@[simp] lemma MvPolynomial.weightedDegree_const {σ : Type*} {w : ℕ} (x : σ →₀ ℕ) :
    weightedDegree (fun _ => w) x = degree x * w := by
  simp only [weightedDegree_apply, Finsupp.sum, smul_eq_mul, Finset.sum_const, degree,
    Finset.sum_mul]

@[simp] lemma MvPolynomial.weightedDegree_add {σ : Type*} {w : σ → ℕ} (d e : σ →₀ ℕ) :
    weightedDegree w (d + e) = weightedDegree w d + weightedDegree w e := by
  classical
  simp only [weightedDegree_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_subset Finsupp.support_add,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib, add_mul]
    rfl
  all_goals
  · intro i _ hi
    simp only [Finsupp.not_mem_support_iff.mp hi, zero_mul]

@[simp] lemma MvPolynomial.degree_add {σ : Type*} (d e : σ →₀ ℕ) :
    degree (d + e) = degree d + degree e := by
  classical
  unfold degree
  rw [Finset.sum_subset Finsupp.support_add,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    rfl
  all_goals
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi

@[simp] lemma MvPolynomial.weightedDegree_sub {σ : Type*} {w : σ → ℕ} (d e : σ →₀ ℕ) (h : e ≤ d) :
    weightedDegree w (d - e) = weightedDegree w d - weightedDegree w e := by
  classical
  simp only [weightedDegree_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_subset Finsupp.support_tsub,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.tsub_apply, Nat.sub_mul]
    apply Nat.eq_sub_of_add_eq
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
    intro x _
    rw [Nat.sub_add_cancel (Nat.mul_le_mul_right _ (h x))]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]
  · intro i _ hi
    rw [Finsupp.tsub_apply, Nat.sub_mul, Finsupp.not_mem_support_iff.mp hi, zero_mul, Nat.zero_sub]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]

@[simp] lemma MvPolynomial.degree_sub {σ : Type*} (d e : σ →₀ ℕ) (h : e ≤ d) :
    degree (d - e) = degree d - degree e := by
  classical
  unfold degree
  rw [Finset.sum_subset Finsupp.support_tsub,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.tsub_apply]
    apply Nat.eq_sub_of_add_eq
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
    intro x _
    rw [Nat.sub_add_cancel (h x)]
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi
  · intro i _ hi
    rw [Finsupp.tsub_apply, Finsupp.not_mem_support_iff.mp hi, Nat.zero_sub]
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi

@[simp] lemma MvPolynomial.weightedDegree_single {σ : Type*} {w : σ → ℕ} (i : σ) (n : ℕ) :
    weightedDegree w (Finsupp.single i n) = n * w i := by
  simp only [weightedDegree_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_subset Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]

@[simp] lemma MvPolynomial.degree_single {σ : Type*} (i : σ) (n : ℕ) :
    degree (Finsupp.single i n) = n := by
  unfold degree
  rw [Finset.sum_subset Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi

@[simp] lemma MvPolynomial.weightedDegree_mapDomain {σ τ : Type*} {w : τ → ℕ} (f : σ → τ) (d : σ →₀ ℕ) :
    weightedDegree w (Finsupp.mapDomain f d) = weightedDegree (fun i => w (f i)) d := by
  simp only [weightedDegree_apply, smul_eq_mul, Function.comp_apply]
  rw [Finsupp.sum_mapDomain_index]
  · simp
  · simp [add_mul]

@[simp] lemma MvPolynomial.degree_mapDomain {σ τ : Type*} (f : σ → τ) (d : σ →₀ ℕ) :
    degree (Finsupp.mapDomain f d) = degree d :=
  Finsupp.sum_mapDomain_index (h := fun _ x => x) (fun _ => rfl) (fun _ _ _ => rfl)

lemma MvPolynomial.isWeightedHomogeneous_mul_X_pow_iff {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} {i : σ} {e : ℕ} (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (p * X i ^ e) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + e * w i := by
  constructor
  · intro hp
    have hn0 : e * w i ≤ n := by
      rw [IsWeightedHomogeneous] at hp
      obtain ⟨d, hd⟩ := ne_zero_iff.mp hp0
      rw [← hp (coeff_mul_X_pow.trans_ne hd), weightedDegree_add, weightedDegree_single]
      exact le_of_add_le_right le_rfl
    refine ⟨n - e * w i, ?_, (Nat.sub_add_cancel hn0).symm⟩
    simp only [IsWeightedHomogeneous, weightedDegree_one, coeff_mul_X] at hp ⊢
    intro d hd
    have := @hp (Finsupp.single i e + d) ?_
    · rw [← this, weightedDegree_add, weightedDegree_single, Nat.add_sub_cancel_left]
    · rwa [add_comm, coeff_mul_X_pow]
  · rintro ⟨m, hp, rfl⟩
    rw [X_pow_eq_monomial]
    exact hp.mul (isWeightedHomogeneous_monomial _ _ _ (by simp))

lemma MvPolynomial.isWeightedHomogeneous_X_pow_mul_iff {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} {i : σ} {e : ℕ} (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (X i ^ e * p) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + e *  w i := by
  rw [mul_comm, isWeightedHomogeneous_mul_X_pow_iff]
  · assumption

lemma MvPolynomial.isWeightedHomogeneous_mul_X_iff {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (p * X i) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + w i := by
  constructor
  · intro hp
    have hn0 : w i ≤ n := by
      rw [IsWeightedHomogeneous] at hp
      obtain ⟨d, hd⟩ := ne_zero_iff.mp hp0
      specialize hp ((coeff_mul_X _ _ _).trans_ne hd)
      refine le_of_add_le_right (a := weightedDegree w d) (Eq.le ?_)
      rwa [weightedDegree_add, weightedDegree_single, one_mul] at hp
    refine ⟨n - w i, ?_, (Nat.sub_add_cancel hn0).symm⟩
    rw [← Nat.sub_add_cancel hn0] at hp
    set m := n.pred
    simp only [IsWeightedHomogeneous, weightedDegree_one, coeff_mul_X] at hp ⊢
    intro d hd
    have := @hp (Finsupp.single i 1 + d) ?_
    simpa [add_comm] using this
    · rwa [add_comm, coeff_mul_X]
  · rintro ⟨m, hp, rfl⟩
    exact hp.mul (isWeightedHomogeneous_X _ _ _)

lemma MvPolynomial.isWeightedHomogeneous_X_mul_iff {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (X i * p) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + w i := by
  rw [mul_comm, isWeightedHomogeneous_mul_X_iff]
  · assumption

lemma MvPolynomial.isHomogeneous_mul_X_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsHomogeneous (p * X i) n ↔ ∃ m, IsHomogeneous p m ∧ n = m + 1 := by
  constructor
  · intro hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha⟩ := isHomogeneous_zero_iff.mp hp
      exact hp0 (mul_X_eq_C_iff.mp ha).2
    refine ⟨n.pred, ?_, (Nat.succ_pred_eq_of_ne_zero hn0).symm⟩
    rw [← Nat.succ_pred_eq_of_ne_zero hn0] at hp
    set m := n.pred
    simp only [IsHomogeneous, IsWeightedHomogeneous, weightedDegree_one, coeff_mul_X] at hp ⊢
    intro d hd
    have := @hp (Finsupp.single i 1 + d) ?_
    simpa [add_comm] using this
    · rwa [add_comm, coeff_mul_X]
  · rintro ⟨m, hp, rfl⟩
    exact hp.mul (isHomogeneous_X _ _)

lemma MvPolynomial.isHomogeneous_X_mul_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsHomogeneous (X i * p) n ↔ ∃ m, IsHomogeneous p m ∧ n = m + 1 := by
  rw [mul_comm, isHomogeneous_mul_X_iff]
  · assumption

lemma MvPolynomial.aeval_X_pow_mul_monomial {σ : Type*} {w : σ → ℕ} (i : σ) (x : σ →₀ ℕ) (a : R) :
    aeval (fun j => X i ^ w j * X j) (monomial x a) =
      monomial (x + .single i (weightedDegree w x)) a := by
  simp only [aeval_monomial, algebraMap_eq, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
      prod_X_pow_eq_monomial, monomial_add_single, Finset.prod_pow_eq_pow_sum,
      ← pow_mul, fun i => mul_comm (w i) (x i)]
  rw [mul_left_comm, C_mul_monomial, mul_one, mul_comm]
  rfl

lemma MvPolynomial.aeval_X_mul_monomial {σ : Type*} (i : σ) (x : σ →₀ ℕ) (a : R) :
    aeval (fun j => X i * X j) (monomial x a) = monomial (x + .single i (degree x)) a := by
  simp only [aeval_monomial, algebraMap_eq, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
      prod_X_pow_eq_monomial, monomial_add_single, Finset.prod_pow_eq_pow_sum, degree]
  rw [mul_left_comm, C_mul_monomial, mul_one, mul_comm]

@[simp] lemma MvPolynomial.degree_zero {σ : Type*} : MvPolynomial.degree (0 : σ →₀ ℕ) = 0 := by
  simp [degree]

/-- Taking a product over `s : Finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`. -/
@[to_additive "Taking a sum over `s : Finset α` is the same as adding the value on a single element
`f a` to the sum over `s.erase a`."]
theorem Finset.mul_prod_erase' {α β : Type*} [DecidableEq α] [CommMonoid β] (s : Finset α) (f : α → β)
    {a : α} (h : a ∉ s → f a = 1) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  by_cases ha : a ∈ s
  · exact Finset.mul_prod_erase _ _ ha
  · rw [h ha, one_mul, Finset.prod_erase _ (h ha)]

lemma Finsupp.add_single_injective {σ : Type*} {j : σ} {f : (σ →₀ ℕ) → ℕ}
    {a b : σ →₀ ℕ} (hf : (∀ i ≠ j, a i = b i) → ∃ (v : ℕ), b j * v + f a = a j * v + f b)
    (h : a + Finsupp.single j (f a) = b + Finsupp.single j (f b)) :
    a = b := by
  ext i
  have eq_of_ne : ∀ i ≠ j, a i = b i := by
    intro i hij
    simpa [hij.symm] using (DFunLike.congr_fun h i)
  by_cases hij : j = i
  swap
  · exact eq_of_ne _ (Ne.symm hij)
  subst hij
  obtain ⟨v, hv⟩ := hf eq_of_ne
  refine mul_left_cancel₀ v.succ_ne_zero ?_
  have := DFunLike.congr_fun h j
  simp only [smul_eq_mul, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Finsupp.sum] at this
  rw [Nat.succ_mul, Nat.succ_mul, ← add_left_cancel_iff (a := f a), ← add_assoc, ← add_assoc,
      add_comm (f a), add_comm (f a), mul_comm v, mul_comm v, hv, add_assoc, add_assoc,
      add_comm (f a), add_comm (f b), this]

theorem MvPolynomial.coeff_aeval_X_pow_mul {σ : Type*} {w : σ → ℕ} {j : σ} (p : MvPolynomial σ R)
    (d : σ →₀ ℕ):
    coeff (d + Finsupp.single j (weightedDegree w d)) (MvPolynomial.aeval (fun i => X j ^ w i * X i) p) =
      coeff d p := by
  classical
  induction p using induction_on'''
  case h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d]
    split_ifs with hd
    · subst hd
      simp
    · rw [coeff_C, if_neg]
      contrapose! hd
      ext i
      symm
      simpa using (Nat.add_eq_zero.mp (DFunLike.congr_fun hd i).symm).1
  case h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, coeff_add, ih]
    congr 1
    rw [aeval_X_pow_mul_monomial, coeff_monomial d]
    split_ifs with hd
    · subst hd
      rw [coeff_monomial, if_pos rfl]
    · rw [coeff_monomial, if_neg]
      contrapose! hd
      apply Finsupp.add_single_injective _ hd
      intro eq_of_ne
      use w j
      simp only [weightedDegree_apply, Finsupp.sum, smul_eq_mul]
      rw [← Finset.add_sum_erase' (s := a.support) (a := j),
          ← Finset.add_sum_erase' (s := d.support) (a := j)]
      · rw [add_left_comm, add_left_cancel_iff, add_left_cancel_iff, Finset.sum_congr]
        · ext i
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, eq_of_ne _ hij]
        · intro i hi
          rw [eq_of_ne _ (Finset.mem_erase.mp hi).1]
      · intro h
        rw [Finsupp.not_mem_support_iff.mp h, zero_mul]
      · intro h
        rw [Finsupp.not_mem_support_iff.mp h, zero_mul]

theorem MvPolynomial.coeff_aeval_X_mul {σ : Type*} {j : σ} (p : MvPolynomial σ R) (d : σ →₀ ℕ):
    coeff (d + Finsupp.single j (degree d)) (MvPolynomial.aeval (fun i => X j * X i) p) =
      coeff d p := by
  classical
  induction p using induction_on'''
  case h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d]
    split_ifs with hd
    · subst hd
      simp
    · rw [coeff_C, if_neg]
      contrapose! hd
      ext i
      symm
      simpa using (Nat.add_eq_zero.mp (DFunLike.congr_fun hd i).symm).1
  case h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, coeff_add, ih]
    congr 1
    rw [aeval_X_mul_monomial, coeff_monomial d]
    split_ifs with hd
    · subst hd
      rw [coeff_monomial, if_pos rfl]
    · rw [coeff_monomial, if_neg]
      contrapose! hd
      ext i
      symm
      have eq_of_ne : ∀ i ≠ j, d i = a i := by
        intro i hij
        simpa [hij.symm] using (DFunLike.congr_fun hd i).symm
      by_cases hij : j = i
      swap
      · exact eq_of_ne _ (Ne.symm hij)
      subst hij
      by_cases hdeg : degree d = degree a
      · rw [hdeg] at hd
        simpa using (DFunLike.congr_fun hd j).symm
      · have := (DFunLike.congr_fun hd j).symm
        have erase_eq : d.support.erase j = a.support.erase j := by
          ext i
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, eq_of_ne _ hij]
        simp only [degree, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
        rw [← Finset.add_sum_erase' (f := d) (a := j), ← Finset.add_sum_erase' (f := a) (a := j),
            Finset.sum_congr erase_eq (fun i hi => eq_of_ne i ?_)]
          at this
        · simpa [← add_assoc, ← two_mul] using this
        · exact (Finset.mem_erase.mp hi).1
        · intro h
          exact Finsupp.not_mem_support_iff.mp h
        · intro h
          exact Finsupp.not_mem_support_iff.mp h

lemma Nat.sub_self_div_two (h : Even n) : n - n / 2 = n / 2 := by
  refine (Nat.div_eq_of_eq_mul_right two_pos ?_).symm
  rw [Nat.mul_sub, Nat.mul_div_cancel' h.two_dvd, two_mul, Nat.add_sub_cancel]

theorem MvPolynomial.coeff_aeval_X_pow_mul' {σ : Type*} {w : σ → ℕ} {j : σ} (p : MvPolynomial σ R) (d : σ →₀ ℕ):
    coeff d (MvPolynomial.aeval (fun i => X j ^ w i * X i) p) =
      if (w j + 1) ∣ weightedDegree w d ∧ weightedDegree w d / (w j + 1) ≤ d j
      then coeff (d - Finsupp.single j (weightedDegree w d / (w j + 1))) p
      else 0 := by
  classical
  split_ifs with hdeg
  · obtain ⟨⟨d', hdeg⟩, hdiv⟩ := hdeg
    rw [hdeg, Nat.mul_div_cancel_left _ (Nat.succ_pos _)] at hdiv ⊢
    rw [← coeff_aeval_X_pow_mul (j := j) p]
    congr
    ext i
    by_cases hij : i = j
    · subst hij
      rw [weightedDegree_sub _ _ (Finsupp.single_le_iff.mpr hdiv), weightedDegree_single, hdeg,
          mul_comm, ← Nat.mul_sub, Nat.add_sub_cancel_left, mul_one, Finsupp.add_apply,
          Finsupp.tsub_apply, Nat.sub_add_cancel]
      · simpa
    · simp [Ne.symm hij]
  induction p using induction_on'''
  case neg.h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d, if_neg]
    · rintro rfl
      simp at hdeg
  case neg.h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, ih, add_zero, aeval_X_pow_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    refine hdeg ⟨?_, ?_⟩
    · use weightedDegree w a
      simp [add_mul, add_comm, mul_comm]
    · rw [map_add, weightedDegree_single, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
          add_comm, ← Nat.mul_succ, Nat.mul_div_cancel]
      · exact Nat.le_add_left _ _
      · exact Nat.succ_pos _

theorem MvPolynomial.coeff_aeval_X_mul' {σ : Type*} {j : σ} (p : MvPolynomial σ R) (d : σ →₀ ℕ):
    coeff d (MvPolynomial.aeval (fun i => X j * X i) p) =
      if Even (degree d) ∧ degree d / 2 ≤ d j
      then coeff (d - Finsupp.single j (degree d / 2)) p
      else 0 := by
  classical
  split_ifs with hdeg
  · rw [← coeff_aeval_X_mul (j := j) p]
    congr
    ext i
    by_cases hij : i = j
    · subst hij
      simp [degree_sub _ _ (Finsupp.single_le_iff.mpr hdeg.2), Nat.sub_self_div_two hdeg.1,
          Nat.sub_add_cancel hdeg.2]
    · simp [Ne.symm hij]
  induction p using induction_on'''
  case neg.h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d, if_neg]
    · rintro rfl
      simp at hdeg
  case neg.h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, ih, add_zero, aeval_X_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    simp [← two_mul] at hdeg

theorem MvPolynomial.aeval_X_mul_injective {σ : Type*} {j : σ} :
    Function.Injective (MvPolynomial.aeval (R := R) (S₁ := MvPolynomial σ R)
      (fun i => X j * X i)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [MvPolynomial.eq_zero_iff] at hp ⊢
  intro d
  simpa [MvPolynomial.coeff_aeval_X_mul, -MvPolynomial.aeval_eq_bind₁]
    using hp (d + Finsupp.single j (degree d))

theorem MvPolynomial.disjoint_support_rename {σ τ : Type*} {p q : MvPolynomial σ R} (f : σ → τ)
    (hf : f.Injective) (h : Disjoint p.support q.support) :
    Disjoint (MvPolynomial.rename f p).support (MvPolynomial.rename f q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not] at *
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hp
  obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ hq
  rw [Finsupp.mapDomain_injective hf u'_eq] at hu'
  exact hu' (h hu)

theorem MvPolynomial.disjoint_support_monomial_mul {σ : Type*} {p q : MvPolynomial σ R}
    (a : σ →₀ ℕ) (b : R) (h : Disjoint p.support q.support) :
    Disjoint (MvPolynomial.monomial a b * p).support (MvPolynomial.monomial a b * q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not, coeff_monomial_mul'] at *
  split_ifs at hp hq with hdeg
  · exact hq ((h (right_ne_zero_of_mul hp)) ▸ mul_zero b)
  · contradiction

theorem MvPolynomial.disjoint_support_X_pow_mul {σ : Type*} {p q : MvPolynomial σ R}
    (j : σ) (n : ℕ) (h : Disjoint p.support q.support) :
    Disjoint (X j ^ n * p).support (X j ^ n * q).support := by
  simpa only [X_pow_eq_monomial] using disjoint_support_monomial_mul (Finsupp.single j n) 1 h

theorem MvPolynomial.disjoint_support_aeval_X_pow_mul {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R} (j : σ) (h : Disjoint p.support q.support) :
    Disjoint
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j ^ w i * MvPolynomial.X i) p).support
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j ^ w i * MvPolynomial.X i) q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not, coeff_aeval_X_pow_mul'] at *
  split_ifs at hp hq with hdeg
  · exact hq (h hp)
  · contradiction

theorem MvPolynomial.disjoint_support_aeval_X_mul {σ : Type*} {p q : MvPolynomial σ R} (j : σ)
    (h : Disjoint p.support q.support) :
    Disjoint
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j * MvPolynomial.X i) p).support
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j * MvPolynomial.X i) q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not, coeff_aeval_X_mul'] at *
  split_ifs at hp hq with hdeg
  · exact hq (h hp)
  · contradiction

theorem MvPolynomial.coeff_zero_or_zero_of_disjoint_support {σ : Type*} {p q : MvPolynomial σ R}
    (x : σ →₀ ℕ) (h : Disjoint p.support q.support) :
    MvPolynomial.coeff x p = 0 ∨ MvPolynomial.coeff x q = 0 := by
  simp only [Finset.disjoint_iff_not_mem_or_not_mem, not_mem_support_iff] at h
  cases @h x
  case inl h => simp [h]
  case inr h => simp [h]

/-- A weighted homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul' {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p n ↔ MvPolynomial.aeval (fun i => X none ^ (Option.elim i 0 w) * X i) (rename some p) =
      X none ^ n * rename some p := by
  classical
  induction p using MvPolynomial.induction_on'' generalizing n
  case h_C a =>
    rw [isWeightedHomogeneous_C_iff]
    constructor
    · rintro (rfl | rfl)
      · simp
      · simp
    · rw [algHom_C, algebraMap_eq, aeval_C, algebraMap_eq, or_iff_not_imp_right]
      intro h hn
      have h := congr_arg (coeff (Finsupp.single none n)) h.symm
      rwa [coeff_C, mul_comm, coeff_C_mul, coeff_X_pow, if_pos rfl, if_neg, mul_one] at h
      · rwa [eq_comm, Finsupp.single_eq_zero]
  case h_add_weak x a p hx ha ih_r ih_l =>
    -- simp? [rename_monomial, aeval_monomial] at *
    simp only at *
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
    have disj : Disjoint ((monomial x) a).support (support p) := by simpa [support_monomial, ha]
    constructor
    · intro h
      have ih_l' := ih_l.mp (MvPolynomial.isWeightedHomogeneous_left_of_add_of_disjoint h disj)
      have ih_r' := ih_r.mp (MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint h disj)
      simp only [map_add, ih_l', ih_r', mul_add]
    · intro h
      rw [map_add, map_add, mul_add] at h
      have disj_lhs := disjoint_support_aeval_X_pow_mul (w := fun i => Option.elim i 0 w) none
        (disjoint_support_rename _ (Option.some_injective _) disj)
      have disj_rhs := disjoint_support_X_pow_mul none n
        (disjoint_support_rename _ (Option.some_injective _) disj)

      have h_l : ∀ (d : Option σ →₀ ℕ),
          coeff d ((aeval fun i ↦ X none ^ (Option.elim i 0 w) * X i) (rename some (monomial x a))) =
          coeff d (X none ^ n * rename some (monomial x a)) := by
        intro d
        obtain (hdl | hdl) := coeff_zero_or_zero_of_disjoint_support d disj_lhs <;>
            obtain (hdr | hdr) := coeff_zero_or_zero_of_disjoint_support d disj_rhs
        · rw [hdl, hdr]
        · have h := (ext_iff _ _).mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdl, ← h]
          simp only [coeff_aeval_X_pow_mul', coeff_X_pow_mul', Option.elim_none, zero_add,
            Nat.div_one, one_dvd, true_and] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hdeg hn
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (Ne.symm hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ (h.symm.trans_ne (Ne.symm hp))
            have : weightedDegree _ d = d none := le_antisymm hdeg <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu')))
          · rw [h]
          · rfl
          · rfl
        -- TODO: this next block is almost the same as the previous one.
        · have h := (ext_iff _ _).mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdr, h]
          simp only [coeff_aeval_X_pow_mul', coeff_X_pow_mul', Option.elim_none, zero_add,
            Nat.div_one, one_dvd, true_and] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hn hdeg
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (h.trans_ne hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ hp
            have : weightedDegree _ d = d none := le_antisymm hdeg <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu' (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu)))
          · rw [h]
          · rfl
          · rfl
        · simpa [hdl, hdr, -aeval_eq_bind₁] using (ext_iff _ _).mp h d
      refine IsWeightedHomogeneous.add
          (ih_l.mpr ((ext_iff _ _).mpr h_l))
          (ih_r.mpr ((ext_iff _ _).mpr fun d => ?_))
      have h := (ext_iff _ _).mp h d
      rw [coeff_add, h_l] at h
      exact add_left_cancel h
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0, -aeval_eq_bind₁] using isWeightedHomogeneous_zero _ _ _
    rw [isWeightedHomogeneous_mul_X_iff]
    constructor
    · rintro ⟨m, hp, rfl⟩
      simp [ih.mp hp, -aeval_eq_bind₁]
      ring
    · intro hp
      have hn0 : w i ≤ n := by
        obtain ⟨d, hd⟩ := ne_zero_iff.mp hp0
        have := (congr_arg (coeff _) hp)
          |>.trans coeff_X_pow_mul
          |>.trans (coeff_rename_mapDomain _ (Option.some_injective _) _ _)
          |>.trans (coeff_mul_X d _ _)
        rw [coeff_aeval_X_pow_mul'] at this
        split_ifs at this with hdeg
        · simp only [Option.elim_none, zero_add, map_add, weightedDegree_mapDomain,
              Option.elim_some, weightedDegree_single, one_mul, mul_zero, add_zero, isUnit_one,
              IsUnit.dvd, Nat.div_one, Finsupp.coe_add, Pi.add_apply, Set.mem_range, exists_false,
              not_false_eq_true, Finsupp.mapDomain_notin_range, Finsupp.single_eq_same, true_and]
            at hdeg
          exact (le_add_left le_rfl).trans hdeg
        · exact (hd this.symm).elim
      refine ⟨n - w i, ih.mpr ?_, (Nat.sub_add_cancel hn0).symm⟩
      rw [← Nat.sub_add_cancel hn0] at hp
      apply mul_X_pow_cancel (i := none) (n := w i)
      apply mul_X_cancel (i := some i)
      simp only [_root_.map_mul, rename_X, aeval_X, Nat.succ_eq_add_one, Option.elim_some] at hp
      rw [pow_add, mul_assoc, mul_left_comm (X none ^ _), ← mul_assoc] at hp
      rw [hp]
      ring
    · assumption

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul' {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p n ↔ MvPolynomial.aeval (fun i => X none * X i) (rename some p) =
      X none ^ n * rename some p := by
  classical
  induction p using MvPolynomial.induction_on'' generalizing n
  case h_C a =>
    rw [isHomogeneous_C_iff]
    constructor
    · rintro (rfl | rfl)
      · simp
      · simp
    · rw [algHom_C, algebraMap_eq, aeval_C, algebraMap_eq, or_iff_not_imp_right]
      intro h hn
      have h := congr_arg (coeff (Finsupp.single none n)) h.symm
      rwa [coeff_C, mul_comm, coeff_C_mul, coeff_X_pow, if_pos rfl, if_neg, mul_one] at h
      · rwa [eq_comm, Finsupp.single_eq_zero]
  case h_add_weak x a p hx ha ih_r ih_l =>
    -- simp? [rename_monomial, aeval_monomial] at *
    simp only at *
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
    have disj : Disjoint ((monomial x) a).support (support p) := by simpa [support_monomial, ha]
    constructor
    · intro h
      have ih_l' := ih_l.mp (MvPolynomial.isHomogeneous_left_of_add_of_disjoint h disj)
      have ih_r' := ih_r.mp (MvPolynomial.isHomogeneous_right_of_add_of_disjoint h disj)
      simp only [map_add, ih_l', ih_r', mul_add]
    · intro h
      rw [map_add, map_add, mul_add] at h
      have disj_lhs := disjoint_support_aeval_X_mul none
        (disjoint_support_rename _ (Option.some_injective _) disj)
      have disj_rhs := disjoint_support_X_pow_mul none n
        (disjoint_support_rename _ (Option.some_injective _) disj)

      have h_l : ∀ (d : Option σ →₀ ℕ),
          coeff d ((aeval fun i ↦ X none * X i) (rename some (monomial x a))) =
          coeff d (X none ^ n * rename some (monomial x a)) := by
        intro d
        obtain (hdl | hdl) := coeff_zero_or_zero_of_disjoint_support d disj_lhs <;>
            obtain (hdr | hdr) := coeff_zero_or_zero_of_disjoint_support d disj_rhs
        · rw [hdl, hdr]
        · have h := (ext_iff _ _).mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdl, ← h]
          simp only [coeff_aeval_X_mul', coeff_X_pow_mul'] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hdeg hn
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (Ne.symm hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ (h.symm.trans_ne (Ne.symm hp))
            have : degree d / 2 = d none := le_antisymm hdeg.2 <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu')))
          · rw [h]
          · rfl
          · rfl
        -- TODO: this next block is almost the same as the previous one.
        · have h := (ext_iff _ _).mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdr, h]
          simp only [coeff_aeval_X_mul', coeff_X_pow_mul'] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hn hdeg
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (h.trans_ne hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ hp
            have : degree d / 2 = d none := le_antisymm hdeg.2 <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu' (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu)))
          · rw [h]
          · rfl
          · rfl
        · simpa [hdl, hdr, -aeval_eq_bind₁] using (ext_iff _ _).mp h d
      refine IsHomogeneous.add
          (ih_l.mpr ((ext_iff _ _).mpr h_l))
          (ih_r.mpr ((ext_iff _ _).mpr fun d => ?_))
      have h := (ext_iff _ _).mp h d
      rw [coeff_add, h_l] at h
      exact add_left_cancel h
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0, -aeval_eq_bind₁] using isHomogeneous_zero _ _ _
    rw [isHomogeneous_mul_X_iff]
    constructor
    · rintro ⟨m, hp, rfl⟩
      simp [ih.mp hp, -aeval_eq_bind₁]
      ring
    · intro hp
      have hn0 : n ≠ 0 := by
        rintro rfl
        apply hp0
        apply rename_injective _ (Option.some_injective _)
        apply aeval_X_mul_injective
        rw [MvPolynomial.ext_iff] at hp ⊢
        intro d
        rw [map_zero, map_zero, coeff_zero]
        specialize hp (d + Finsupp.single none 1 + Finsupp.single (some i) 1)
        rw [_root_.map_mul, _root_.map_mul, rename_X, aeval_X, ← mul_assoc, coeff_mul_X,
            coeff_mul_X, pow_zero, one_mul, coeff_mul_X] at hp
        rw [hp, ← not_mem_support_iff, support_rename_of_injective (Option.some_injective _),
            Finset.mem_image, not_exists]
        simp only [not_and]
        intro x _ h
        have := DFunLike.congr_fun h none
        rw [Finsupp.mapDomain_notin_range] at this
        simp at this
        · rintro ⟨x, ⟨⟩⟩
      refine ⟨n.pred, ih.mpr ?_, (Nat.succ_pred_eq_of_ne_zero hn0).symm⟩
      rw [← Nat.succ_pred_eq_of_ne_zero hn0] at hp
      set m := n.pred
      apply mul_X_cancel (i := none)
      apply mul_X_cancel (i := some i)
      simp only [_root_.map_mul, rename_X, aeval_X, Nat.succ_eq_add_one] at hp
      rwa [pow_succ, mul_assoc, mul_left_comm (X none), ← mul_assoc, ← mul_assoc, ← mul_assoc]
        at hp
    · assumption

/-- A weighted homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p n ↔ MvPolynomial.aeval (fun i => X none ^ w i * X (some i)) p =
      X none ^ n * rename some p := by
  rw [isWeightedHomogeneous_iff_comp_smul_eq_pow_smul', aeval_rename]
  rfl

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p n ↔ MvPolynomial.aeval (fun i => X none * X (some i)) p =
      X none ^ n * rename some p := by
  rw [isHomogeneous_iff_comp_smul_eq_pow_smul', aeval_rename]
  rfl

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isWeightedHomogeneous_iff_eval_smul_eq_pow_smul [Infinite R] [IsDomain R]
    {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p n ↔ ∀ x (f : σ → R),
      MvPolynomial.eval (fun i => x ^ w i * f i) p = x ^ n * eval f p := by
  refine isWeightedHomogeneous_iff_comp_smul_eq_pow_smul.trans ⟨fun h x f => ?_, fun h => ?_⟩
  · have h := congr_arg (eval (fun i => Option.elim i x f)) h
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, Option.elim_none, Option.elim_some,
        coe_eval₂Hom, map_pow, eval_rename] at h
    rw [← eval₂_id]
    convert h
    ext y
    simp
  · apply MvPolynomial.eq_of_eval_eq
    intro x
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, coe_eval₂Hom, map_pow, eval_rename]
    convert (eval₂_id _).trans (h (x none) (x ∘ some))
    ext
    simp

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isHomogeneous_iff_eval_smul_eq_pow_smul [Infinite R] [IsDomain R]
    {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p n ↔ ∀ x f, MvPolynomial.eval (x • f) p = x ^ n * eval f p := by
  refine isHomogeneous_iff_comp_smul_eq_pow_smul.trans ⟨fun h x f => ?_, fun h => ?_⟩
  · have h := congr_arg (eval (fun i => Option.elim i x f)) h
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, Option.elim_none, Option.elim_some,
        coe_eval₂Hom, map_pow, eval_rename] at h
    rw [← eval₂_id]
    convert h
    ext y
    simp
  · apply MvPolynomial.eq_of_eval_eq
    intro x
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, coe_eval₂Hom, map_pow, eval_rename]
    convert (eval₂_id _).trans (h (x none) (x ∘ some))
    ext
    simp

theorem MvPolynomial.IsHomogeneous.of_mul_left [IsDomain R] {σ : Type*} {p q : MvPolynomial σ R}
    (hq : IsHomogeneous q n) (hpq : IsHomogeneous (p * q) (m + n)) (hq0 : q ≠ 0) :
    IsHomogeneous p m := by
  rw [MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hq] at hpq
  exact mul_right_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hq0)) hpq

theorem MvPolynomial.IsWeightedHomogeneous.of_mul_right [IsDomain R] {σ : Type*} {p q : MvPolynomial σ R}
    {w : σ → ℕ}
    (hp : IsWeightedHomogeneous w p m) (hpq : IsWeightedHomogeneous w (p * q) (m + n)) (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w q n := by
  rw [MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hp] at hpq
  exact mul_left_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hp0)) hpq

theorem MvPolynomial.IsHomogeneous.of_mul_right [IsDomain R] {σ : Type*} {p q : MvPolynomial σ R}
    (hp : IsHomogeneous p m) (hpq : IsHomogeneous (p * q) (m + n)) (hp0 : p ≠ 0) :
    IsHomogeneous q n := by
  rw [MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hp] at hpq
  exact mul_left_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hp0)) hpq

theorem MvPolynomial.isHomogeneous_esymm {σ : Type*} [Fintype σ] {n : ℕ} :
    IsHomogeneous (esymm σ R n) n :=
  IsHomogeneous.sum _ _ _ (fun i hi => by
    simpa [(Finset.mem_powersetCard.mp hi).2]
      using IsHomogeneous.prod (R := R) i X 1 (fun t _ => isHomogeneous_X _ _))

/-- The total degree is zero exactly for the constant polynomials. -/
lemma MvPolynomial.weightedTotalDegree_eq_zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R}
    {w : σ → ℕ} (hw : NonTorsionWeight w) :
    weightedTotalDegree w P = 0 ↔ ∃ x, P = C x := by
  simp only [weightedTotalDegree_eq_zero_iff hw, mem_support_iff]
  constructor
  · rintro hdeg
    use constantCoeff P
    ext x
    by_cases hx : x = 0
    · simp [hx, constantCoeff_eq]
    · classical
      rw [coeff_C, if_neg (Ne.symm hx)]
      contrapose! hx
      ext
      exact hdeg _ hx _
  · rintro ⟨x, rfl⟩ m hm i
    classical
    simp only [coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp] at hm
    simp [← hm.1]

/-- The total degree is zero exactly for the constant polynomials. -/
lemma MvPolynomial.totalDegree_eq_zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R} :
    totalDegree P = 0 ↔ ∃ x, P = C x := by
  constructor
  · rintro hdeg
    use constantCoeff P
    ext x
    by_cases hx : x = 0
    · simp [hx, constantCoeff_eq]
    · classical
      rw [coeff_C, if_neg (Ne.symm hx), coeff_eq_zero_of_totalDegree_lt]
      · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hx
        rw [hdeg]
        refine Finset.sum_pos' (fun _ _ => zero_le _)
          ⟨i, Finsupp.mem_support_iff.mpr hi, Nat.pos_of_ne_zero hi⟩
  · rintro ⟨x, rfl⟩
    exact totalDegree_C _

/-- A homogeneous polynomial has degree zero if and only if it's constant. -/
lemma MvPolynomial.IsWeightedHomogeneous.zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R}
    {w : σ → ℕ} (hw : NonTorsionWeight w)
    (hP : IsWeightedHomogeneous w P n) (hP0 : P ≠ 0) : n = 0 ↔ ∃ x, P = C x := by
  refine Iff.trans ?_ (weightedTotalDegree_eq_zero_iff_exists_C hw)
  constructor
  · rintro rfl
    rwa [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]
  · intro h
    exact IsWeightedHomogeneous.inj_right hP0 hP (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero.mpr h)

/-- A homogeneous polynomial has degree zero if and only if it's constant. -/
lemma MvPolynomial.IsHomogeneous.zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R}
    (hP : IsHomogeneous P n) (hP0 : P ≠ 0) : n = 0 ↔ ∃ x, P = C x := by
  refine Iff.trans ?_ totalDegree_eq_zero_iff_exists_C
  constructor
  · rintro rfl
    rwa [totalDegree_zero_iff_isHomogeneous]
  · intro h
    exact IsHomogeneous.inj_right hP ((totalDegree_zero_iff_isHomogeneous _).mp h) hP0

/-- Two multivariate polynomials that are homogeneous of the same degree and divide each other,
are equal up to constants. -/
lemma MvPolynomial.IsWeightedHomogeneous.exists_C_mul_eq_of_dvd [IsDomain R] {σ : Type*}
    {w : σ → ℕ} (hw : NonTorsionWeight w)
    {P Q : MvPolynomial σ R} (hP : P.IsWeightedHomogeneous w n) (hQ : Q.IsWeightedHomogeneous w n)
    (hdvd : P ∣ Q) :
    ∃ c, C c * P = Q := by
  obtain ⟨R, rfl⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hR0 : R = 0
  · use 0
    simp [hR0]
  obtain ⟨x, rfl⟩ : ∃ x, R = C x :=
    ((IsWeightedHomogeneous.of_mul_right hP (by simpa) hP0).zero_iff_exists_C hw hR0).mp rfl
  exact ⟨x, mul_comm _ _⟩

/-- Two multivariate polynomials that are homogeneous of the same degree and divide each other,
are equal up to constants. -/
lemma MvPolynomial.IsHomogeneous.exists_C_mul_eq_of_dvd [IsDomain R] {σ : Type*}
    {P Q : MvPolynomial σ R} (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous n) (hdvd : P ∣ Q) :
    ∃ c, C c * P = Q := by
  obtain ⟨R, rfl⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hR0 : R = 0
  · use 0
    simp [hR0]
  obtain ⟨x, rfl⟩ : ∃ x, R = C x :=
    ((IsHomogeneous.of_mul_right hP (by simpa) hP0).zero_iff_exists_C hR0).mp rfl
  exact ⟨x, mul_comm _ _⟩

theorem MvPolynomial.eval_bind₁ {σ τ : Type*} (f : τ → R) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval f (bind₁ g φ) = eval (fun i => eval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _

lemma MvPolynomial.IsWeightedHomogeneous.bind₁ {σ τ : Type*} {w₁ : σ → ℕ} {w₂ : τ → ℕ}
    {P : MvPolynomial σ R} {Q : σ → MvPolynomial τ R}
    (hP : P.IsWeightedHomogeneous w₁ m) (hQ : ∀ i, (Q i).IsWeightedHomogeneous w₂ (w₁ i * n)) :
    (bind₁ Q P).IsWeightedHomogeneous w₂ (m * n) := by
  induction P using MvPolynomial.induction_on'' generalizing m
  case h_C a =>
    obtain (rfl | rfl) := isWeightedHomogeneous_C_iff.mp hP
    · simpa using isWeightedHomogeneous_zero _ _ _
    · simpa using isWeightedHomogeneous_C _ a
  case h_add_weak a b f ha hb ih_r ih_l =>
    simp only at *
    rw [map_add]
    have : Disjoint ((monomial a) b).support (support f) := by
      classical
      simpa [support_monomial, hb] using ha
    exact (ih_l (isWeightedHomogeneous_left_of_add_of_disjoint hP this)).add
      (ih_r (MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint hP this))
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0] using isWeightedHomogeneous_zero _ _ _
    obtain ⟨m, hp, rfl⟩ := (isWeightedHomogeneous_mul_X_iff hp0).mp hP
    rw [_root_.map_mul, bind₁_X_right, add_mul]
    exact (ih hp).mul (hQ _)

lemma MvPolynomial.IsWeightedHomogeneous.bind₁' {σ τ : Type*} {w₁ n : σ → ℕ} {w₂ : τ → ℕ}
    {P : MvPolynomial σ R} {Q : σ → MvPolynomial τ R}
    (hP : P.IsWeightedHomogeneous w₁ m) (hQ : ∀ i, (Q i).IsWeightedHomogeneous w₂ (w₁ i * n i)) :
    (MvPolynomial.bind₁ Q P).IsWeightedHomogeneous w₂ (m * sorry) := by
  induction P using MvPolynomial.induction_on'' generalizing m
  case h_C a =>
    obtain (rfl | rfl) := isWeightedHomogeneous_C_iff.mp hP
    · simpa using isWeightedHomogeneous_zero _ _ _
    · simpa using isWeightedHomogeneous_C (M := ℕ) _ a
  case h_add_weak a b f ha hb ih_r ih_l =>
    simp only at *
    rw [map_add]
    have : Disjoint ((monomial a) b).support (support f) := by
      classical
      simpa [support_monomial, hb] using ha
    exact (ih_l (isWeightedHomogeneous_left_of_add_of_disjoint hP this)).add
      (ih_r (MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint hP this))
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0] using isWeightedHomogeneous_zero _ _ _
    obtain ⟨m, hp, rfl⟩ := (isWeightedHomogeneous_mul_X_iff hp0).mp hP
    rw [_root_.map_mul, bind₁_X_right, add_mul]
    exact (ih hp).mul (hQ _)

/-
/-- Two multivariate polynomials that are homogeneous of the same degree and divide each other,
are equal up to constants. -/
lemma MvPolynomial.IsHomogeneous.exists_C_mul_bind_eq_of_bind_dvd [IsDomain R] {σ τ : Type*}
    {P Q : MvPolynomial σ R} (S : σ → MvPolynomial τ R)
    (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous n) (hdvd : bind₁ S P ∣ bind₁ S Q) :
    ∃ c, C c * bind₁ S P = bind₁ S Q := by
  obtain ⟨R, SQ⟩ := hdvd
  rw [SQ]
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hR0 : R = 0
  · use 0
    simp [hR0]
  obtain ⟨x, rfl⟩ : ∃ x, R = C x :=
    sorry -- ((IsHomogeneous.of_mul_right hP (by simpa) hP0).zero_iff_exists_C hR0).mp rfl
  exact ⟨x, mul_comm _ _⟩

/-- Two multivariate polynomials are equal up to a constant if one divides the other,
and we can transform them into homogeneous polynomials on a partition of the variables. -/
lemma MvPolynomial.exists_C_mul_eq_of_dvd_of_homogeneous_left_of_homogeneous_right
    [IsDomain R] {σ σ' τ τ' : Type*} (P Q : MvPolynomial (σ ⊕ τ) R)
    (hdvd : P ∣ Q)
    (Pl Ql : (τ → R) → MvPolynomial σ' R) (Pr Qr : (σ → R) → MvPolynomial τ' R)
    (v : σ' → MvPolynomial σ R) (w : τ' → MvPolynomial τ R)
    (hPl : ∀ u, (Pl u).IsHomogeneous n) (hQl : ∀ u, (Ql u).IsHomogeneous n)
    (hPr : ∀ t, (Pr t).IsHomogeneous m) (hQr : ∀ t, (Qr t).IsHomogeneous m)
    (hPPl : ∀ t u, eval (Sum.elim t u) P = eval (eval t ∘ v) (Pl u))
    (hPPr : ∀ t u, eval (Sum.elim t u) P = eval (eval u ∘ w) (Pr t))
    (hQQl : ∀ t u, eval (Sum.elim t u) Q = eval (eval t ∘ v) (Ql u))
    (hQQr : ∀ t u, eval (Sum.elim t u) Q = eval (eval u ∘ w) (Qr t)) :
    ∃ c, C c * P = Q := by
  sorry
-/

lemma MvPolynomial.irreducible_X_sub_X {σ : Type*} {i j : σ} (hij : i ≠ j) :
    Irreducible (X i - X j : MvPolynomial σ R) := by
  rw [irreducible_iff]
  sorry

lemma MvPolynomial.isRelPrime_X_sub_X_of_ne_left [IsDomain R] {σ : Type*}
    {i i' j j' : σ} (hi : i ≠ i') (hij : i ≠ j) (hij' : i' ≠ j') :
    IsRelPrime (X i - X j : MvPolynomial σ R) (X i' - X j') := by
  refine (MvPolynomial.irreducible_X_sub_X hij).isRelPrime_iff_not_dvd.mpr (mt (fun h => ?_) hi)
  obtain ⟨c, hc⟩ := ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)).exists_C_mul_eq_of_dvd
    ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)) h
  sorry

lemma MvPolynomial.isRelPrime_X_sub_X_of_ne_right [IsDomain R] {σ : Type*}
    {i i' j j' : σ} (hij : i ≠ j) (hij' : i' ≠ j') (hj : j ≠ j') :
    IsRelPrime (X i - X j : MvPolynomial σ R) (X i' - X j') := by
  rw [← IsRelPrime.neg_left_iff, ← IsRelPrime.neg_right_iff, neg_sub, neg_sub]
  exact isRelPrime_X_sub_X_of_ne_left hj hij.symm hij'.symm

noncomputable def Polynomial.ofVec (v : Fin m → R) : R[X] :=
  ∑ i, C (v i) * X^(i : ℕ)

@[simp] lemma Polynomial.coeff_ofVec (v : Fin m → R) (i : ℕ) :
    (ofVec v).coeff i = if hi : i < m then v ⟨i, hi⟩ else 0 := by
  simp only [ofVec, finset_sum_coeff]
  split_ifs with hi
  · simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨i, hi⟩, if_pos rfl]
    · intro b _ hb
      exact if_neg (fun hi => hb (by simp [hi]))
    · simp
  · simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    convert Finset.sum_const_zero
    rw [if_neg]
    rintro rfl
    exact hi (Fin.prop _)

@[simp] lemma Polynomial.ofVec_one {v : Fin 1 → R} : ofVec v = C (v 0) := by
  ext i
  cases i
  · simp
  · simp

@[simp] lemma Polynomial.natDegree_ofVec {v : Fin (m + 1) → R} (h : v (Fin.last _) ≠ 0) :
    natDegree (ofVec v) = m := by
  by_cases hm : m = 0
  · subst hm
    simp
  rw [ofVec, Fin.sum_univ_castSucc, natDegree_add_eq_right_of_natDegree_lt, natDegree_C_mul_X_pow,
      Fin.val_last]
  · assumption
  · refine (natDegree_sum_le _ _).trans_lt ?_
    rw [natDegree_C_mul_X_pow _ _ h, Fin.val_last, Finset.fold_max_lt]
    refine ⟨Nat.pos_iff_ne_zero.mpr hm, fun i _ => (natDegree_C_mul_X_pow_le _ _).trans_lt ?_⟩
    exact i.prop

lemma isPolynomial_ofVec (i : ℕ) :
    IsPolynomial (fun (v : Fin m → R) => (ofVec v).coeff i) := by
  simp only [coeff_ofVec]
  split_ifs with hi
  · simpa using IsPolynomial.apply_const (R := R) (⟨i, hi⟩ : Fin m)
  · exact IsPolynomial.const 0

lemma isPolynomial_ofVec_snoc {x : R} (i : ℕ) :
    IsPolynomial (fun (v : Fin m → R) => (ofVec (Fin.snoc v x)).coeff i) := by
  simp only [coeff_ofVec, Fin.snoc]
  split_ifs with hi_succ hi
  · simpa using IsPolynomial.apply_const (R := R) (⟨i, hi⟩ : Fin m)
  · have hi_eq : i = m := le_antisymm (Nat.lt_succ.mp hi_succ) (le_of_not_gt hi)
    subst hi_eq
    exact IsPolynomial.const x
  · exact IsPolynomial.const 0

@[simp] lemma Polynomial.ofVec_smul (v : Fin m → R) (x : R) : ofVec (x • v) = x • ofVec v := by
  ext i
  rw [coeff_ofVec, coeff_smul, coeff_ofVec]
  split_ifs <;> simp

@[simp] lemma Polynomial.ofVec_const_mul (v : Fin m → R) (x : R) : ofVec (fun i => x * v i) =
    C x * ofVec v := by
  ext i
  rw [coeff_ofVec, coeff_C_mul, coeff_ofVec]
  split_ifs <;> simp

lemma prod_eval_prod_X_sub_C {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ι → K) (u : κ → K) :
    ∏ i, (∏ j, (X - C (u j))).eval (t i) = ∏ i, ∏ j, (t i - u j) :=
  Finset.prod_congr rfl (fun i _ => (by simp only [eval_prod, eval_sub, eval_X, eval_C]))

/-- We can express each coefficient of a polynomial in terms of its roots. -/
noncomputable def coeffOfRoots {ι : Type*} [Fintype ι] (i : Fin (Fintype.card ι)) :
    MvPolynomial ι K :=
  (-1) ^ (Fintype.card ι - ↑i) * MvPolynomial.esymm _ _ (Fintype.card ι - i)

theorem MvPolynomial.eval_esymm_eq_multiset_esymm {σ : Type*} [Fintype σ] (f : σ → R) (n : ℕ) :
    eval f (esymm σ R n) = (Finset.univ.val.map f).esymm n :=
  aeval_esymm_eq_multiset_esymm _ _ _ _

lemma MvPolynomial.eval_coeffOfRoots {ι : Type*} [Fintype ι] (t : ι → K) (i : Fin (Fintype.card ι)) :
    MvPolynomial.eval t (coeffOfRoots i) = Polynomial.coeff (∏ i, (Polynomial.X - Polynomial.C (t i))) i := by
  conv_rhs =>
    rw [← one_mul (∏ _, _), ← _root_.map_one Polynomial.C,
        coeff_eq_esymm_roots_of_splits (splits_C_mul_prod_X_sub_C t _ _)]
    · rfl
    · exact i.prop.le.trans_eq (natDegree_C_mul_prod_X_sub_C _ _ one_ne_zero).symm
  rw [coeffOfRoots, _root_.map_mul, eval_esymm_eq_multiset_esymm]
  simp

lemma ofVec_coeffOfRoots_one {ι : Type*} [Fintype ι] (t : ι → K) :
    ofVec (Fin.snoc (fun i => MvPolynomial.eval t (coeffOfRoots i)) 1) = ∏ i, (X - C (t i)) := by
  ext i
  rw [coeff_ofVec]
  split_ifs with hi
  · conv_rhs => rw [← Fin.val_mk hi]
    cases hi
    case pos.refl =>
      exact (Fin.snoc_last _ _).trans (coeff_prod_X_sub_C_card t Finset.univ).symm
    case pos.step h =>
      exact (Fin.snoc_castSucc _ _ ⟨i, h⟩).trans (MvPolynomial.eval_coeffOfRoots t ⟨i, h⟩)
  · exact (coeff_eq_zero_of_natDegree_lt ((natDegree_prod_X_sub_C t _).trans_lt (lt_of_not_ge (mt Nat.lt_succ.mpr hi)))).symm

lemma ofVec_coeffOfRoots_smul {ι : Type*} [Fintype ι] (x : K) (t : ι → K) :
    ofVec (Fin.snoc (fun i => MvPolynomial.eval t (x • coeffOfRoots i)) x) = C x * ∏ i, (X - C (t i)) := by
  ext i
  rw [coeff_ofVec]
  split_ifs with hi
  · conv_rhs => rw [← Fin.val_mk hi]
    cases hi
    case pos.refl =>
      exact (Fin.snoc_last _ _).trans (coeff_C_mul_prod_X_sub_C_card t Finset.univ x).symm
    case pos.step h =>
      refine (Fin.snoc_castSucc _ _ ⟨i, h⟩).trans ?_
      simp only [MvPolynomial.smul_eval, coeff_C_mul, mul_eq_mul_left_iff]
      rw [(MvPolynomial.eval_coeffOfRoots t ⟨i, h⟩)]
      exact Or.inl rfl
  · exact (coeff_eq_zero_of_natDegree_lt ((natDegree_C_mul_prod_X_sub_C_le t _ _).trans_lt
            (lt_of_not_ge (mt Nat.lt_succ.mpr hi)))).symm

lemma coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) (t : ι → K) j :
    (∏ i in s, (X - C (t i))).coeff j =
      if j ≤ s.card
      then (-1) ^ (s.card - j) * ∑ t_1 ∈ Finset.powersetCard (s.card - j) s, t_1.prod t
      else 0 := by
  split_ifs with hj
  · convert coeff_eq_esymm_roots_of_splits (splits_prod_X_sub_C t _) (hj.trans_eq (natDegree_prod_X_sub_C t _).symm)
    · simp
    · simp [Finset.esymm_map_val]
  · exact coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_prod_X_sub_C, ← not_le])

lemma MvPolynomial.isWeightedHomogeneous_coeffOfRoots {ι : Type*} [Fintype ι] [Infinite K] (i) :
    IsWeightedHomogeneous (fun (_ : ι) => 1) (coeffOfRoots (K := K) i) (Fintype.card ι - (i : ℕ)) :=
  isWeightedHomogeneous_iff_eval_smul_eq_pow_smul.mpr fun c f => by
    simp only [eval_coeffOfRoots, coeff_prod_X_sub_C, Finset.card_univ, Fin.is_le', ↓reduceIte,
      pow_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.mul_sum, mul_left_comm]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [(Finset.mem_powersetCard.mp hs).2]

/-- The resultant as a multivariate polynomial in the coefficients of two polynomials.

Note that this only equals the actual resultant if the leading coefficients are nonzero.
-/
noncomputable def resultantPolynomialCoeff :
    MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) K :=
  MvPolynomial.bind₁
    (fun ij => sylvesterMatrixVec (fun i => MvPolynomial.X (Sum.inr i)) (fun i => MvPolynomial.X (Sum.inl i)) ij.1 ij.2)
    MvPolynomial.det
  /-
  Classical.choose (IsPolynomial.resultant
    (P := fun (v : Fin m → K) => ofVec (Fin.snoc v 1))
    (Q := fun (w : Fin n → K) => ofVec (Fin.snoc w 1))
    (fun v => natDegree_ofVec (by simp))
    (fun w => natDegree_ofVec (by simp))
    isPolynomial_ofVec_snoc
    isPolynomial_ofVec_snoc)
  -/

@[simp] lemma Polynomial.toVec_ofVec (v : Fin (m + 1) → R) (h : v (Fin.last m) ≠ 0) :
    toVec (ofVec v) = v ∘ Fin.cast (congr_arg (· + 1) (natDegree_ofVec h)) := by
  ext ⟨i, hi⟩
  rw [natDegree_ofVec h] at hi
  simp [toVec, hi]

@[simp] lemma MvPolynomial.aeval_sylvesterVec {ι S : Type*} [CommRing S] [Algebra R S]
    (v : Fin (n + 1) → MvPolynomial ι R) (t : ι → S) (i : Fin m) (j) :
    MvPolynomial.aeval t (sylvesterVec v i j) =
      sylvesterVec (fun i => aeval t (v i)) i j := by
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    simp [sylvesterVec_of_lt _ _ _ h]
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) n
    case inl h₂ =>
      simp [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
    case inr h₂ =>
      simp [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]

@[simp] lemma MvPolynomial.aeval_sylvesterMatrixVec {ι S : Type*} [CommRing S] [Algebra R S]
    (v : Fin (m + 1) → MvPolynomial ι R) (w : Fin (n + 1) → MvPolynomial ι R)
    (t : ι → S) (i j) :
    MvPolynomial.aeval t (sylvesterMatrixVec v w i j) =
      sylvesterMatrixVec (fun i => aeval t (v i)) (fun j => aeval t (w j)) i j := by
  unfold sylvesterMatrixVec
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [sylvesterMatrixVec]
  · simp [sylvesterMatrixVec]

@[simp] lemma MvPolynomial.eval_sylvesterMatrixVec {ι : Type*}
    (v : Fin (m + 1) → MvPolynomial ι R) (w : Fin (n + 1) → MvPolynomial ι R)
    (t : ι → R) (i j) :
    MvPolynomial.eval t (sylvesterMatrixVec v w i j) =
      sylvesterMatrixVec (fun i => eval t (v i)) (fun j => eval t (w j)) i j :=
  aeval_sylvesterMatrixVec v w t i j

@[simp] lemma MvPolynomial.eval_resultantPolynomialCoeff
    (tu : (Fin (m + 1) ⊕ Fin (n + 1)) → K)
    (hl : tu (Sum.inl (Fin.last m)) ≠ 0) (hr : tu (Sum.inr (Fin.last n)) ≠ 0) :
    MvPolynomial.eval tu resultantPolynomialCoeff =
    (ofVec (fun i => tu (Sum.inl i))).resultant (ofVec (fun i => tu (Sum.inr i))) := by
  rw [resultantPolynomialCoeff, eval_bind₁, eval_det',
    resultant_eq_det_sylvesterMatrixVec_cast _ _ (natDegree_ofVec hl) (natDegree_ofVec hr)]
  congr 1
  ext i j
  rw [toVec_ofVec _ hr, toVec_ofVec _ hl, of_apply, eval_sylvesterMatrixVec]
  congr <;>
  · ext
    apply eval_X

lemma MvPolynomial.isWeightedHomogeneous_resultantPolynomialCoeff [Infinite K] :
    IsWeightedHomogeneous (Sum.elim (fun (_ : Fin (m + 1)) => (m + 1)) (fun (_ : Fin (n + 1)) => (n + 1)))
      (resultantPolynomialCoeff (K := K)) (n * (m + 1) + m * (n + 1)) :=
  isWeightedHomogeneous_iff_eval_smul_eq_pow_smul.mpr fun c f => by
    -- Note that we can't quite reuse the theorem about the resultant function being homogeneous,
    -- since we also need to care about the case where the leading coefficient is zero.
    calc
    _ = (of fun i j ↦ sylvesterMatrixVec (c ^ (n + 1) • fun i ↦ f (Sum.inr i)) (c ^ (m + 1) • fun j ↦ f (Sum.inl j)) i j).det := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [-sylvesterMatrixVec_smul, -smul_sylvesterMatrixVec]
      rfl
    _ = c ^ ((m + 1) * n) * (c ^ ((n + 1) * m) * (of fun i j ↦ sylvesterMatrixVec (fun i ↦ f (Sum.inr i)) (fun j ↦ f (Sum.inl j)) i j).det) := by
      rw [sylvesterMatrixVec_smul, smul_sylvesterMatrixVec]
      simp only [of_apply]
      convert det_mul_row _ _ using 2
      · simp [Fin.prod_univ_add, pow_mul]
      · convert (det_mul_row (Fin.addCases (fun _ => c ^ (n + 1)) (fun _ => 1)) _).symm using 2
        · simp [Fin.prod_univ_add, pow_mul]
    _ = _ := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [mul_assoc, pow_add, mul_comm, mul_left_comm]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem MvPolynomial.IsWeightedHomogeneous.rename {σ τ : Type*}
    {f : σ → τ} {w₁ : σ → ℕ} {w₂ : τ → ℕ} {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w₁ p n)
    (hw : ∀ i, w₂ (f i) = w₁ i) :
    IsWeightedHomogeneous w₂ (rename f p) n := by
  rw [← p.support_sum_monomial_coeff, map_sum]
  simp_rw [rename_monomial]
  apply IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ isWeightedHomogeneous_monomial _ _ _ _
  intro d hd
  simp [hw, h (mem_support_iff.mp hd)]

@[simp] lemma MvPolynomial.eval_snoc (t : ι → R) (v : Fin m → MvPolynomial ι R) (x : MvPolynomial ι R) (i) :
    eval t (Fin.snoc (α := fun _ => MvPolynomial ι R) v x i) =
    Fin.snoc (α := fun _ => R) (fun i => eval t (v i)) (eval t x) i := by
  sorry

/-- The resultant as a multivariate polynomial in the roots of two monic polynomials. -/
noncomputable def resultantPolynomialRoots : MvPolynomial (ι ⊕ κ) K :=
  MvPolynomial.bind₁ (Sum.elim
      (Fin.snoc (fun i => MvPolynomial.rename Sum.inl (coeffOfRoots i)) 1)
      (Fin.snoc (fun i => MvPolynomial.rename Sum.inr (coeffOfRoots i)) 1))
    resultantPolynomialCoeff

@[simp] lemma MvPolynomial.eval_resultantPolynomialRoots (tu : ι ⊕ κ → K) :
    MvPolynomial.eval tu resultantPolynomialRoots =
    (∏ i, (Polynomial.X - Polynomial.C (tu (Sum.inl i)))).resultant
      (∏ i, (Polynomial.X - Polynomial.C (tu (Sum.inr i)))) := by
  simp [resultantPolynomialRoots, eval_bind₁, eval_resultantPolynomialCoeff, eval_rename,
    Function.comp, ofVec_coeffOfRoots_one]

lemma MvPolynomial.isWeightedHomogeneous_resultantPolynomialRoots [Infinite K] :
    IsWeightedHomogeneous (Sum.elim (fun (i : ι) => 1) (fun (_ : κ) => 1))
      (resultantPolynomialRoots (K := K))
        ((Fintype.card κ * (Fintype.card ι + 1) + Fintype.card ι * (Fintype.card κ + 1)) * _) :=
  isWeightedHomogeneous_resultantPolynomialCoeff.bind₁ fun i => by
    obtain (i | i) := i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Sum.elim_lam_const_lam_const, Sum.elim_inl, Fin.snoc_last]
      · simp?
        convert (isWeightedHomogeneous_coeffOfRoots (K := K) i).rename (fun _ => ?_) using 1
        · sorry
        · rfl
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp?
      · simp?

theorem prod_root_differences_dvd_resultantPolynomialRoots [DecidableEq ι] [DecidableEq κ] [Infinite K] :
    ∏ (i : ι), ∏ (j : κ), (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr j)) ∣
      (resultantPolynomialRoots (K := K)) :=
    Finset.prod_dvd_of_isRelPrime
      (fun i _ j _ hij => IsRelPrime.prod_left fun i' _ => IsRelPrime.prod_right fun j' _ =>
        MvPolynomial.isRelPrime_X_sub_X_of_ne_left
          (Sum.inl_injective.ne hij)
          Sum.inl_ne_inr
          Sum.inl_ne_inr)
      (fun i _ => Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij =>
        MvPolynomial.isRelPrime_X_sub_X_of_ne_right
          Sum.inl_ne_inr
          Sum.inl_ne_inr
          (Sum.inr_injective.ne hij))
        (fun j _ => MvPolynomial.X_sub_X_dvd_of_eval_eq_zero _ (fun tu hij => by
          rw [MvPolynomial.eval_resultantPolynomialRoots, resultant_eq_zero_of_root]
          · exact prod_X_sub_C_ne_zero _ _
          · exact isRoot_prod_X_sub_C.mpr ⟨i, Finset.mem_univ _, rfl⟩
          · exact isRoot_prod_X_sub_C.mpr ⟨j, Finset.mem_univ _, hij⟩)))

lemma Polynomial.eval_prod_X_sub_C {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → K) (u : κ → K) (i : ι) :
    (∏ j, (X - C (u j))).eval (t i) = ∏ j, (t i - u j) := by
  simp only [eval_prod, eval_sub, eval_X, eval_C]

lemma Polynomial.prod_eval_prod_X_sub_C {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → K) (u : κ → K) :
    ∏ i, (∏ j, (X - C (u j))).eval (t i) = ∏ i, ∏ j, (t i - u j) :=
  Finset.prod_congr rfl (fun i _ => (by simp only [eval_prod, eval_sub, eval_X, eval_C]))

lemma MvPolynomial.eval_prod_prod_X_sub_C {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → K) (u : κ → K) :
    MvPolynomial.eval t (∏ i, (∏ j, (X i - C (u j)))) = ∏ i, ∏ j, (t i - u j) := by
  rw [eval_prod, Fintype.prod_congr]
  · intro i
    simp only [eval_prod, eval_sub, eval_X, eval_C]

lemma MvPolynomial.eval_prod_prod_X_sub_C' {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → K) (u : κ → K) (i : ι) :
    ∏ x : κ, (t i - u x) = (MvPolynomial.eval (MvPolynomial.eval u ∘ (Fin.snoc coeffOfRoots 1)))
      (∑ j : Fin (_ + 1), MvPolynomial.C (t i ^ (j : ℕ)) * MvPolynomial.X j) := by
  simp only [map_pow, map_add, map_sum, _root_.map_mul, eval_C, eval_X, Function.comp_apply]
  rw [← Polynomial.eval_prod_X_sub_C, Polynomial.eval_eq_sum_range, natDegree_prod_X_sub_C,
    Finset.card_univ, Finset.sum_range, Fintype.sum_congr _ _ (fun j => ?_)]
  rw [mul_comm]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.val_last, Fin.snoc_last, ← Finset.card_univ, coeff_prod_X_sub_C_card, _root_.map_one]
  · simp [eval_coeffOfRoots]

lemma Finset.prod_prod_sub_swap (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    ∏ i in s, ∏ j in t, (f i - g j) = (-1) ^ (s.card * t.card) * ∏ j in t, ∏ i in s, (g j - f i) := by
  rw [prod_comm, pow_mul, ← prod_const, ← prod_mul_distrib, prod_congr rfl (fun j _ => ?_)]
  rw [← prod_const, ← prod_mul_distrib, prod_congr rfl (fun i _ => ?_)]
  rw [neg_one_mul, neg_sub]

lemma MvPolynomial.isHomogeneous_prod_sum_coeff (u : κ → K) :
    (∏ j : κ, (∑ i : Fin (m + 1), C (u j ^ (i : ℕ)) * X i)).IsHomogeneous (Fintype.card κ) := by
  rw [Fintype.card_eq_sum_ones]
  exact IsHomogeneous.prod _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ =>
    (isHomogeneous_C _ _).mul (isHomogeneous_X _ _)

lemma MvPolynomial.isHomogeneous_C_mul_prod_sum_coeff (u : κ → K) :
    (C ((-1) ^ (m * n)) * ∏ j : κ, (∑ i : Fin (m + 1), C (u j ^ (i : ℕ)) * X i)).IsHomogeneous (Fintype.card κ) :=
  (isHomogeneous_prod_sum_coeff _).C_mul _

/-- If P = C x * ∏ (X - t i) and Q = C y * ∏ (X - u i), then
  Res_(n,m) (P, Q) = ∏ (-1)^(n*m) * x^m * y^n (t i - u j) -/
lemma resultant_eq_prod_roots_aux [DecidableEq ι] [DecidableEq κ]
    (x y : K)
    [Infinite K] : -- TODO: we don't need this hypothesis if we work over `ℤ`
    ∀ (t : ι → K) (u : κ → K),
        Polynomial.resultant (∏ i, (X - C (t i))) (∏ i, (X - C (u i))) =
      (-1)^(Fintype.card ι * Fintype.card κ) * ∏ i, ∏ j, (t i - u j) := by
  intro t u

  let m := Fintype.card ι
  let n := Fintype.card κ

  suffices MvPolynomial.eval (Sum.elim t u) resultantPolynomialRoots =
      MvPolynomial.eval (Sum.elim t u) (MvPolynomial.C ((-1) ^ (Fintype.card ι * Fintype.card κ)) *
        ∏ i : ι, ∏ j : κ, (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr j))) by
    simpa [MvPolynomial.eval_resultantPolynomialRoots] using this

  congr
  rw [resultantPolynomialRoots]

  -- TODO: these polynomials are equal up to a constant because rescaling all the coefficients of `f` with `λ` is the same as rescaling the root with `1 / λ`
  sorry

  /-
  obtain ⟨c, hc⟩ := MvPolynomial.exists_C_mul_eq_of_dvd_of_homogeneous_left_of_homogeneous_right
    (R := K) (m := m) (n := n) (σ := ι) (τ := κ) (σ' := Fin (m + 1)) (τ' := Fin (n + 1)) _ _
    prod_root_differences_dvd_resultantPolynomialRoots
    (fun u => MvPolynomial.C ((-1) ^ (m * n)) * ∏ j, (∑ i : Fin (m + 1), MvPolynomial.C (u j ^ (i : ℕ)) * MvPolynomial.X i))
    (fun u => MvPolynomial.bind₁ (Sum.elim
        MvPolynomial.X
        (fun i => MvPolynomial.C (MvPolynomial.eval u (coeffOfRoots i))))
      resultantPolynomialCoeff)
    (fun t => ∏ i, _ /- ∑ (j : Fin n), MvPolynomial.C (t i ^ (j : ℕ)) * MvPolynomial.X j -/)
    (fun t => MvPolynomial.bind₁ (Sum.elim
        (fun i => MvPolynomial.C (MvPolynomial.eval t (coeffOfRoots i)))
        MvPolynomial.X)
      resultantPolynomialCoeff)
    (Fin.snoc coeffOfRoots x) (Fin.snoc coeffOfRoots y)
    ?_
    ?_
    ?_
    ?_
    (fun t u => by
      simp only [MvPolynomial.eval_prod, map_sub, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr,
        _root_.map_mul, MvPolynomial.eval_C]
      rw [Finset.prod_prod_sub_swap, Finset.card_univ, Finset.card_univ,
          Fintype.prod_congr _ _ (fun i => ?_)]
      rw [MvPolynomial.eval_prod_prod_X_sub_C'])
    (fun t u => by
      simp only [MvPolynomial.eval_prod, map_sub, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_congr _ _ (fun i => ?_)]
      rw [MvPolynomial.eval_prod_prod_X_sub_C'])
    (fun t u => by
      simp only [MvPolynomial.eval_resultantPolynomialRoots, Sum.elim_inl, Sum.elim_inr,
        MvPolynomial.eval_bind₁, MvPolynomial.eval_resultantPolynomialCoeff, MvPolynomial.eval_C,
        ofVec_coeffOfRoots, Function.comp_apply, MvPolynomial.eval_X])
    (fun t u => by
      simp only [MvPolynomial.eval_resultantPolynomialRoots, Sum.elim_inl, Sum.elim_inr,
        MvPolynomial.eval_bind₁, MvPolynomial.eval_resultantPolynomialCoeff, MvPolynomial.eval_C,
        ofVec_coeffOfRoots, Function.comp_apply, MvPolynomial.eval_X])
  suffices c = (-1)^(m * n) by
    rw [← this, ← hc]
    simp
  sorry
  -/

/-- If P = a_n ∏ (X - t i) and Q = b_n ∏ (X - u i, then
  Res_(n,m) (P, Q) = ∏ (-1)^(n*m) * (a_n)^m * (b_m)^n (t i - u j) -/
lemma resultant_eq_prod_roots [Infinite K] -- TODO: should work over `ℤ`
    (t : Fin m → K) (u : Fin n → K) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Polynomial.resultant (C x * ∏ i, (X - C (t i))) (C y * ∏ i, (X - C (u i))) =
      (-1)^(m * n) * x ^ n * y ^ m * ∏ i, ∏ j, (t i - u j) := by
  by_cases hm : m = 0
  · subst hm
    simp [natDegree_C_mul hy]
  by_cases hn : n = 0
  · subst hn
    simp [natDegree_C_mul hx]
  rw [C_mul_resultant, resultant_C_mul,
      resultant_eq_prod_roots_aux,
      natDegree_C_mul, natDegree_prod_X_sub_C, Finset.card_univ, Fintype.card_fin,
      natDegree_prod_X_sub_C, Finset.card_univ, Fintype.card_fin]
  · ring
  · assumption
  · simpa
  · simpa [natDegree_C_mul hy]


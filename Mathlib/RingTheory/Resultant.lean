import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.CC
import Mathlib.Tactic.SlimCheck

variable {R : Type}

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

section Zero

variable [Zero R]

/-- `sylvesterVec P i` is the vector `P` with `i` zeros appended to the left and `m - i` zeros to the right. -/
def sylvesterVec (P : Fin (n + 1) → R) (i : Fin m) : Fin (n + m) → R :=
  vecRotate (Fin.pad P 0) ((i.castAdd _).cast (add_comm _ _))

lemma sylvesterVec_apply (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m)) :
    sylvesterVec P i j = Fin.pad P 0 (j - ((i.castAdd _).cast (add_comm _ _))) :=
  rfl

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

example : sylvesterVec (m := 3) ![1, 2, 3] 1 = ![0, 1, 2, 3, 0] := by decide
example : sylvesterVec (m := 3) ![1, 2, 3] 2 = ![0, 0, 1, 2, 3] := by decide

/-
def sylvesterBlock (P : Fin (n + 1) → R) : Matrix (Fin m) (Fin (n + m)) R :=
  Matrix.of (sylvesterVec P)
-/

end Zero

variable [CommRing R] [Nontrivial R]

def sylvesterMatrixVec (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  (Matrix.of (Fin.addCases (fun i j ↦ sylvesterVec P i (j.cast (add_comm _ _))) (sylvesterVec Q)))ᵀ

@[simp] lemma sylvesterMatrixVec_comp_cast (a b) (P : Fin (a + 1) → R) (Q : Fin (b + 1) → R)
    (h₁ : n + 1 = a + 1) (h₂ : m + 1 = b + 1) (h : m + n = b + a := by simp) :
    sylvesterMatrixVec (P ∘ Fin.cast h₁) (Q ∘ Fin.cast h₂) =
      (sylvesterMatrixVec P Q).submatrix (Fin.cast h) (Fin.cast h) := by
  have := Nat.succ_injective h₁
  subst this
  have := Nat.succ_injective h₂
  subst this
  simp

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

@[simp] lemma Polynomial.toVec_X_add_C (x : R) :
    toVec (X + C x) = ![x, 1] ∘ Fin.cast (by simp) := by
  ext ⟨i, hi⟩
  rw [natDegree_X_add_C, Nat.lt_succ] at hi
  rcases hi with (_ | ⟨(_ | ⟨⟩)⟩) <;>
    rw [toVec_mk] <;>
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

-- #eval Polynomial.sylvesterMatrix (Polynomial.ofList [(1 : ℤ), 2, 3]) (Polynomial.ofList [4, 5, 6])

/- We define the resultant as the determinant of the previous matrix. -/
def Polynomial.resultant (P Q : Polynomial R) := det (Polynomial.sylvesterMatrix P Q)

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

@[simp] lemma resultant_C (P : Polynomial R) (x : R) :
    P.resultant (C x) = x ^ P.natDegree := by
  rw [resultant, sylvesterMatrix_C, det_diagonal, Fin.prod_const, natDegree_C, add_zero]

@[simp] lemma C_resultant (Q : Polynomial R) (x : R) :
    (C x).resultant Q = x ^ Q.natDegree := by
  rw [resultant, C_sylvesterMatrix, det_diagonal, Fin.prod_const, natDegree_C, zero_add]

@[simp] lemma X_add_C_resultant_X_add_C (x y : R) :
    (X + C x).resultant (X + C y) = y - x := by
  rw [resultant, sylvesterMatrix, toVec_X_add_C, toVec_X_add_C, sylvesterMatrixVec_comp_cast, det_submatrix]

/-- If P = a_n ∏ (X - t i) and Q = b_n ∏ (X - u i, then
  Res_(n,m) (P, Q) = ∏ (-1)^(n*m) * (a_n)^m * (b_m)^n (t i - u j) -/
lemma resultant_eq_prod_roots (P Q : Polynomial R)
    (t : Fin (P.natDegree + 1) → R) (u : Fin (Q.natDegree + 1) → R)
    (hsplitP : P = C P.leadingCoeff * ∏ i, (X - C (t i)))
    (hsplitQ : Q = C Q.leadingCoeff * ∏ i, (X - C (u i))) :
    Polynomial.resultant P Q =
      (-1)^(m * n) * (P.leadingCoeff)^m * (Q.leadingCoeff)^n * ∏ i, ∏ j, (t i - u j) :=
  sorry


lemma resultant_eq_comb (P Q : Polynomial R) :
    ∃ (U V : Polynomial R), U * P + V * Q = C (Polynomial.resultant P Q) :=
  sorry

end general

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Resultant of polynomials

This file contains basic facts about resultant of polynomials over commutative rings.

Polynomial.resultant : R[X] → R[X] → R

ID (Generality?) : Res(f,g)=0 ↔ f and g share a root (where?)
ID (?) : ∃ a b : R[X], Res f g = a * f + b * q (??)
CommRing: Res f g = (Sylvester f g).Det

TODO: Discriminant (Quadratic Formula)
-/


noncomputable section

section TO_MOVE

-- @[simp] lemma Fin.val_three {n : ℕ} : ((3 : Fin (n + 4)) : ℕ) = 3 :=
--   rfl

@[simp]
lemma Equiv.trans_symm {α β γ : Type*} {f : α ≃ β} {g : β ≃ γ} :
  (f.trans g).symm = g.symm.trans f.symm :=
rfl

theorem sign_finRotate_ite {n : ℕ} :
  Equiv.Perm.sign (finRotate n) = if n = 0 then 1 else (-1) ^ (n + 1) := by
cases n <;> simp [pow_succ]

lemma Equiv.Perm.sign_trans_symm {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]
    {e : α ≃ β} {f : β ≃ α} : sign (e.trans f) = sign (f.trans e) := calc
  _ = sign ((f.symm.trans (f.trans e)).trans f) := by simp [← trans_assoc]
  _ = _ := sign_symm_trans_trans _ _

@[simp]
lemma neg_one_pow_pow {R : Type*} [Monoid R] [HasDistribNeg R] (n : ℕ) :
    ((-1 : Rˣ) ^ n) ^ n = (-1) ^ n :=
(pow_mul _ _ _).symm.trans (neg_one_pow_congr (by simp [Nat.even_mul]))

@[simp]
theorem finRotate_pow_apply {m n : ℕ} {k : Fin m} :
  (((finRotate m) ^ n) k : ℕ) = (k + n) % m := by
  revert k
  induction n with
  | zero => simp [Nat.mod_eq_of_lt]
  | succ n ih =>
    intro k
    cases m with
    | zero => fin_cases k
    | succ m =>
      simp [pow_succ, ih, Fin.val_add]
      abel_nf

@[simp]
theorem finRotate_pow_apply' {m : ℕ} {n k : Fin m} :
  ((finRotate m) ^ (n : ℕ)) k = k + n :=
Fin.ext (finRotate_pow_apply.trans (Fin.val_add _ _).symm)

@[simp]
theorem finAddFlip_eq_add_mod {m n : ℕ} {k : Fin (m + n)} :
    finAddFlip k = ((k + n) % (m + n) : ℕ) := by
  refine k.addCases (fun k₁ ↦ ?_) (fun k₁ ↦ ?_)
  · simp [add_comm n, Nat.mod_eq_of_lt]
  · simp [add_comm m k₁, add_assoc, Nat.mod_eq_of_lt (Nat.lt_add_left m k₁.is_lt)]

theorem finAddFlip_eq_finRotate_pow {m n : ℕ} :
    finAddFlip.trans (finCongr (add_comm _ _)) = (finRotate (m + n)) ^ n := by
  ext; simp

theorem finAddFlip_eq_finRotate_pow' {m n : ℕ} :
    (finCongr (add_comm _ _)).trans finAddFlip = (finRotate (m + n)) ^ m := by
  ext; simp [add_comm n m]

theorem sign_finAddFlip {m n : ℕ} :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m))) = (-1) ^ (m * n) := by
  rw [finAddFlip_eq_finRotate_pow]
  cases m with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => simp [sign_finRotate_ite, pow_succ]
  | succ m => simp [sign_finRotate_ite, Nat.succ_mul, pow_add, pow_mul, mul_pow]

theorem sign_finAddFlip' {m n : ℕ} :
    Equiv.Perm.sign ((finCongr (add_comm n m)).trans finAddFlip) = (-1) ^ (m * n) := by
  rw [finAddFlip_eq_finRotate_pow']
  cases m with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => simp [sign_finRotate_ite, pow_succ]
  | succ m => simp [sign_finRotate_ite, Nat.succ_mul, pow_add, pow_mul,
      mul_pow, mul_comm, pow_right_comm]

theorem Matrix.det_submatrix {m n R : Type*} [DecidableEq n] [Fintype n]
      [DecidableEq m] [Fintype m] [CommRing R] (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    (A.submatrix e₁ e₂).det = Equiv.Perm.sign (e₁.trans e₂.symm) * A.det := calc
  _ = ((A.submatrix e₂ e₂).submatrix (e₁.trans e₂.symm) id).det := by simp [← Function.comp_assoc]
  _ = _ := by rw [Matrix.det_permute, det_submatrix_equiv_self]

theorem Matrix.det_submatrix' {m n R : Type*} [DecidableEq n] [Fintype n]
      [DecidableEq m] [Fintype m] [CommRing R] (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    (A.submatrix e₁ e₂).det = Equiv.Perm.sign (e₁.symm.trans e₂) * A.det := by
  rw [det_submatrix, Equiv.Perm.sign_trans_symm, ← Equiv.Perm.sign_symm,
    Equiv.trans_symm, Equiv.symm_symm]

theorem Matrix.det_submatrix'' {m n R : Type*} [DecidableEq n] [Fintype n]
      [DecidableEq m] [Fintype m] [CommRing R] (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    (A.submatrix e₁ e₂).det = Equiv.Perm.sign (e₂.trans e₁.symm) * A.det := by
  rw [det_submatrix, ← Equiv.Perm.sign_symm, Equiv.trans_symm, Equiv.symm_symm]

theorem Matrix.det_submatrix''' {m n R : Type*} [DecidableEq n] [Fintype n]
      [DecidableEq m] [Fintype m] [CommRing R] (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    (A.submatrix e₁ e₂).det = Equiv.Perm.sign (e₂.symm.trans e₁) * A.det := by
  rw [det_submatrix', ← Equiv.Perm.sign_symm, Equiv.trans_symm, Equiv.symm_symm]

end TO_MOVE


namespace Polynomial

variable {R : Type*} [CommRing R] (f g : R[X])

section sylvester
/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively
    is a `(n+m) × (n+m)` matrix with the coefficients of `f` and `g` arranged in a specific way.
    Here, `m` and `n` are free variables, not yet fixed to the actual degrees of the polynomials
    `f` and `g`. -/
def sylvester (m n : ℕ) : Matrix (Fin (n+m)) (Fin (n+m)) R :=
fun i j ↦ j.addCases
  (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+m) then f.coeff (i - j₁) else 0)
  (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+n) then g.coeff (i - j₁) else 0)

variable {f g}

section def_lemmas

variable {m n : ℕ}

lemma sylvester_fst_coeff {k : Fin (m+1)} {j : Fin n} :
    sylvester f g m n ⟨k+j, by linarith [k.is_lt, j.is_lt]⟩ (j.castAdd m) = f.coeff k := by
  rw [sylvester, Fin.addCases_left, add_comm (j:ℕ) m,
    if_pos ⟨Nat.le_add_left _ _, Nat.add_le_add_right (Nat.le_of_lt_succ k.is_lt) _⟩,
    Fin.val_mk, Nat.add_sub_cancel]

lemma sylvester_fst_coeff' (k : Fin (m+1)) {j : Fin n} {i : Fin (n+m)}
    (H : (k + j : ℕ) = i) :
    sylvester f g m n i (j.castAdd m) = f.coeff k := by
  convert sylvester_fst_coeff; exact H.symm

lemma sylvester_fst_zero (i : Fin (n+m)) {j : Fin n}
    (H : (i:ℕ) < j) : sylvester f g m n i (j.castAdd m) = 0 := by
  rw [sylvester, Fin.addCases_left, if_neg (by simp [H])]

lemma sylvester_fst_zero' (i : Fin (n+m)) {j : Fin n}
    (H : (j + m : ℕ) < i) : sylvester f g m n i (j.castAdd m) = 0 := by
  rw [sylvester, Fin.addCases_left, if_neg (by simp [H])]

lemma sylvester_snd_coeff {k : Fin (n+1)} {j : Fin m} :
    sylvester f g m n ⟨k+j, by linarith [k.is_lt, j.is_lt]⟩ (j.natAdd n) = g.coeff k := by
  rw [sylvester, Fin.addCases_right, add_comm (j:ℕ) n,
    if_pos ⟨Nat.le_add_left _ _, Nat.add_le_add_right (Nat.le_of_lt_succ k.is_lt) _⟩,
    Fin.val_mk, Nat.add_sub_cancel]

lemma sylvester_snd_coeff' (k : Fin (n+1)) {j : Fin m} {i : Fin (n+m)}
    (H : (k + j : ℕ) = i) :
    sylvester f g m n i (j.natAdd n) = g.coeff k := by
  convert sylvester_snd_coeff; exact H.symm

lemma sylvester_snd_zero (i : Fin (n+m)) {j : Fin m}
    (H : (i:ℕ) < j) : sylvester f g m n i (j.natAdd n) = 0 := by
  rw [sylvester, Fin.addCases_right, if_neg (by simp [H])]

lemma sylvester_snd_zero' (i : Fin (n+m)) {j : Fin m}
    (H : (j + n : ℕ) < i) : sylvester f g m n i (j.natAdd n) = 0 := by
  rw [sylvester, Fin.addCases_right, if_neg (by simp [H])]

lemma sylvester_induction {motive : Π (x : R) (i j : Fin (n+m)), Prop}
      (fst_coeff : ∀ (k : Fin (m+1)) (j : Fin n),
        motive (f.coeff k) ⟨k+j, by linarith [k.is_lt, j.is_lt]⟩ (j.castAdd m))
      (snd_coeff : ∀ (k : Fin (n+1)) (j : Fin m),
        motive (g.coeff k) ⟨k+j, by linarith [k.is_lt, j.is_lt]⟩ (j.natAdd n))
      (fst_zero₁ : ∀ (i : ℕ) (j : Fin n) (H : i < j),
        motive 0 ⟨i, by linarith [j.is_lt]⟩ (j.castAdd m))
      (fst_zero₂ : ∀ (i : Fin (n+m)) (j : Fin n) (H : j + m < i),
        motive 0 i (j.castAdd m))
      (snd_zero₁ : ∀ (i : ℕ) (j : Fin m) (H : i < j),
        motive 0 ⟨i, by linarith [j.is_lt]⟩ (j.natAdd n))
      (snd_zero₂ : ∀ (i : Fin (n+m)) (j : Fin m) (H : j + n < i),
        motive 0 i (j.natAdd n)) :
    ∀ {i j}, motive (sylvester f g m n i j) i j := by
  intro i j
  cases j using Fin.addCases with
  | left j =>
    rw [sylvester, Fin.addCases_left]
    split_ifs with h
    · rcases h with ⟨h1, h2⟩
      rcases Nat.exists_eq_add_of_le h1 with ⟨k, h3⟩
      have : k < m + 1 := Nat.lt_succ_of_le <| Nat.le_of_add_le_add_left <| by rwa [← h3]
      convert fst_coeff ⟨k, this⟩ j using 1
      · rw [h3, Fin.val_mk, Nat.add_sub_cancel_left]
      · exact Fin.ext <| h3.trans <| add_comm _ _
    · rw [Set.mem_Icc, Decidable.not_and_iff_not_or_not] at h
      cases h with
      | inl h => exact fst_zero₁ i j (by linarith)
      | inr h => exact fst_zero₂ i j (by linarith)
  | right j =>
    rw [sylvester, Fin.addCases_right]
    split_ifs with h
    · rcases h with ⟨h1, h2⟩
      rcases Nat.exists_eq_add_of_le h1 with ⟨k, h3⟩
      have : k < n + 1 := Nat.lt_succ_of_le <| Nat.le_of_add_le_add_left <| by rwa [← h3]
      convert snd_coeff ⟨k, this⟩ j using 1
      · rw [h3, Fin.val_mk, Nat.add_sub_cancel_left]
      · exact Fin.ext (by rw [h3, add_comm])
    · rw [Set.mem_Icc, Decidable.not_and_iff_not_or_not] at h
      cases h with
      | inl h => exact snd_zero₁ i j (by linarith)
      | inr h => exact snd_zero₂ i j (by linarith)

end def_lemmas

theorem sylvester_comm {f g : R[X]} {m n : ℕ} :
  sylvester g f n m = (sylvester f g m n).submatrix
    (finCongr (add_comm m n))
    (finAddFlip) := by
  ext i j
  refine j.addCases (fun j₁ ↦ ?_) (fun j₁ ↦ ?_) <;> simp [sylvester]

lemma sylvester_one_zero : sylvester f g 1 0 = !![g.coeff 0] := by
  ext i j; fin_cases i; fin_cases j; simp [sylvester, Fin.addCases]

/- Ideally, there will be good reduction algorithms. -/

-- lemma sylvester_two_one : sylvester f g 2 1 =
--   !![f.coeff 0, g.coeff 0, 0;
--      f.coeff 1, g.coeff 1, g.coeff 0;
--      f.coeff 2, 0,         g.coeff 1] := by
--   ext i j; fin_cases i <;> fin_cases j <;> simp [sylvester, Fin.addCases]

--   lemma sylvester_three_two : sylvester f g 3 2 =
--     !![f.coeff 0, 0,         g.coeff 0, 0,         0;
--        f.coeff 1, f.coeff 0, g.coeff 1, g.coeff 0, 0;
--        f.coeff 2, f.coeff 1, g.coeff 2, g.coeff 1, g.coeff 0;
--        f.coeff 3, f.coeff 2, 0,         g.coeff 2, g.coeff 1;
--        0,         f.coeff 3, 0,         0,         g.coeff 2] := by
--   ext i j; fin_cases i <;> fin_cases j <;> simp [sylvester, Fin.addCases]

-- lemma sylvester_four_three : sylvester f g 4 3 =
--   !![f.coeff 0, 0,         0,         g.coeff 0, 0,         0,         0;
--      f.coeff 1, f.coeff 0, 0,         g.coeff 1, g.coeff 0, 0,         0;
--      f.coeff 2, f.coeff 1, f.coeff 0, g.coeff 2, g.coeff 1, g.coeff 0, 0;
--      f.coeff 3, f.coeff 2, f.coeff 1, g.coeff 3, g.coeff 2, g.coeff 1, g.coeff 0;
--      f.coeff 4, f.coeff 3, f.coeff 2, 0,         g.coeff 3, g.coeff 2, g.coeff 1;
--      0,         f.coeff 4, f.coeff 3, 0,         0,         g.coeff 3, g.coeff 2;
--      0,         0,         f.coeff 4, 0,         0,         0,         g.coeff 3] := by
--   have this : ((3 : Fin 4) : ℕ) = 3 := rfl
--   ext i j; fin_cases i <;> fin_cases j <;> simp [sylvester, Fin.addCases, this]

end sylvester


section resultant

/-- A version of `resultant` where the degrees of the polynomials `f` and `g` are free variables. -/
def resultant_aux (f g : R[X]) (m n : ℕ) : R :=
(sylvester f g m n : Matrix _ _ R).det

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix
    of `f` and `g`. -/
def resultant : R :=
resultant_aux f g f.natDegree g.natDegree

variable {f g}

theorem resultant_comm : g.resultant f =
    (-1) ^ (f.natDegree * g.natDegree) * f.resultant g := by
  rw [resultant, resultant_aux, sylvester_comm, Matrix.det_submatrix', finCongr_symm,
    sign_finAddFlip']
  simp [resultant, resultant_aux]

lemma resultant_C_C {x y : R} : resultant (C x) (C y) = 1 :=
have : IsEmpty (Fin ((C y).natDegree + (C x).natDegree)) := by
  convert Fin.isEmpty; simp only [natDegree_C, add_zero]
Matrix.det_isEmpty

lemma resultant_linear_C {a b c : R} (H : a ≠ 0) :
    resultant (C a * X + C b) (C c) = c := by
  rw [resultant, resultant_aux, natDegree_linear H, natDegree_C, sylvester_one_zero,
    coeff_C_zero, Matrix.det_fin_one_of]

lemma resultant_X_add_C_C {x y : R} : resultant (X + C x) (C y) = y := by
  nontriviality R
  convert resultant_linear_C (one_ne_zero (α:=R)); rw [C_1, one_mul]

lemma resultant_C_X_add_C {x y : R} : resultant (C x) (X + C y) = x := by
  nontriviality R
  rw [resultant_comm, resultant_X_add_C_C, natDegree_X_add_C, natDegree_C]
  simp

lemma resultant_X_C {x : R} : resultant (X) (C x) = x := by
  convert resultant_X_add_C_C; rw [C_0, add_zero]

lemma resultant_C_X {x : R} : resultant (C x) X = x := by
  convert resultant_C_X_add_C; rw [C_0, add_zero]

end resultant


section sylvester_map

/-- If `P.degree ≤ m` and `Q.degree ≤ n`, and `(a, b) ∈ R[X]_n × R[X]_m`, then `P * a + Q * b`
is in `R[X]_(n + m)`.  -/
lemma sylvester_map_mem_aux {m n : ℕ} {P Q : Polynomial R}
    (hP : P.degree ≤ m) (hQ : Q.degree ≤ n) {a : R[x]_n} {b : R[x]_m} :
    P * a.val + Q * b.val ∈ R[x]_(n + m) :=
  add_mem (mul_left_mem_degreeLT' _ _ hP a.prop) (mul_left_mem_degreeLT _ _ hQ b.prop)

/-- We define the linear map `R[X]_n × R[X]_m → R[X]_{n + m}` with `(a, b) ↦ P * a + Q * b`. -/
noncomputable def sylvesterMap {m n : ℕ} (P Q : Polynomial R) :
    ((R[x]_n) × (R[x]_m)) →ₗ[R] (R[x]_(n + m)) :=
  if h : P.degree ≤ m ∧ Q.degree ≤ n then
    { toFun         := fun ab ↦ ⟨P * ab.1 + Q * ab.2, sylvester_map_mem_aux h.1 h.2⟩
      map_add' x y  := by simp; ring_nf
      map_smul' r a := by simp }
  else 0

@[simp] lemma sylvesterMap_apply {m n : ℕ} {P Q : Polynomial R}
    (hP : P.degree ≤ m) (hQ : Q.degree ≤ n) {AB : (R[x]_n) × (R[x]_m)} :
    sylvesterMap P Q AB = ⟨P * AB.1 + Q * AB.2, sylvester_map_mem_aux hP hQ⟩ := by
  simp [sylvesterMap, dif_pos (And.intro hP hQ)]

@[simp] lemma sylvesterMap_X_pow_zero {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (i : Fin m) :
    sylvesterMap P Q (⟨X ^ (i : ℕ), degreeLT_X_pow_mem R i⟩, 0) =
      ⟨P * X ^ (i : ℕ), mul_left_mem_degreeLT' _ _ hP (degreeLT_X_pow_mem R i)⟩ := by
  simp [hP, hQ]

@[simp] lemma sylvesterMap_zero_X_pow {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (i : Fin n) :
    sylvesterMap P Q (0, ⟨X ^ (i : ℕ), degreeLT_X_pow_mem R i⟩) =
      ⟨Q * X ^ (i : ℕ), mul_left_mem_degreeLT _ _ hQ (degreeLT_X_pow_mem R i)⟩ := by
  simp [hP, hQ]

/-- The Sylvester matrix is equal to the Sylvester map as a matrix in basis
(1, .., X^(m-1); 1, ..., X^(n-1)) and (1, ..., X^(m+n-1)).
-/
lemma sylvesterMap_toMatrix {P Q : Polynomial R} {m n : ℕ} (hP : P.degree ≤ m) (hQ : Q.degree ≤ n) :
    LinearMap.toMatrix (degreeLT.basis_prod R n m) (degreeLT.basis R (n + m)) (sylvesterMap P Q) =
    sylvester P Q m n := by
  ext i j
  refine sylvester_induction (motive := fun x i j ↦ LinearMap.toMatrix _ _ _ i j = x)
    (fun k j₁ ↦ ?_) (fun k j₁ ↦ ?_)
    (fun i j₁ h ↦ ?_) (fun i j₁ h ↦ ?_) (fun i j₁ h ↦ ?_) (fun i j₁ h ↦ ?_)
  · simp [hP, hQ, LinearMap.toMatrix_apply]
  · simp [hP, hQ, LinearMap.toMatrix_apply]
  · simp [hP, hQ, LinearMap.toMatrix_apply, coeff_mul_X_pow', if_neg (not_le_of_lt h)]
  · have H : (j₁ : ℕ) ≤ i := by linarith
    rcases Nat.exists_eq_add_of_le H with ⟨k, hk⟩
    rw [hk, add_lt_add_iff_left, ← WithBot.coe_lt_coe] at h
    simp [hP, hQ, LinearMap.toMatrix_apply, coeff_mul_X_pow', if_pos H,
      hk, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hP h)]
  · simp [hP, hQ, LinearMap.toMatrix_apply, coeff_mul_X_pow', if_neg (not_le_of_lt h)]
  · have H : (j₁ : ℕ) ≤ i := by linarith
    rcases Nat.exists_eq_add_of_le H with ⟨k, hk⟩
    rw [hk, add_lt_add_iff_left, ← WithBot.coe_lt_coe] at h
    simp [hP, hQ, LinearMap.toMatrix_apply, coeff_mul_X_pow', if_pos H,
      hk, Nat.add_sub_cancel_left, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hQ h)]

lemma sylvester_toLin {P Q : Polynomial R} {m n : ℕ} (hP : P.degree ≤ m) (hQ : Q.degree ≤ n) :
    (sylvester P Q m n).toLin (degreeLT.basis_prod R n m) (degreeLT.basis R (n + m)) =
    sylvesterMap P Q :=
  sylvesterMap_toMatrix hP hQ ▸ Matrix.toLin_toMatrix _ _ _

end sylvester_map


section bezout

/-- A pair `(A, B)` witnessing `P * A + Q * B = C (resultant P Q)`, as long as `P` and `Q` are not
both constant polynomials. -/
def bezout (m n : ℕ) (P Q : Polynomial R) : (R[x]_n) × (R[x]_m) :=
  if H : n + m = 0 then 0 else
  Matrix.toLin (degreeLT.basis R (n + m)) (degreeLT.basis_prod R n m)
    (sylvester P Q m n).adjugate
    ⟨1, mem_degreeLT.2 <| degree_one_le.trans_lt <| WithBot.coe_pos.2 <| Nat.pos_of_ne_zero H⟩

@[simp] lemma bezout_apply (m n : ℕ) (P Q : Polynomial R) (H : n + m ≠ 0) :
  bezout m n P Q =
  Matrix.toLin (degreeLT.basis R (n + m)) (degreeLT.basis_prod R n m)
    (sylvester P Q m n).adjugate
    ⟨1, mem_degreeLT.2 <| degree_one_le.trans_lt <| WithBot.coe_pos.2 <| Nat.pos_of_ne_zero H⟩ :=
dif_neg H

theorem mul_add_mul_resultant_aux (m n : ℕ) (P Q : Polynomial R)
    (H : n + m ≠ 0)
    (hP : P.degree ≤ m) (hQ : Q.degree ≤ n) :
    P * (bezout m n P Q).1 + Q * (bezout m n P Q).2 =
      C (resultant_aux P Q m n) := by
  have h := Matrix.mul_adjugate (sylvester P Q m n)
  replace h := congr_arg (Matrix.toLin (degreeLT.basis R (n + m)) (degreeLT.basis R (n + m))) h
  replace h := Subtype.ext_iff.1 <| LinearMap.ext_iff.1 h
    ⟨1, mem_degreeLT.2 <| degree_one_le.trans_lt <| WithBot.coe_pos.2 <| Nat.pos_of_ne_zero H⟩
  rw [Matrix.toLin_mul _ (degreeLT.basis_prod R n m), LinearMap.coe_comp, Function.comp_apply,
    map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_coe, id_eq, SetLike.mk_smul_mk,
    sylvester_toLin hP hQ, ← bezout_apply m n P Q H, sylvesterMap_apply hP hQ] at h
  simp only [smul_eq_C_mul, mul_one] at h
  exact h

theorem mul_add_mul_resultant (P Q : Polynomial R) (H : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    P * (bezout P.natDegree Q.natDegree P Q).1 + Q * (bezout P.natDegree Q.natDegree P Q).2 =
      C (resultant P Q) :=
  mul_add_mul_resultant_aux _ _ _ _ (by aesop) P.degree_le_natDegree Q.degree_le_natDegree

theorem mul_add_mul_resultant_left (P Q : Polynomial R) (H : P.natDegree ≠ 0) :
    P * (bezout P.natDegree Q.natDegree P Q).1 + Q * (bezout P.natDegree Q.natDegree P Q).2 =
      C (resultant P Q) :=
  mul_add_mul_resultant _ _ (by aesop)

theorem mul_add_mul_resultant_right (P Q : Polynomial R) (H : Q.natDegree ≠ 0) :
    P * (bezout P.natDegree Q.natDegree P Q).1 + Q * (bezout P.natDegree Q.natDegree P Q).2 =
      C (resultant P Q) :=
  mul_add_mul_resultant _ _ (by aesop)

end bezout

end Polynomial

#lint

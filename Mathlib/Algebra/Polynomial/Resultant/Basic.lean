/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Content

/-!
# Resultant of polynomials

This file contains basic facts about resultant of polynomials over commutative rings.

Polynomial.resultant : R[X] → R[X] → R

ID (Generality?) : Res(f,g)=0 ↔ f and g share a root (where?)
ID (?) : ∃ a b : R[X], Res f g = a * f + b * q (??)
CommRing: Res f g = (Sylvester f g).Det

TODO: Discriminant (Quadratic Formula)

Question: is it better for m and n to have a specified "default argument"? i.e.
`def resultant (f g : R[X]) (m n : ℕ := f.natDegree, g.natDegree) : R`? That way we don't
need to make all those `aux` definitions?
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

@[simp] theorem sign_finAddFlip {m n : ℕ} :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m))) = (-1) ^ (m * n) := by
  rw [finAddFlip_eq_finRotate_pow]
  cases m with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => simp [sign_finRotate_ite, pow_succ]
  | succ m => simp [sign_finRotate_ite, Nat.succ_mul, pow_add, pow_mul, mul_pow]

@[simp] theorem sign_finAddFlip' {m n : ℕ} :
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

section sylvester

variable {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively
    is a `(n+m) × (n+m)` matrix with the coefficients of `f` and `g` arranged in a specific way.
    Here, `m` and `n` are free variables, not yet fixed to the actual degrees of the polynomials
    `f` and `g`. -/
def sylvester : Matrix (Fin (n+m)) (Fin (n+m)) R :=
  fun i j ↦ j.addCases
    (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+m) then f.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+n) then g.coeff (i - j₁) else 0)

variable {f g m n}

section def_lemmas

@[simp] lemma sylvester_fst_coeff {j : Fin n} {k : Fin (m+1)} :
    sylvester f g m n ⟨j+k, add_lt_add_of_lt_of_le j.2 k.is_le⟩ (j.castAdd m) = f.coeff k := by
  rw [sylvester, Fin.addCases_left,
    if_pos ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.le_of_lt_succ k.is_lt) _⟩,
    Fin.val_mk, Nat.add_sub_cancel_left]

lemma sylvester_fst_coeff' {j : Fin n} {i : Fin (n+m)} (k : Fin (m+1))
    (H : (j + k : ℕ) = i) :
    sylvester f g m n i (j.castAdd m) = f.coeff k := by
  convert sylvester_fst_coeff using 3; exact H.symm

@[simp] lemma sylvester_fst_zero₁ {j : Fin n} {i : { i : Fin (n+m) // (i : ℕ) < j }} :
    sylvester f g m n i (j.castAdd m) = 0 := by
  rw [sylvester, Fin.addCases_left, if_neg (by simp [i.2])]

@[simp] lemma sylvester_fst_zero₂ {j : Fin n} {i : { i : Fin (n+m) // (j + m : ℕ) < i }} :
    sylvester f g m n i (j.castAdd m) = 0 := by
  rw [sylvester, Fin.addCases_left, if_neg (by simp [i.2])]

@[simp] lemma sylvester_snd_coeff {j : Fin m} {k : Fin (n+1)} :
    sylvester f g m n ⟨j+k, add_comm m n ▸ add_lt_add_of_lt_of_le j.2 k.is_le⟩ (j.natAdd n) =
      g.coeff k := by
  rw [sylvester, Fin.addCases_right,
    if_pos ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.le_of_lt_succ k.is_lt) _⟩,
    Fin.val_mk, Nat.add_sub_cancel_left]

lemma sylvester_snd_coeff' {j : Fin m} {i : Fin (n+m)} (k : Fin (n+1))
    (H : (j + k : ℕ) = i) :
    sylvester f g m n i (j.natAdd n) = g.coeff k := by
  convert sylvester_snd_coeff using 3; exact H.symm

@[simp] lemma sylvester_snd_zero₁ {j : Fin m} {i : { i : Fin (n+m) // (i : ℕ) < j }} :
    sylvester f g m n i (j.natAdd n) = 0 := by
  rw [sylvester, Fin.addCases_right, if_neg (by simp [i.2])]

@[simp] lemma sylvester_snd_zero₂ {j : Fin m} {i : { i : Fin (n+m) // (j + n : ℕ) < i }} :
    sylvester f g m n i (j.natAdd n) = 0 := by
  rw [sylvester, Fin.addCases_right, if_neg (by simp [i.2])]

/-- A special form of "induction" (i.e. splitting into cases) used for reasoning about the
Sylvester matrix, that splits `Fin (n+m) × Fin (n+m)` into 6 "regions". Use `Fin.addCases`
to case on the second argument first, and then use `sylvester_induction_left` and
`sylvester_induction_right`. Used in conjunction with the definitional lemmas like
`sylvester_fst_coeff`, where the `fst_coeff` part of the name has been specifically chosen to
match the case names generated here. See `sylvesterMap_toMatrix` for an example. -/
lemma sylvester_induction_left {i : Fin (n+m)} (j : Fin n) {motive : Fin (n+m) → Prop}
      (fst_coeff : ∀ (k : Fin (m+1)),
        motive ⟨j+k, add_lt_add_of_lt_of_le j.2 k.is_le⟩)
      (fst_zero₁ : ∀ (i : { i : Fin (n+m) // (i : ℕ) < j }),
        motive i)
      (fst_zero₂ : ∀ (i : { i : Fin (n+m) // (j + m : ℕ) < i }),
        motive i) :
    motive i := by
  cases le_or_lt (j : ℕ) (i : ℕ) with
  | inl h₁ => cases le_or_lt (i : ℕ) (j + m : ℕ) with
    | inl h₂ =>
        convert fst_coeff ⟨i-j, Nat.lt_succ_of_le <| Nat.sub_le_iff_le_add'.2 h₂⟩
        exact (Nat.add_sub_cancel' h₁).symm
    | inr h₂ => exact fst_zero₂ ⟨i, h₂⟩
  | inr h₁ => exact fst_zero₁ ⟨i, h₁⟩

/-- A special form of "induction" (i.e. splitting into cases) used for reasoning about the
Sylvester matrix, that splits `Fin (n+m) × Fin (n+m)` into 6 "regions". Use `Fin.addCases`
to case on the second argument first, and then use `sylvester_induction_left` and
`sylvester_induction_right`. Used in conjunction with the definitional lemmas like
`sylvester_snd_coeff`, where the `snd_coeff` part of the name has been specifically chosen to
match the case names generated here. See `sylvesterMap_toMatrix` for an example. -/
lemma sylvester_induction_right {i : Fin (n+m)} (j : Fin m) {motive : Fin (n+m) → Prop}
      (snd_coeff : ∀ (k : Fin (n+1)),
        motive ⟨j+k, add_comm m n ▸ add_lt_add_of_lt_of_le j.2 k.is_le⟩)
      (snd_zero₁ : ∀ (i : { i : Fin (n+m) // (i : ℕ) < j }),
        motive i)
      (snd_zero₂ : ∀ (i : { i : Fin (n+m) // (j + n : ℕ) < i }),
        motive i) :
    motive i := by
  cases le_or_lt (j : ℕ) (i : ℕ) with
  | inl h₁ => cases le_or_lt (i : ℕ) (j + n : ℕ) with
    | inl h₂ =>
        convert snd_coeff ⟨i-j, Nat.lt_succ_of_le <| Nat.sub_le_iff_le_add'.2 h₂⟩
        exact (Nat.add_sub_cancel' h₁).symm
    | inr h₂ => exact snd_zero₂ ⟨i, h₂⟩
  | inr h₁ => exact snd_zero₁ ⟨i, h₁⟩

end def_lemmas

theorem sylvester_comm : sylvester g f n m =
    (sylvester f g m n).submatrix (finCongr (add_comm m n)) (finAddFlip) := by
  ext i j
  refine j.addCases (fun j₁ ↦ ?_) (fun j₁ ↦ ?_) <;> simp [sylvester]

theorem sylvester_C_snd {a : R} :
    sylvester f (C a) m 0 = Matrix.diagonal (fun _ ↦ a) := by
  ext i j
  cases j using Fin.addCases with
  | left j => fin_cases j
  | right j => cases i using sylvester_induction_right j with
    | snd_coeff k =>
        fin_cases k
        rw [sylvester_snd_coeff, coeff_C_zero, Fin.natAdd_zero]
        exact Eq.symm (Matrix.diagonal_apply_eq _ _)
    | snd_zero₁ i => rw [sylvester_snd_zero₁, Fin.natAdd_zero, Matrix.diagonal_apply,
        if_neg (Fin.ext_iff.not.2 <| ne_of_lt i.2)]
    | snd_zero₂ i => rw [sylvester_snd_zero₂, Fin.natAdd_zero, Matrix.diagonal_apply,
        if_neg (Fin.ext_iff.not.2 <| ne_of_gt i.2)]

theorem sylvester_C_fst {a : R} :
    sylvester (C a) f 0 m = Matrix.diagonal (fun _ ↦ a) := by
  ext i j
  have hjj : ((finAddFlip j).val : ℕ) = j := by
    cases j using Fin.addCases with
    | left j₁  => simp only [finAddFlip_apply_castAdd, Fin.coe_natAdd, zero_add, Fin.coe_castAdd]
    | right j₁ => fin_cases j₁
  rw [sylvester_comm, sylvester_C_snd]
  refine ite_congr ?_ (fun _ ↦ rfl) (fun _ ↦ rfl)
  simp only [Nat.add_zero, finCongr_apply, Fin.ext_iff, Fin.coe_cast, eq_iff_iff, ← hjj]

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

variable {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)

/-- A version of `resultant` where the degrees of the polynomials `f` and `g` are free variables. -/
def resultantAux : R :=
(sylvester f g m n : Matrix _ _ R).det

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix
    of `f` and `g`. -/
def resultant : R :=
resultantAux f g f.natDegree g.natDegree

variable {f g m n}

lemma resultant_def : resultant f g = (sylvester f g f.natDegree g.natDegree).det := rfl

theorem resultant_comm : g.resultant f =
    (-1) ^ (f.natDegree * g.natDegree) * f.resultant g := by
  rw [resultant_def, sylvester_comm, Matrix.det_submatrix']
  simp [resultant_def]

variable {a b c x y z : R}

/-- For polynomial `f` and constant `a`, `Res(a,f) = a^m`. -/
theorem resultantAux_C : resultantAux (C a) f 0 m = a ^ m := by
  rw [resultantAux, sylvester_C_fst, Matrix.det_diagonal, Fin.prod_const, add_zero]

/-- For polynomial `f` and constant `a`, `Res(f,a) = a^m`. -/
theorem resultantAux_C' : resultantAux f (C a) m 0 = a ^ m := by
  rw [resultantAux, sylvester_C_snd, Matrix.det_diagonal, Fin.prod_const, zero_add]

/-- For polynomial `f` and constant `a`, `Res(f,a) = a^n`. -/
theorem resultant_C : resultant (C a) f = a ^ f.natDegree := by
  rw [resultant, natDegree_C, resultantAux_C]

/-- For polynomial `f` and constant `a`, `Res(a,f) = a^n`. -/
theorem resultant_C' : resultant f (C a) = a ^ f.natDegree := by
  rw [resultant, natDegree_C, resultantAux_C']

lemma resultant_C_C : resultant (C a) (C b) = 1 := by
  rw [resultant_C, natDegree_C, pow_zero]

lemma resultant_linear_C (H : a ≠ 0) : resultant (C a * X + C b) (C x) = x := by
  rw [resultant_C', natDegree_linear H, pow_one]

lemma resultant_C_linear (H : a ≠ 0) : resultant (C x) (C a * X + C b) = x := by
  rw [resultant_C, natDegree_linear H, pow_one]

lemma resultant_X_add_C_C {x y : R} : resultant (X + C x) (C y) = y := by
  nontriviality R
  rw [resultant_C', natDegree_X_add_C, pow_one]

lemma resultant_C_X_add_C {x y : R} : resultant (C x) (X + C y) = x := by
  nontriviality R
  rw [resultant_C, natDegree_X_add_C, pow_one]

lemma resultant_X_C {x : R} : resultant (X) (C x) = x := by
  convert resultant_X_add_C_C; rw [C_0, add_zero]

lemma resultant_C_X {x : R} : resultant (C x) X = x := by
  convert resultant_C_X_add_C; rw [C_0, add_zero]

end resultant


section sylvester_map

variable {R : Type*} [CommRing R] {P Q : Polynomial R} {m n : ℕ}
  (hP : P.degree ≤ m := by exact P.degree_le_natDegree)
  (hQ : Q.degree ≤ n := by exact Q.degree_le_natDegree)
  {a : R[x]_n} {b : R[x]_m} {AB : (R[x]_n) × (R[x]_m)}

include hP hQ in
/-- If `P.degree ≤ m` and `Q.degree ≤ n`, and `(a, b) ∈ R[x]_n × R[x]_m`, then `P * a + Q * b`
is in `R[x]_(n + m)`. -/
lemma sylvesterMap_mem_aux : P * a.val + Q * b.val ∈ R[x]_(n + m) :=
  add_mem (mul_left_mem_degreeLT' _ _ hP a.prop) (mul_left_mem_degreeLT _ _ hQ b.prop)

variable (P Q) in
/-- We define the linear map `R[x]_n × R[x]_m → R[x]_{n + m}` with `(a, b) ↦ P * a + Q * b`. -/
noncomputable def sylvesterMap : ((R[x]_n) × (R[x]_m)) →ₗ[R] (R[x]_(n + m)) :=
  if h : P.degree ≤ m ∧ Q.degree ≤ n then
    { toFun         := fun ab ↦ ⟨P * ab.1 + Q * ab.2, sylvesterMap_mem_aux h.1 h.2⟩
      map_add' x y  := by simp; ring_nf
      map_smul' r a := by simp }
  else 0

variable (P Q) in
/-- We define the linear map `R[x]_n × R[x]_m → R[x]_{n + m}` with `(a, b) ↦ P * a + Q * b`.
Here `m` and `n` are fixed to be `P.natDegree` and `Q.natDegree` respectively. -/
@[simps] noncomputable def sylvesterMap' :
    ((R[x]_Q.natDegree) × (R[x]_P.natDegree)) →ₗ[R] (R[x]_(Q.natDegree + P.natDegree)) where
  toFun         := fun ab ↦ ⟨P * ab.1 + Q * ab.2, sylvesterMap_mem_aux⟩
  map_add' x y  := by simp; ring_nf
  map_smul' r a := by simp

@[simp] lemma sylvesterMap_apply :
    sylvesterMap P Q AB = ⟨P * AB.1 + Q * AB.2, sylvesterMap_mem_aux hP hQ⟩ := by
  simp [sylvesterMap, dif_pos (And.intro hP hQ)]

lemma sylvesterMap_eq_sylvesterMap' :
    sylvesterMap P Q = sylvesterMap' P Q :=
  dif_pos ⟨P.degree_le_natDegree, Q.degree_le_natDegree⟩

include hP hQ

@[simp] lemma sylvesterMap_X_pow_zero (i : Fin n) :
    sylvesterMap P Q (⟨X ^ (i : ℕ), degreeLT_X_pow_mem i⟩, 0) =
      ⟨P * X ^ (i : ℕ), mul_left_mem_degreeLT' _ _ hP (degreeLT_X_pow_mem i)⟩ := by
  simp [hP, hQ]

@[simp] lemma sylvesterMap_zero_X_pow (i : Fin m) :
    sylvesterMap P Q (0, ⟨X ^ (i : ℕ), degreeLT_X_pow_mem i⟩) =
      ⟨Q * X ^ (i : ℕ), mul_left_mem_degreeLT _ _ hQ (degreeLT_X_pow_mem i)⟩ := by
  simp [hP, hQ]

/-- The Sylvester matrix is equal to the Sylvester map as a matrix in basis
(1, .., X^(m-1); 1, ..., X^(n-1)) and (1, ..., X^(m+n-1)).
-/
lemma sylvesterMap_toMatrix :
    LinearMap.toMatrix (degreeLT.basis_prod R n m) (degreeLT.basis R (n + m)) (sylvesterMap P Q) =
    sylvester P Q m n := by
  ext i j
  cases j using Fin.addCases with
  | left j => cases i using sylvester_induction_left j with
    | fst_coeff k =>
        rw [sylvester_fst_coeff]
        simp [hP, hQ, add_comm (j : ℕ), LinearMap.toMatrix_apply]
    | fst_zero₁ i =>
        rw [sylvester_fst_zero₁]
        simp [hP, hQ, LinearMap.toMatrix_apply, coeff_mul_X_pow', if_neg (not_le_of_lt i.2)]
    | fst_zero₂ i =>
        have h₁ : (j : ℕ) ≤ i := le_trans (Nat.le_add_right _ _) i.2.le
        have h₂ : (m : ℕ) < i -j := Nat.lt_sub_of_add_lt <| (add_comm _ _).trans_lt i.2
        rw [sylvester_fst_zero₂, LinearMap.toMatrix_apply, degreeLT.basis_prod_castAdd,
          sylvesterMap_apply hP hQ, degreeLT.basis_repr]
        show (P * X ^ (j:ℕ) + Q * 0).coeff i = (0:R)
        rw [mul_zero, add_zero, coeff_mul_X_pow', if_pos h₁,
          coeff_eq_zero_of_degree_lt (hP.trans_lt (WithBot.coe_lt_coe.2 h₂) : P.degree < (i-j:ℕ))]
  | right j => cases i using sylvester_induction_right j with
    | snd_coeff k =>
        rw [sylvester_snd_coeff]
        simp [hP, hQ, add_comm (j : ℕ), LinearMap.toMatrix_apply]
    | snd_zero₁ i =>
        rw [sylvester_snd_zero₁]
        simp [hP, hQ, LinearMap.toMatrix_apply, coeff_mul_X_pow', if_neg (not_le_of_lt i.2)]
    | snd_zero₂ i =>
        have h₁ : (j : ℕ) ≤ i := le_trans (Nat.le_add_right _ _) i.2.le
        have h₂ : (n : ℕ) < i -j := Nat.lt_sub_of_add_lt <| (add_comm _ _).trans_lt i.2
        rw [sylvester_snd_zero₂, LinearMap.toMatrix_apply, degreeLT.basis_prod_natAdd,
          sylvesterMap_apply hP hQ, degreeLT.basis_repr]
        show (P * 0 + Q * X ^ (j:ℕ)).coeff i = (0:R)
        rw [mul_zero, zero_add, coeff_mul_X_pow', if_pos h₁,
          coeff_eq_zero_of_degree_lt (hQ.trans_lt (WithBot.coe_lt_coe.2 h₂) : Q.degree < (i-j:ℕ))]

omit hP hQ in
/-- The Sylvester matrix is equal to the Sylvester map as a matrix in basis
(1, .., X^(m-1); 1, ..., X^(n-1)) and (1, ..., X^(m+n-1)).
-/
lemma sylvesterMap_toMatrix' :
    LinearMap.toMatrix (degreeLT.basis_prod R _ _) (degreeLT.basis R _) (sylvesterMap' P Q) =
    sylvester P Q _ _ := by
  rw [← sylvesterMap_eq_sylvesterMap', sylvesterMap_toMatrix]

lemma sylvester_toLin :
    (sylvester P Q m n).toLin (degreeLT.basis_prod R n m) (degreeLT.basis R (n + m)) =
    sylvesterMap P Q :=
  sylvesterMap_toMatrix hP hQ ▸ Matrix.toLin_toMatrix _ _ _

omit hP hQ in
lemma sylvester_toLin' :
    (sylvester P Q _ _).toLin (degreeLT.basis_prod R _ _) (degreeLT.basis R _) =
    sylvesterMap' P Q :=
  sylvesterMap_toMatrix' (P:=P) ▸ Matrix.toLin_toMatrix _ _ _

/-- `Res(P,Q)` is the determinant of the linear map `A, B ↦ PA+QB`, viewed as a linear map
on the space `R[x]_(n+m)` after identification of `R[x]_(n+m)` with `R[x]_n × R[x]_m`.
Here `m` and `n` are free variables. -/
theorem det_sylvesterMap_aux : (sylvesterMap P Q (m:=m) (n:=n) ∘ₗ
      degreeLT.addLinearEquiv.toLinearMap).det =
    resultantAux P Q m n := by
  rw [← LinearMap.det_toMatrix (degreeLT.basis R (n + m)),
    LinearMap.toMatrix_comp _ (degreeLT.basis_prod R n m),
    degreeLT.addLinearEquiv, LinearMap.toMatrix_basis_equiv, mul_one, resultantAux,
    sylvesterMap_toMatrix hP hQ]

omit hP hQ in
/-- `Res(P,Q)` is the determinant of the linear map `A, B ↦ PA+QB`, viewed as a linear map
on the space `R[x]_(n+m)` after identification of `R[x]_(n+m)` with `R[x]_n × R[x]_m`.
Here `m` and `n` are fixed to be `P.natDegree` and `Q.natDegree` repectively. -/
theorem det_sylvesterMap : (sylvesterMap' P Q ∘ₗ degreeLT.addLinearEquiv.toLinearMap).det =
    resultant P Q :=
  sylvesterMap_eq_sylvesterMap' (P:=P) ▸ det_sylvesterMap_aux

end sylvester_map


section bezout

variable {R : Type*} [CommRing R] {m n : ℕ} {P Q : Polynomial R} (H : n + m ≠ 0)
  (hP : P.degree ≤ m := by exact P.degree_le_natDegree)
  (hQ : Q.degree ≤ n := by exact Q.degree_le_natDegree)

variable (m n P Q) in
/-- A pair `(A, B)` witnessing `P * A + Q * B = C (resultant P Q)`, as long as `P` and `Q` are not
both constant polynomials. -/
def bezout : (R[x]_n) × (R[x]_m) :=
  if H : n + m = 0 then 0 else
  Matrix.toLin (degreeLT.basis R (n + m)) (degreeLT.basis_prod R n m)
    (sylvester P Q m n).adjugate
    ⟨1, mem_degreeLT.2 <| degree_one_le.trans_lt <| WithBot.coe_pos.2 <| Nat.pos_of_ne_zero H⟩

@[simp] lemma bezout_apply : bezout m n P Q =
  Matrix.toLin (degreeLT.basis R (n + m)) (degreeLT.basis_prod R n m)
    (sylvester P Q m n).adjugate
    ⟨1, mem_degreeLT.2 <| degree_one_le.trans_lt <| WithBot.coe_pos.2 <| Nat.pos_of_ne_zero H⟩ :=
dif_neg H

include H hP hQ in
theorem bezout_comb_eq_resultantAux :
    P * (bezout m n P Q).1 + Q * (bezout m n P Q).2 =
      C (resultantAux P Q m n) := by
  have h := Matrix.mul_adjugate (sylvester P Q m n)
  replace h := congr_arg (Matrix.toLin (degreeLT.basis R (n + m)) (degreeLT.basis R (n + m))) h
  replace h := Subtype.ext_iff.1 <| LinearMap.ext_iff.1 h
    ⟨1, mem_degreeLT.2 <| degree_one_le.trans_lt <| WithBot.coe_pos.2 <| Nat.pos_of_ne_zero H⟩
  rw [Matrix.toLin_mul _ (degreeLT.basis_prod R n m), LinearMap.coe_comp, Function.comp_apply,
    map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_coe, id_eq, SetLike.mk_smul_mk,
    sylvester_toLin hP hQ, ← bezout_apply H, sylvesterMap_apply hP hQ] at h
  simp only [smul_eq_C_mul, mul_one] at h
  exact h

theorem bezout_comb_eq_resultant (H : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    P * (bezout P.natDegree Q.natDegree P Q).1 + Q * (bezout P.natDegree Q.natDegree P Q).2 =
      C (resultant P Q) :=
  bezout_comb_eq_resultantAux (by aesop)

theorem bezout_comb_eq_resultant_left (H : P.natDegree ≠ 0) :
    P * (bezout P.natDegree Q.natDegree P Q).1 + Q * (bezout P.natDegree Q.natDegree P Q).2 =
      C (resultant P Q) :=
  bezout_comb_eq_resultant (by aesop)

theorem bezout_comb_eq_resultant_right (H : Q.natDegree ≠ 0) :
    P * (bezout P.natDegree Q.natDegree P Q).1 + Q * (bezout P.natDegree Q.natDegree P Q).2 =
      C (resultant P Q) :=
  bezout_comb_eq_resultant (by aesop)

theorem resultant_eq_zero_of_root {x : R} (h0 : P ≠ 0 ∨ Q ≠ 0)
    (hP : IsRoot P x) (hQ : IsRoot Q x) : resultant P Q = 0 := by
  have hPD (h : P ≠ 0) : P.natDegree ≠ 0 :=
    ne_of_gt <| natDegree_pos_iff_degree_pos.2 <| degree_pos_of_root h hP
  have hQD (h : Q ≠ 0) : Q.natDegree ≠ 0 :=
    ne_of_gt <| natDegree_pos_iff_degree_pos.2 <| degree_pos_of_root h hQ
  by_cases hP0 : P = 0
  · rw [hP0, ← C_0, resultant_C, zero_pow (hQD <| h0.neg_resolve_left hP0)]
  · rw [← eval_C (x:=x) (a:=resultant P Q), ← bezout_comb_eq_resultant_left (hPD hP0)]
    simp only [eval_add, eval_mul, hP.eq_zero, hQ.eq_zero, zero_mul, add_zero]

theorem resultant_eq_zero_of_root_left {x : R} (h0 : P ≠ 0)
    (hP : IsRoot P x) (hQ : IsRoot Q x) : resultant P Q = 0 :=
  resultant_eq_zero_of_root (Or.inl h0) hP hQ

theorem resultant_eq_zero_of_root_right {x : R} (h0 : Q ≠ 0)
    (hP : IsRoot P x) (hQ : IsRoot Q x) : resultant P Q = 0 :=
  resultant_eq_zero_of_root (Or.inr h0) hP hQ

end bezout


section RingHom

variable {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S} {f g : R[X]} {m n : ℕ}

/-- The sylvester matrix of two polynomials `f` and `g` is conserved under a ring homomorphism. -/
theorem sylvester_map :
    sylvester (f.map φ) (g.map φ) m n = (sylvester f g m n).map φ := by
  ext i j
  rw [sylvester, Matrix.map_apply, sylvester]
  cases j using Fin.addCases <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> split_ifs <;>
    simp only [φ.map_zero, coeff_map]

/-- The resultant of two polynomials `f` and `g` is conserved under a ring homomorphism. -/
theorem resultantAux_map :
    resultantAux (f.map φ) (g.map φ) m n = φ (resultantAux f g m n) := by
  rw [resultantAux, resultantAux, sylvester_map, RingHom.map_det, RingHom.mapMatrix_apply]

/-- The resultant of two polynomials `f` and `g` is conserved under a ring homomorphism
that maps the leading coefficients of `f` and `g` to non-zero values. -/
theorem resultant_map (hf : φ f.leadingCoeff ≠ 0) (hg : φ g.leadingCoeff ≠ 0) :
    resultant (f.map φ) (g.map φ) = φ (resultant f g) := by
  rw [resultant, resultant, resultantAux_map, natDegree_map_of_leadingCoeff_ne_zero _ hf,
    natDegree_map_of_leadingCoeff_ne_zero _ hg]

/-- The resultant of two polynomials `f` and `g` is conserved under an
injective ring homomorphism. -/
theorem resultant_map_of_injective (hφ : (⇑φ).Injective) :
    resultant (f.map φ) (g.map φ) = φ (resultant f g) := by
  rw [resultant, resultant, resultantAux_map, natDegree_map_eq_of_injective hφ,
    natDegree_map_eq_of_injective hφ]

end RingHom


section translate

variable {R : Type*} [CommRing R] {x : R} {f g : R[X]} {m n : ℕ}
  (hf : f.degree ≤ m := by exact f.degree_le_natDegree)
  (hg : g.degree ≤ n := by exact g.degree_le_natDegree)

/-- The square involving `sylvesterMap` and `translate x` commutes. -/
lemma translate_sylvesterMap :
    (translateLinear x _).toLinearMap ∘ₗ sylvesterMap f g (m := m) (n := n) =
      sylvesterMap (f.translate x) (g.translate x) ∘ₗ (translateProd x n m).toLinearMap := by
  by_cases h : f.degree ≤ m ∧ g.degree ≤ n
  · rcases h with ⟨hf₁, hg₁⟩
    have hf₂ : (f.translate x).degree ≤ m := degree_translate.trans_le hf₁
    have hg₂ : (g.translate x).degree ≤ n := degree_translate.trans_le hg₁
    ext P : 3 <;> simp [hf₁, hf₂, hg₁, hg₂, sylvesterMap_apply]
  · have h₁ : ¬((f.translate x).degree ≤ m ∧ (g.translate x).degree ≤ n) := by
      rwa [degree_translate, degree_translate]
    rw [sylvesterMap, dif_neg h, sylvesterMap, dif_neg h₁, LinearMap.comp_zero, LinearMap.zero_comp]

include hf hg in
lemma resultantAux_translate :
    resultantAux (f.translate x) (g.translate x) m n = resultantAux f g m n :=
  have hft : (f.translate x).degree ≤ m := degree_translate.trans_le hf
  have hgt : (g.translate x).degree ≤ n := degree_translate.trans_le hg
  calc
  _ = (sylvester (f.translate x) (g.translate x) m n).det := rfl
  _ = Matrix.det (LinearMap.toMatrix
        (degreeLT.basis_prod R n m) (degreeLT.basis R (n + m))
        (sylvesterMap (f.translate x) (g.translate x) ∘ₗ (translateProd x n m).toLinearMap)) := by
    rw [LinearMap.toMatrix_comp _ (degreeLT.basis_prod R n m), Matrix.det_mul,
      sylvesterMap_toMatrix hft hgt, LinearMap.det_toMatrix, translateProd_det', mul_one]
  _ = Matrix.det (LinearMap.toMatrix
        (degreeLT.basis_prod R n m) (degreeLT.basis R (n + m))
        ((translateLinear x _).toLinearMap ∘ₗ sylvesterMap f g (m := m) (n := n))) := by
    rw [translate_sylvesterMap]
  _ = (sylvester f g m n).det := by
    rw [LinearMap.toMatrix_comp _ (degreeLT.basis R (n + m)), Matrix.det_mul,
      sylvesterMap_toMatrix hf hg, LinearMap.det_toMatrix, translate_det', one_mul]

lemma resultant_translate :
    resultant (f.translate x) (g.translate x) = resultant f g := by
  rw [resultant, resultant, natDegree_translate, natDegree_translate, resultantAux_translate]

end translate


section field

variable {K : Type*} [Field K] {P Q : K[X]}

lemma resultant_eq_zero_iff :
    P.resultant Q = 0 ↔
      ∃ a b : K[X], a.degree < Q.natDegree ∧ b.degree < P.natDegree ∧ (a ≠ 0 ∨ b ≠ 0) ∧
        P * a + Q * b = 0 := by
  rw [← det_sylvesterMap (P:=P) (Q:=Q)]
  have := (LinearMap.hasEigenvalue_zero_tfae
    (P.sylvesterMap' Q ∘ₗ degreeLT.addLinearEquiv.toLinearMap)).out 3 5
  rw [this]
  refine ⟨fun ⟨m, hm, h⟩ ↦
      ⟨ (degreeLT.addLinearEquiv m).1,
        (degreeLT.addLinearEquiv m).2,
        ?_, ?_, ?_, ?_⟩,
    fun ⟨a, b, ha, hb, h₁, h₂⟩ ↦
      ⟨ degreeLT.addLinearEquiv.symm (⟨a, mem_degreeLT.2 ha⟩, ⟨b, mem_degreeLT.2 hb⟩),
        ?_, ?_⟩⟩
  · exact mem_degreeLT.1 (degreeLT.addLinearEquiv m).1.2
  · exact mem_degreeLT.1 (degreeLT.addLinearEquiv m).2.2
  · exact not_and_or.1 <| fun ⟨hm₁, hm₂⟩ ↦
      (LinearEquiv.map_ne_zero_iff _).2 hm <|
      Prod.ext (Subtype.ext hm₁) (Subtype.ext hm₂)
  · exact Subtype.ext_iff.1 h
  · exact (LinearEquiv.map_ne_zero_iff _).2 fun hab ↦ not_and_or.2 h₁ <|
      by rwa [Prod.mk_eq_zero, Submodule.mk_eq_zero, Submodule.mk_eq_zero] at hab
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact Subtype.ext h₂

lemma resultant_eq_zero_iff_not_coprime (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    P.resultant Q = 0 ↔ ¬IsCoprime P Q := by
  rw [resultant_eq_zero_iff]
  classical
  refine ⟨fun ⟨a, b, ha, hb, h₁, h₂⟩ hc ↦ ?_, fun h ↦
      ⟨Q / EuclideanDomain.gcd P Q, -(P / EuclideanDomain.gcd P Q), ?_⟩⟩
  · have hpq : P * a = Q * (-b) := by rw [mul_neg, eq_neg_iff_add_eq_zero, h₂]
    have hpb : P ∣ b := dvd_neg.1 <| hc.dvd_of_dvd_mul_left <| hpq ▸ dvd_mul_right _ _
    have hqa : Q ∣ a := hc.symm.dvd_of_dvd_mul_left <| hpq ▸ dvd_mul_right _ _
    cases h₁ with
    | inl ha0 => exact ha0 <| eq_zero_of_dvd_of_natDegree_lt hqa <| WithBot.coe_lt_coe.1 <|
        (a.degree_eq_natDegree ha0).symm.trans_lt ha
    | inr hb0 => exact hb0 <| eq_zero_of_dvd_of_natDegree_lt hpb <| WithBot.coe_lt_coe.1 <|
        (b.degree_eq_natDegree hb0).symm.trans_lt hb
  · have hg : EuclideanDomain.gcd P Q ≠ 0 :=
      EuclideanDomain.gcd_eq_zero_iff.not.2 (not_and_of_not_or_not hPQ)
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hq : Q = 0
      · simp [hq]
      · rw [← degree_eq_natDegree hq]
        exact degree_div_lt hq <| degree_pos_of_ne_zero_of_nonunit hg <|
          EuclideanDomain.gcd_isUnit_iff.not.2 h
    · by_cases hp : P = 0
      · simp [hp]
      · rw [← degree_eq_natDegree hp, degree_neg]
        exact degree_div_lt hp <| degree_pos_of_ne_zero_of_nonunit hg <|
          EuclideanDomain.gcd_isUnit_iff.not.2 h
    · simp [div_eq_zero_iff hg]
      exact hPQ.symm.imp (fun hq0 ↦ degree_le_of_dvd (EuclideanDomain.gcd_dvd_right _ _) hq0)
        (fun hp0 ↦ degree_le_of_dvd (EuclideanDomain.gcd_dvd_left _ _) hp0)
    · refine eq_zero_of_ne_zero_of_mul_right_eq_zero hg ?_
      rw [add_mul, mul_assoc, mul_comm (_/_),
        EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_right _ _),
        mul_assoc, neg_mul, mul_comm (_/_),
        EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_left _ _),
        mul_neg, mul_comm, add_neg_cancel]
-- could shorten this proof using Bezout?

end field


end Polynomial

#lint

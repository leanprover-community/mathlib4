/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.LinearAlgebra.Determinant

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
/-
d=2 e=1:
a0 b0
a1 b1 b0
a2    b1
-/
def sylvester (m n : ℕ) : Matrix (Fin (n+m)) (Fin (n+m)) R :=
fun i j ↦ j.addCases
  (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+m) then f.coeff (i - j₁) else 0)
  (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+n) then g.coeff (i - j₁) else 0)

theorem sylvester_comm {f g : R[X]} {m n : ℕ} :
  sylvester g f n m = (sylvester f g m n).submatrix
    (finCongr (add_comm m n))
    (finAddFlip) := by
  ext i j
  refine j.addCases (fun j₁ ↦ ?_) (fun j₁ ↦ ?_) <;> simp [sylvester]

lemma sylvester_one_zero : sylvester f g 1 0 = !![g.coeff 0] := by
  ext i j; fin_cases i; fin_cases j; simp [sylvester, Fin.addCases]

lemma sylvester_two_one : sylvester f g 2 1 =
  !![f.coeff 0, g.coeff 0, 0;
     f.coeff 1, g.coeff 1, g.coeff 0;
     f.coeff 2, 0,         g.coeff 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sylvester, Fin.addCases]

end sylvester


section resultant

def resultant : R :=
(sylvester f g f.natDegree g.natDegree : Matrix _ _ R).det

variable {f g}

theorem resultant_comm : g.resultant f =
    (-1) ^ (f.natDegree * g.natDegree) * f.resultant g := by
  rw [resultant, sylvester_comm, Matrix.det_submatrix', finCongr_symm, sign_finAddFlip']
  simp [resultant]

lemma resultant_C_C {x y : R} : resultant (C x) (C y) = 1 :=
have : IsEmpty (Fin ((C y).natDegree + (C x).natDegree)) := by
  convert Fin.isEmpty; simp only [natDegree_C, add_zero]
Matrix.det_isEmpty

lemma resultant_X_add_C_C {x y : R} : resultant (X + C x) (C y) = y := by
  nontriviality R
  rw [resultant, natDegree_X_add_C, natDegree_C, sylvester_one_zero,
    coeff_C_zero, Matrix.det_fin_one_of]

lemma resultant_C_X_add_C {x y : R} : resultant (C x) (X + C y) = x := by
  nontriviality R
  rw [resultant_comm, resultant_X_add_C_C, natDegree_X_add_C, natDegree_C]
  simp

lemma resultant_X_C {x : R} : resultant (X) (C x) = x := by
  convert resultant_X_add_C_C; rw [C_0, add_zero]

lemma resultant_C_X {x : R} : resultant (C x) X = x := by
  convert resultant_C_X_add_C; rw [C_0, add_zero]

end resultant

end Polynomial

#lint

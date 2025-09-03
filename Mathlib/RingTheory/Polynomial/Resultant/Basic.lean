/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Resultant of two polynomials

This file contains basic facts about resultant of two polynomials over commutative rings.

## Main definitions

* `Polynomial.resultant`: The resultant of two polynomials `p` and `q` is defined as the determinant
  of the Sylvester matrix of `p` and `q`.
* `Polynomial.disc`: The discriminant of a polynomial `f` is defined as the resultant of `f` and
  `f.derivative`, modified by factoring out a sign and a power of the leading term.

## TODO

* The eventual goal is to prove the following property:
  `resultant (∏ a ∈ s, (X - C a)) f = ∏ a ∈ s, f.eval a`.
  This allows us to write the `resultant f g` as the product of terms of the form `a - b` where `a`
  is a root of `f` and `b` is a root of `g`.
* A smaller intermediate goal is to show that the Sylvester matrix corresponds to the linear map
  that we will call the Sylvester map, which is `R[X]_n × R[X]_m →ₗ[R] R[X]_(n + m)` given by
  `(p, q) ↦ f * p + g * q`, where `R[X]_n` is
  `Polynomial.degreeLT` in `Mathlib.RingTheory.Polynomial.Basic`.
* Resultant of two binary forms (i.e. homogeneous polynomials in two variables), after binary forms
  are implemented.

-/

open Set

namespace Polynomial

section sylvester

variable {R : Type*} [Semiring R]

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively is a
`(n+m) × (n+m)` matrix with the coefficients of `f` and `g` arranged in a specific way. Here, `m`
and `n` are free variables, not necessarily equal to the actual degrees of the polynomials `f` and
`g`. -/
def sylvester (f g : R[X]) (m n : ℕ) : Matrix (Fin (n + m)) (Fin (n + m)) R :=
  .of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)

variable (f g : R[X]) (m n : ℕ)

@[simp] theorem sylvester_C_right (a : R) :
    sylvester f (C a) m 0 = Matrix.diagonal (fun _ ↦ a) :=
  Matrix.ext fun i j ↦ j.addCases nofun fun j ↦ by
    rw [sylvester, Matrix.of_apply, Fin.addCases_right, Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff]

/--
The Sylvester matrix for `f` and `f.derivative`, modified by dividing the bottom row by
the leading coefficient of `f`. Important because its determinant is (up to a sign) the
discriminant of `f`.
-/
noncomputable def
sylvesterDeriv (f : R[X]) :
    Matrix (Fin (f.natDegree - 1 + f.natDegree)) (Fin (f.natDegree - 1 + f.natDegree)) R :=
  letI n := f.natDegree
  if hn : n = 0 then 0
  else (f.sylvester f.derivative n (n - 1)).updateRow ⟨2 * n - 2, by omega⟩
    (fun j ↦ if ↑j = n - 2 then 1 else (if ↑j = 2 * n - 2 then n else 0))

/-- We can get the usual Sylvester matrix of `f` and `f.derivative` back from the modified one
by multiplying the last row by the leading coefficient of `f`. -/
lemma sylvesterDeriv_updateRow (f : R[X]) (hf : 0 < f.natDegree) :
    (sylvesterDeriv f).updateRow ⟨2 * f.natDegree - 2, by omega⟩
      (f.leadingCoeff • (sylvesterDeriv f ⟨2 * f.natDegree - 2, by omega⟩)) =
    (sylvester f f.derivative f.natDegree (f.natDegree - 1)) := by
  by_cases hn : f.natDegree = 0
  · ext ⟨i, hi⟩; omega
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [sylvesterDeriv, dif_neg hn]
  rcases ne_or_eq i (2 * f.natDegree - 2) with hi' | rfl
  · -- Top part of matrix
    rw [Matrix.updateRow_ne (Fin.ne_of_val_ne hi'),
      Matrix.updateRow_ne (Fin.ne_of_val_ne hi')]
  · -- Bottom row
    simp only [sylvester, Fin.addCases, mem_Icc, coeff_derivative, eq_rec_constant, leadingCoeff,
      Matrix.updateRow_self, Matrix.updateRow_apply, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Matrix.of_apply, Fin.castLT_mk, tsub_le_iff_right, Fin.cast_mk,
      Fin.subNat_mk, dite_eq_ite]
    split_ifs
    on_goal 2 => rw [show f.natDegree = 1 by omega]
    on_goal 3 =>
      rw [← Nat.cast_one (R := R), ← Nat.cast_add, show f.natDegree = 1 by omega]
      norm_num
    on_goal 6 => rw [← Nat.cast_one (R := R), ← Nat.cast_add]
    all_goals grind

end sylvester

section resultant

variable {R : Type*} [CommRing R]

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix of `f`
and `g`. The size arguments `m` and `n` are implemented as `optParam`, meaning that the default
values are `f.natDegree` and `g.natDegree` respectively, but they can also be specified to be
other values. -/
def resultant (f g : R[X]) (m : ℕ := f.natDegree) (n : ℕ := g.natDegree) : R :=
  (sylvester f g m n).det

variable (f g : R[X]) (m n : ℕ)

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
@[simp]
theorem resultant_C_zero_right (a : R) : resultant f (C a) m 0 = a ^ m := by simp [resultant]

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
theorem resultant_C_right (a : R) : resultant f (C a) m = a ^ m := by simp

end resultant

section disc

variable {R : Type*} [CommRing R]

/-- The discriminant of a polynomial, defined as the determinant of `f.sylvesterDeriv` modified
by a sign. The sign is chosen so polynomials over `ℝ` with all roots real have non-negative
discriminant. -/
noncomputable def disc (f : R[X]) : R :=
  f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)

/-- The discriminant of a constant polynomial is `1`. -/
@[simp] lemma disc_C (r : R) : disc (C r) = 1 := by
  let e : Fin ((C r).natDegree - 1 + (C r).natDegree) ≃ Fin 0 := finCongr (by simp)
  simp [disc, ← Matrix.det_reindex_self e]

/-- The discriminant of a linear polynomial is `1`. -/
lemma disc_of_degree_eq_one {f : R[X]} (hf : f.degree = 1) : disc f = 1 := by
  rw [← Nat.cast_one, degree_eq_iff_natDegree_eq_of_pos one_pos] at hf
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 1 := finCongr (by omega)
  have : f.sylvesterDeriv.reindex e e = !![1] := by
    have : NeZero (f.natDegree - 1 + f.natDegree) := ⟨by omega⟩
    ext ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨rfl⟩ : i = 0 := by omega
    obtain ⟨rfl⟩ : j = 0 := by omega
    simp [e, sylvesterDeriv, mul_comm, hf]
  simp [disc, ← Matrix.det_reindex_self e, this, hf]

/-- Standard formula for the discriminant of a quadratic polynomial. -/
lemma disc_of_degree_eq_two {f : R[X]} (hf : f.degree = 2) :
    disc f = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2 := by
  rw [← Nat.cast_two, degree_eq_iff_natDegree_eq_of_pos two_pos] at hf
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 3 := finCongr (by omega)
  rw [disc, ← Matrix.det_reindex_self e]
  have : f.sylvesterDeriv.reindex e e =
    !![f.coeff 0,     f.coeff 1,         0;
        f.coeff 1, 2 * f.coeff 2, f.coeff 1;
        1,                     0,         2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, sylvesterDeriv, sylvester, coeff_derivative, mul_comm, Fin.addCases,
        one_add_one_eq_two, hf, Fin.cast]
  simp only [this, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val, hf]
  ring_nf

/-- Relation between the resultant and the discriminant.

(Note this is actually false when `f` is a constant polynomial not equal to 1, so the assumption on
the degree is genuinely needed.) -/
lemma resultant_deriv {f : R[X]} (hf : 0 < f.degree) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.disc := by
  rw [← natDegree_pos_iff_degree_pos] at hf
  rw [resultant, ← sylvesterDeriv_updateRow f hf, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, disc]
  suffices ∀ (r s : R), s * r = s * r * (-1) ^ (f.natDegree * (f.natDegree - 1) / 2 * 2) by
    ring_nf
    apply this
  simp only [mul_comm _ 2, pow_mul, neg_one_sq, one_pow, mul_one, implies_true]

end disc

end Polynomial

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.HasseDeriv

#align_import data.polynomial.taylor from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Taylor expansions of polynomials

## Main declarations

* `Polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `Polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(Polynomial.hasseDeriv k f).eval r`
* `Polynomial.eq_zero_of_hasseDeriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/


noncomputable section

namespace Polynomial

open Polynomial

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : R[X] →ₗ[R] R[X] where
  toFun f := f.comp (X + C r)
  map_add' f g := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]
#align polynomial.taylor Polynomial.taylor

theorem taylor_apply : taylor r f = f.comp (X + C r) :=
  rfl
#align polynomial.taylor_apply Polynomial.taylor_apply

@[simp]
theorem taylor_X : taylor r X = X + C r := by simp only [taylor_apply, X_comp]
set_option linter.uppercaseLean3 false in
#align polynomial.taylor_X Polynomial.taylor_X

@[simp]
theorem taylor_C (x : R) : taylor r (C x) = C x := by simp only [taylor_apply, C_comp]
set_option linter.uppercaseLean3 false in
#align polynomial.taylor_C Polynomial.taylor_C

@[simp]
theorem taylor_zero' : taylor (0 : R) = LinearMap.id := by
  ext
  simp only [taylor_apply, add_zero, comp_X, _root_.map_zero, LinearMap.id_comp,
    Function.comp_apply, LinearMap.coe_comp]
#align polynomial.taylor_zero' Polynomial.taylor_zero'

theorem taylor_zero (f : R[X]) : taylor 0 f = f := by rw [taylor_zero', LinearMap.id_apply]
#align polynomial.taylor_zero Polynomial.taylor_zero

@[simp]
theorem taylor_one : taylor r (1 : R[X]) = C 1 := by rw [← C_1, taylor_C]
#align polynomial.taylor_one Polynomial.taylor_one

@[simp]
theorem taylor_monomial (i : ℕ) (k : R) : taylor r (monomial i k) = C k * (X + C r) ^ i := by
  simp [taylor_apply]
#align polynomial.taylor_monomial Polynomial.taylor_monomial

/-- The `k`th coefficient of `Polynomial.taylor r f` is `(Polynomial.hasseDeriv k f).eval r`. -/
theorem taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasseDeriv n f).eval r :=
  show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, coeff_C_mul,
      hasseDeriv_monomial, taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i,
      map_sum]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push_neg at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]
#align polynomial.taylor_coeff Polynomial.taylor_coeff

@[simp]
theorem taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r := by
  rw [taylor_coeff, hasseDeriv_zero, LinearMap.id_apply]
#align polynomial.taylor_coeff_zero Polynomial.taylor_coeff_zero

@[simp]
theorem taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r := by
  rw [taylor_coeff, hasseDeriv_one]
#align polynomial.taylor_coeff_one Polynomial.taylor_coeff_one

@[simp]
theorem natDegree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p := by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [taylor_monomial, natDegree_C_mul_eq_of_mul_ne_zero, natDegree_pow_X_add_C, c0]
#align polynomial.nat_degree_taylor Polynomial.natDegree_taylor

@[simp]
theorem taylor_mul {R} [CommSemiring R] (r : R) (p q : R[X]) :
    taylor r (p * q) = taylor r p * taylor r q := by simp only [taylor_apply, mul_comp]
#align polynomial.taylor_mul Polynomial.taylor_mul

/-- `Polynomial.taylor` as an `AlgHom` for commutative semirings -/
@[simps!]
def taylorAlgHom {R} [CommSemiring R] (r : R) : R[X] →ₐ[R] R[X] :=
  AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)
#align polynomial.taylor_alg_hom Polynomial.taylorAlgHom

theorem taylor_taylor {R} [CommSemiring R] (f : R[X]) (r s : R) :
    taylor r (taylor s f) = taylor (r + s) f := by
  simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, C_add, add_assoc]
#align polynomial.taylor_taylor Polynomial.taylor_taylor

theorem taylor_eval {R} [CommSemiring R] (r : R) (f : R[X]) (s : R) :
    (taylor r f).eval s = f.eval (s + r) := by
  simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]
#align polynomial.taylor_eval Polynomial.taylor_eval

theorem taylor_eval_sub {R} [CommRing R] (r : R) (f : R[X]) (s : R) :
    (taylor r f).eval (s - r) = f.eval s := by rw [taylor_eval, sub_add_cancel]
#align polynomial.taylor_eval_sub Polynomial.taylor_eval_sub

theorem taylor_injective {R} [CommRing R] (r : R) : Function.Injective (taylor r) := by
  intro f g h
  apply_fun taylor (-r) at h
  simpa only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, C_neg, neg_add_cancel_right,
    comp_X] using h
#align polynomial.taylor_injective Polynomial.taylor_injective

theorem eq_zero_of_hasseDeriv_eq_zero {R} [CommRing R] (f : R[X]) (r : R)
    (h : ∀ k, (hasseDeriv k f).eval r = 0) : f = 0 := by
  apply taylor_injective r
  rw [LinearMap.map_zero]
  ext k
  simp only [taylor_coeff, h, coeff_zero]
#align polynomial.eq_zero_of_hasse_deriv_eq_zero Polynomial.eq_zero_of_hasseDeriv_eq_zero

/-- Taylor's formula. -/
theorem sum_taylor_eq {R} [CommRing R] (f : R[X]) (r : R) :
    ((taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
  rw [← comp_eq_sum_left, sub_eq_add_neg, ← C_neg, ← taylor_apply, taylor_taylor, neg_add_self,
    taylor_zero]
#align polynomial.sum_taylor_eq Polynomial.sum_taylor_eq

end Polynomial

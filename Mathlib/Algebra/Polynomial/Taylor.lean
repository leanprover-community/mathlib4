/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.HasseDeriv

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

section Semiring

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : R[X] →ₗ[R] R[X] where
  toFun f := f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]

theorem taylor_apply : taylor r f = f.comp (X + C r) :=
  rfl

@[simp]
theorem taylor_X : taylor r X = X + C r := X_comp

@[simp]
theorem taylor_X_pow (n : ℕ) : taylor r (X ^ n) = (X + C r) ^ n := X_pow_comp

@[simp]
theorem taylor_C (x : R) : taylor r (C x) = C x := C_comp

theorem taylor_zero (f : R[X]) : taylor 0 f = f := by rw [taylor_apply, C_0, add_zero, comp_X]

@[simp]
theorem taylor_zero' : taylor (0 : R) = LinearMap.id := LinearMap.ext taylor_zero

@[simp]
theorem taylor_one : taylor r (1 : R[X]) = C 1 := taylor_C r 1

@[simp]
theorem taylor_monomial (i : ℕ) (k : R) : taylor r (monomial i k) = C k * (X + C r) ^ i := by
  simp [taylor_apply]

/-- The `k`th coefficient of `Polynomial.taylor r f` is `(Polynomial.hasseDeriv k f).eval r`. -/
theorem taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasseDeriv n f).eval r :=
  show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, map_sum,
      hasseDeriv_monomial, taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push_neg at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

@[simp]
theorem taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r := by
  rw [taylor_coeff, hasseDeriv_zero, LinearMap.id_apply]

@[simp]
theorem taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r := by
  rw [taylor_coeff, hasseDeriv_one]

@[simp]
theorem coeff_taylor_natDegree : (taylor r f).coeff f.natDegree = f.leadingCoeff := by
  by_cases hf : f = 0
  · rw [hf, map_zero, coeff_natDegree]
  · rw [taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C]

@[simp]
theorem natDegree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p := by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [taylor_monomial, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, c0]

@[simp]
theorem leadingCoeff_taylor : (taylor r f).leadingCoeff = f.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_taylor, coeff_taylor_natDegree, leadingCoeff]

@[simp]
theorem taylor_eq_zero : taylor r f = 0 ↔ f = 0 := by
  rw [← leadingCoeff_eq_zero, ← leadingCoeff_eq_zero, leadingCoeff_taylor]

@[simp]
theorem degree_taylor (p : R[X]) (r : R) : degree (taylor r p) = degree p := by
  by_cases hp : p = 0
  · rw [hp, map_zero]
  · rw [degree_eq_natDegree hp, degree_eq_iff_natDegree_eq ((taylor_eq_zero r p).not.2 hp),
      natDegree_taylor]

theorem eq_zero_of_hasseDeriv_eq_zero (f : R[X]) (r : R)
    (h : ∀ k, (hasseDeriv k f).eval r = 0) : f = 0 := by
  rw [← taylor_eq_zero r]
  ext k
  rw [taylor_coeff, h, coeff_zero]

end Semiring

section Ring

variable {R : Type*} [Ring R]

theorem taylor_injective (r : R) : Function.Injective (taylor r) :=
  (injective_iff_map_eq_zero' _).2 (taylor_eq_zero r)

@[simp] lemma taylor_inj {r : R} {p q : R[X]} :
    taylor r p = taylor r q ↔ p = q := (taylor_injective r).eq_iff

end Ring

section CommSemiring

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

@[simp]
theorem taylor_mul (p q : R[X]) : taylor r (p * q) = taylor r p * taylor r q := mul_comp ..

/-- `Polynomial.taylor` as an `AlgHom` for commutative semirings -/
@[simps!]
def taylorAlgHom (r : R) : R[X] →ₐ[R] R[X] :=
  AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

@[simp]
theorem taylor_pow (n : ℕ) : taylor r (f ^ n) = taylor r f ^ n :=
  (taylorAlgHom r).map_pow ..

@[simp, norm_cast] lemma coe_taylorAlgHom : taylorAlgHom r = taylor r :=
  rfl

theorem taylor_taylor (f : R[X]) (r s : R) : taylor r (taylor s f) = taylor (r + s) f := by
  simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, add_assoc]

theorem taylor_eval (r : R) (f : R[X]) (s : R) : (taylor r f).eval s = f.eval (s + r) := by
  simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

theorem eval_add_of_sq_eq_zero (p : R[X]) (x y : R) (hy : y ^ 2 = 0) :
    p.eval (x + y) = p.eval x + p.derivative.eval x * y := by
  rw [add_comm, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range' ((Nat.lt_succ_self _).trans (Nat.lt_succ_self _)),
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp [pow_succ, mul_assoc, ← pow_two, hy, add_comm (eval x p)]

theorem aeval_add_of_sq_eq_zero {S : Type*} [CommRing S] [Algebra R S]
    (p : R[X]) (x y : S) (hy : y ^ 2 = 0) :
    p.aeval (x + y) = p.aeval x + p.derivative.aeval x * y := by
  simp only [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ hy, derivative_map]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (r : R) (f : R[X])

/-- `Polynomial.taylor` as an `AlgEquiv` for commutative rings. -/
noncomputable def taylorEquiv (r : R) : R[X] ≃ₐ[R] R[X] where
  invFun      := taylorAlgHom (-r)
  left_inv P  := by simp [taylor, comp_assoc]
  right_inv P := by simp [taylor, comp_assoc]
  __ := taylorAlgHom r

@[simp, norm_cast] lemma toAlgHom_taylorEquiv : taylorEquiv r = taylorAlgHom r := rfl

@[simp, norm_cast] lemma coe_taylorEquiv : taylorEquiv r = taylor r := rfl

@[simp] lemma taylorEquiv_symm : (taylorEquiv r).symm = taylorEquiv (-r) :=
  AlgEquiv.ext fun _ ↦ rfl

theorem taylor_eval_sub (s : R) :
    (taylor r f).eval (s - r) = f.eval s := by rw [taylor_eval, sub_add_cancel]

/-- Taylor's formula. -/
theorem sum_taylor_eq (f : R[X]) (r : R) :
    ((taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
  rw [← comp_eq_sum_left, sub_eq_add_neg, ← C_neg, ← taylor_apply, taylor_taylor, neg_add_cancel,
    taylor_zero]

end CommRing

end Polynomial

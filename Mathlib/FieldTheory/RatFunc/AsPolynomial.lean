/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content

/-!
# Generalities on the polynomial structure of rational functions

## Main definitions
- `RatFunc.C` is the constant polynomial
- `RatFunc.X` is the indeterminate
- `RatFunc.eval` evaluates a rational function given a value for the indeterminate
-/

noncomputable section

universe u

variable {K : Type u}

namespace RatFunc

section Eval

open scoped Classical

open scoped nonZeroDivisors Polynomial

open RatFunc

/-! ### Polynomial structure: `C`, `X`, `eval` -/

section Domain

variable [CommRing K] [IsDomain K]

/-- `RatFunc.C a` is the constant rational function `a`. -/
def C : K →+* RatFunc K := algebraMap _ _
set_option linter.uppercaseLean3 false in #align ratfunc.C RatFunc.C

@[simp]
theorem algebraMap_eq_C : algebraMap K (RatFunc K) = C :=
  rfl
set_option linter.uppercaseLean3 false in #align ratfunc.algebra_map_eq_C RatFunc.algebraMap_eq_C

@[simp]
theorem algebraMap_C (a : K) : algebraMap K[X] (RatFunc K) (Polynomial.C a) = C a :=
  rfl
set_option linter.uppercaseLean3 false in #align ratfunc.algebra_map_C RatFunc.algebraMap_C

@[simp]
theorem algebraMap_comp_C : (algebraMap K[X] (RatFunc K)).comp Polynomial.C = C :=
  rfl
set_option linter.uppercaseLean3 false in #align ratfunc.algebra_map_comp_C RatFunc.algebraMap_comp_C

theorem smul_eq_C_mul (r : K) (x : RatFunc K) : r • x = C r * x := by
  rw [Algebra.smul_def, algebraMap_eq_C]
set_option linter.uppercaseLean3 false in #align ratfunc.smul_eq_C_mul RatFunc.smul_eq_C_mul

/-- `RatFunc.X` is the polynomial variable (aka indeterminate). -/
def X : RatFunc K :=
  algebraMap K[X] (RatFunc K) Polynomial.X
set_option linter.uppercaseLean3 false in #align ratfunc.X RatFunc.X

@[simp]
theorem algebraMap_X : algebraMap K[X] (RatFunc K) Polynomial.X = X :=
  rfl
set_option linter.uppercaseLean3 false in #align ratfunc.algebra_map_X RatFunc.algebraMap_X

end Domain

section Field

variable [Field K]

@[simp]
theorem num_C (c : K) : num (C c) = Polynomial.C c :=
  num_algebraMap _
set_option linter.uppercaseLean3 false in #align ratfunc.num_C RatFunc.num_C

@[simp]
theorem denom_C (c : K) : denom (C c) = 1 :=
  denom_algebraMap _
set_option linter.uppercaseLean3 false in #align ratfunc.denom_C RatFunc.denom_C

@[simp]
theorem num_X : num (X : RatFunc K) = Polynomial.X :=
  num_algebraMap _
set_option linter.uppercaseLean3 false in #align ratfunc.num_X RatFunc.num_X

@[simp]
theorem denom_X : denom (X : RatFunc K) = 1 :=
  denom_algebraMap _
set_option linter.uppercaseLean3 false in #align ratfunc.denom_X RatFunc.denom_X

theorem X_ne_zero : (X : RatFunc K) ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
set_option linter.uppercaseLean3 false in #align ratfunc.X_ne_zero RatFunc.X_ne_zero

variable {L : Type u} [Field L]

/-- Evaluate a rational function `p` given a ring hom `f` from the scalar field
to the target and a value `x` for the variable in the target.

Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/
def eval (f : K →+* L) (a : L) (p : RatFunc K) : L :=
  (num p).eval₂ f a / (denom p).eval₂ f a
#align ratfunc.eval RatFunc.eval

variable {f : K →+* L} {a : L}

theorem eval_eq_zero_of_eval₂_denom_eq_zero {x : RatFunc K}
    (h : Polynomial.eval₂ f a (denom x) = 0) : eval f a x = 0 := by rw [eval, h, div_zero]
#align ratfunc.eval_eq_zero_of_eval₂_denom_eq_zero RatFunc.eval_eq_zero_of_eval₂_denom_eq_zero

theorem eval₂_denom_ne_zero {x : RatFunc K} (h : eval f a x ≠ 0) :
    Polynomial.eval₂ f a (denom x) ≠ 0 :=
  mt eval_eq_zero_of_eval₂_denom_eq_zero h
#align ratfunc.eval₂_denom_ne_zero RatFunc.eval₂_denom_ne_zero

variable (f a)

@[simp]
theorem eval_C {c : K} : eval f a (C c) = f c := by simp [eval]
set_option linter.uppercaseLean3 false in #align ratfunc.eval_C RatFunc.eval_C

@[simp]
theorem eval_X : eval f a X = a := by simp [eval]
set_option linter.uppercaseLean3 false in #align ratfunc.eval_X RatFunc.eval_X

@[simp]
theorem eval_zero : eval f a 0 = 0 := by simp [eval]
#align ratfunc.eval_zero RatFunc.eval_zero

@[simp]
theorem eval_one : eval f a 1 = 1 := by simp [eval]
#align ratfunc.eval_one RatFunc.eval_one

@[simp]
theorem eval_algebraMap {S : Type*} [CommSemiring S] [Algebra S K[X]] (p : S) :
    eval f a (algebraMap _ _ p) = (algebraMap _ K[X] p).eval₂ f a := by
  simp [eval, IsScalarTower.algebraMap_apply S K[X] (RatFunc K)]
#align ratfunc.eval_algebra_map RatFunc.eval_algebraMap

/-- `eval` is an additive homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 1 (X / (X-1)) + eval _ 1 (-1 / (X-1)) = 0`
`... ≠ 1 = eval _ 1 ((X-1) / (X-1))`.

See also `RatFunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
theorem eval_add {x y : RatFunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x + y) = eval f a x + eval f a y := by
  unfold eval
  by_cases hxy : Polynomial.eval₂ f a (denom (x + y)) = 0
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_add_dvd x y) hxy
    rw [Polynomial.eval₂_mul] at this
    cases mul_eq_zero.mp this <;> contradiction
  rw [div_add_div _ _ hx hy, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  simp only [← Polynomial.eval₂_mul, ← Polynomial.eval₂_add]
  congr 1
  apply num_denom_add
#align ratfunc.eval_add RatFunc.eval_add

/-- `eval` is a multiplicative homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 0 X * eval _ 0 (1/X) = 0 ≠ 1 = eval _ 0 1 = eval _ 0 (X * 1/X)`.

See also `RatFunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
theorem eval_mul {x y : RatFunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x * y) = eval f a x * eval f a y := by
  unfold eval
  by_cases hxy : Polynomial.eval₂ f a (denom (x * y)) = 0
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_mul_dvd x y) hxy
    rw [Polynomial.eval₂_mul] at this
    cases mul_eq_zero.mp this <;> contradiction
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  repeat' rw [← Polynomial.eval₂_mul]
  congr 1
  apply num_denom_mul
#align ratfunc.eval_mul RatFunc.eval_mul

end Field

end Eval

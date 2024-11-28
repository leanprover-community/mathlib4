/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Hilbert polynomials

In this file, we formalise the following statement: if `F` is a field with characteristic `0`, then
given any `p : F[X]` and `d : ℕ`, there exists some `h : F[X]` such that for any large enough
`n : ℕ`, `h(n)` is equal to the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
This `h` is unique and is called the Hilbert polynomial of `p` and `d` (`Polynomial.hilbert p d`).

## Main definitions

* `Polynomial.hilbert p d`. If `F` is a field with characteristic `0`, `p : F[X]` and `d : ℕ`, then
  `Polynomial.hilbert p d : F[X]` is the polynomial whose value at `n` equals the coefficient of
  `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`

## TODO

* Prove that `Polynomial.hilbert p d : F[X]` is the polynomial whose value at `n` equals the
  coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`

* Hilbert polynomials of graded modules.
-/

open BigOperators Nat PowerSeries

namespace Polynomial

section greatestFactorOneSubNotDvd

variable {R : Type*} [CommRing R] (p : R[X]) (hp : p ≠ 0) (d : ℕ)

/--
Given a polynomial `p`, the factor `f` of `p` such that the product of `f` and
`(1 - X : R[X]) ^ p.rootMultiplicity 1` equals `p`. We define this here because if `p` is divisible
by `1 - X`, then the expression `p/(1 - X)ᵈ` can be reduced. We want to construct the Hilbert
polynomial based on the most reduced form of the fraction `p/(1 - X)ᵈ`. Later we will see that this
method of construction makes it much easier to calculate the specific degree of the Hilbert
polynomial.
-/
noncomputable def greatestFactorOneSubNotDvd : R[X] :=
  ((- 1 : R[X]) ^ p.rootMultiplicity 1) *
  (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose

end greatestFactorOneSubNotDvd

variable (F : Type*) [Field F] [CharZero F]

/--
A polynomial which makes it easier to define the Hilbert polynomial. See also the theorem
`Polynomial.preHilbert_eq_choose_sub_add`, which states that for any `d k n : ℕ` with `k ≤ n`,
`(Polynomial.preHilbert d k).eval (n : F) = (n - k + d).choose d`.
-/
noncomputable def preHilbert (d k : ℕ) : F[X] :=
  (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) + 1))

theorem preHilbert_eq_choose_sub_add (d k n : ℕ) (hkn : k ≤ n):
    (preHilbert F d k).eval (n : F) = (n - k + d).choose d := by
  rw [preHilbert, eval_smul, eval_comp, map_natCast, eval_add, eval_sub, eval_X, eval_natCast,
    eval_one, smul_eq_mul, ← cast_sub hkn, ← cast_add_one, ← ascPochhammer_eval_cast,
    ascPochhammer_nat_eq_ascFactorial, ascFactorial_eq_factorial_mul_choose, cast_mul,
    ← mul_assoc]
  simp only [isUnit_iff_ne_zero, ne_eq, Ne.symm <| @NeZero.ne' _ _ _ <| @NeZero.charZero _ _
    ⟨factorial_ne_zero d⟩ .., not_false_eq_true, IsUnit.inv_mul_cancel, one_mul]

variable {F}

/--
Given `p : F[X]` and `d : ℕ`, the Hilbert polynomial of `p` and `d`. Later we will
show that `PowerSeries.coeff F n (p * (PowerSeries.invOneSubPow F d))` is equal to
`(Polynomial.hilbert p d).eval (n : F)` for any large enough `n : ℕ`, which is the
key property of the Hilbert polynomial.
-/
noncomputable def hilbert (p : F[X]) (d : ℕ) : F[X] :=
  let _ := Classical.propDecidable (p = 0)
  if h : p = 0 then 0
  else if d ≤ p.rootMultiplicity 1 then 0
  else ∑ i in Finset.range ((greatestFactorOneSubNotDvd p h).natDegree + 1),
  ((greatestFactorOneSubNotDvd p h).coeff i) • preHilbert F (d - (p.rootMultiplicity 1) - 1) i

end Polynomial

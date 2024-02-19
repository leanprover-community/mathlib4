/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Complex.Basic

/-!
# Coercion to complex-valued arithmetic functions

This file defines coercions from arithmetic functions with values in some commutative
(semi)ring `R` to arithmetic functions with values in `ℂ`, given that `ℂ` is an `R`-algebra.
This is necessary to be able to write `LSeries f` when `f : ArithmeticFunction ℤ` (say),
as `LSeries` requires an arithmetic function with values in `ℂ` as input.
-/

namespace ArithmeticFunction

section toComplex

/-!
### Definition and compatibility with operations
-/

variable {R : Type*} [CommSemiring R] [Algebra R ℂ]

/-- Coerce an arithmetic function with values in `R` to one with values in `ℂ`.
We cannot inline this in `instToComplexAritmeticFunction` because it gets unfolded too much. -/
@[coe] def toComplexArithmeticFunction (f : ArithmeticFunction R) : ArithmeticFunction ℂ where
  toFun n := algebraMap R ℂ (f n)
  map_zero' := by simp only [map_zero, _root_.map_zero]

instance instToComplexAritmeticFunction : CoeHead (ArithmeticFunction R) (ArithmeticFunction ℂ) :=
  ⟨toComplexArithmeticFunction (R := R)⟩

@[simp]
lemma toComplexArithmeticFunction_apply {f : ArithmeticFunction R} {n : ℕ} :
    (f : ArithmeticFunction ℂ) n = algebraMap R ℂ (f n) := rfl

@[simp, norm_cast]
lemma toComplexArithmeticFunction_add {f g : ArithmeticFunction R} :
    (↑(f + g) : ArithmeticFunction ℂ) = ↑f + g := by
  ext
  simp only [toComplexArithmeticFunction_apply, add_apply, map_add]

@[simp, norm_cast]
lemma toComplexArithmeticFunction_mul {f g : ArithmeticFunction R} :
    (↑(f * g) : ArithmeticFunction ℂ) = ↑f * g := by
  ext
  simp only [toComplexArithmeticFunction_apply, mul_apply, map_sum, map_mul]

@[simp, norm_cast]
lemma toComplexArithmeticFunction_pmul {f g : ArithmeticFunction R} :
    (↑(pmul f g) : ArithmeticFunction ℂ) = pmul (f : ArithmeticFunction ℂ) (↑g) := by
  ext
  simp only [toComplexArithmeticFunction_apply, pmul_apply, map_mul]

open Nat in
@[simp, norm_cast]
lemma toComplexArithmeticFunction_ppow {f : ArithmeticFunction R} {n : ℕ} :
    (↑(ppow f n) : ArithmeticFunction ℂ) = ppow (f : ArithmeticFunction ℂ) n := by
  ext m
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [ppow_zero, toComplexArithmeticFunction_apply, natCoe_apply, zeta_apply, cast_ite,
      cast_zero, cast_one, RingHom.map_ite_zero_one, CharP.cast_eq_zero]
  · simp only [toComplexArithmeticFunction_apply, ppow_apply hn, map_pow]

end toComplex

section nat_int_real

/-!
### Injectivity and transitivity
-/

open Complex in
lemma toComplexArithmeticFunction_real_injective :
    Function.Injective (toComplexArithmeticFunction (R := ℝ)) := by
  intro f g hfg
  ext n
  simpa only [toComplexArithmeticFunction_apply, coe_algebraMap, ofReal_inj]
    using congr_arg (· n) hfg

@[simp, norm_cast]
lemma toComplexArithmeticFunction_real_inj {f g : ArithmeticFunction ℝ} :
    (f : ArithmeticFunction ℂ) = g ↔ f = g :=
  toComplexArithmeticFunction_real_injective.eq_iff

lemma toComplexArithmeticFunction_int_injective :
    Function.Injective (toComplexArithmeticFunction (R := ℤ)) := by
  intro f g hfg
  ext n
  simpa only [toComplexArithmeticFunction_apply, algebraMap_int_eq, eq_intCast, Int.cast_inj]
    using congr_arg (· n) hfg

@[simp, norm_cast]
lemma toComplexArithmeticFunction_int_inj {f g : ArithmeticFunction ℤ} :
    (f : ArithmeticFunction ℂ) = g ↔ f = g :=
  toComplexArithmeticFunction_int_injective.eq_iff

lemma toComplexArithmeticFunction_nat_injective :
    Function.Injective (toComplexArithmeticFunction (R := ℕ)) := by
  intro f g hfg
  ext n
  simpa only [toComplexArithmeticFunction_apply, eq_natCast, Nat.cast_inj]
    using congr_arg (· n) hfg

@[simp, norm_cast]
lemma toComplexArithmeticFunction_nat_inj {f g : ArithmeticFunction ℕ} :
    (f : ArithmeticFunction ℂ) = g ↔ f = g :=
  toComplexArithmeticFunction_nat_injective.eq_iff

@[norm_cast]
lemma toComplexArithmeticFunction_real_int {f : ArithmeticFunction ℤ} :
    ((f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ) = f := rfl

@[norm_cast]
lemma toComplexArithmeticFunction_real_nat {f : ArithmeticFunction ℕ} :
    ((f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ) = f := rfl

@[norm_cast]
lemma toComplexArithmeticFunction_int_nat {f : ArithmeticFunction ℕ} :
    ((f : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) = f := rfl

end nat_int_real

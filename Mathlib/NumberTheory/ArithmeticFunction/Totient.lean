/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Euler's totient function as an arithmetic function

## Main definitions

* `ArithmeticFunction.totient`: Euler's totient function `φ`, seen as an arithmetic function.

## Main results

* `ArithmeticFunction.isMultiplicative_totient`: the totient function is multiplicative.
* `ArithmeticFunction.totient_mul_zeta`: Gauss's identity `φ * ζ = id`.
* `ArithmeticFunction.coe_moebius_mul_coe_id`: `μ * id = φ`.
-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

open scoped zeta Moebius

/-- Euler's totient function `φ` as an arithmetic function. -/
def totient : ArithmeticFunction ℕ :=
  ⟨Nat.totient, Nat.totient_zero⟩

@[simp]
theorem totient_apply {n : ℕ} : totient n = n.totient := rfl

@[arith_mult]
theorem isMultiplicative_totient : IsMultiplicative totient :=
  ⟨rfl, Nat.totient_mul⟩

/-- Gauss's identity `∑ d ∣ n, φ d = n`, as an identity of arithmetic functions. -/
@[simp]
theorem totient_mul_zeta : totient * ζ = .id := by
  ext n
  simp_rw [mul_zeta_apply, id_apply, totient_apply, sum_totient]

@[simp]
theorem zeta_mul_totient : ζ * totient = .id := by
  rw [mul_comm, totient_mul_zeta]

theorem coe_moebius_mul_coe_id [Ring R] :
    (μ * ArithmeticFunction.id : ArithmeticFunction R) = totient := by
  rw [← zeta_mul_totient, natCoe_mul, ← mul_assoc, coe_moebius_mul_coe_zeta, one_mul]

theorem coe_id_mul_coe_moebius [Ring R] :
    (ArithmeticFunction.id * μ : ArithmeticFunction R) = totient := by
  rw [← totient_mul_zeta, natCoe_mul, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

/-- The product of the totients of the lcm and of the gcd of two natural numbers is the product
of their totients. -/
theorem _root_.Nat.totient_lcm_mul_totient_gcd (m n : ℕ) :
    (m.lcm n).totient * (m.gcd n).totient = m.totient * n.totient :=
  isMultiplicative_totient.lcm_apply_mul_gcd_apply

end ArithmeticFunction

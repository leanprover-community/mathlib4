/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Lemmas about `ℤᵐ⁰`.
-/

assert_not_exists Ring

open Multiplicative

namespace WithZero

@[deprecated exp_zsmul (since := "2025-05-17")]
theorem ofAdd_zpow (a : ℤ) : (↑(ofAdd a) : ℤᵐ⁰) = ofAdd (1 : ℤ) ^ a :=
  show exp a = exp 1 ^ a by simp

@[deprecated exp_neg (since := "2025-05-17")]
theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤᵐ⁰) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a :=
  show (exp (-1 : ℤ) ^ (-a)) ^ n = exp (n : ℤ) ^ a by
    simp [mul_comm]

end WithZero

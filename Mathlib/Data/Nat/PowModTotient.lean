/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# Modular exponentiation with the totient function

This file contains lemmas about modular exponentiation.
In particular, it contains lemmas showing that an exponent can be reduced modulo the totient
function when the base is coprime to the modulus.

## Main Results

* `pow_totient_mod`: If `x` is coprime to `n`, then the modular exponentiation
  `x ^ k % n` can be reduced to `x ^ (k % φ n) % n`.

## TODOs

- Extend to results in cases where the base is not coprime to the modulus.
- Write a tactic or simproc that can automatically reduce exponents
  or towers of exponents using these results.

-/

namespace Nat

lemma pow_totient_mod_eq_one {x n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ φ n) % n = 1 := by
  exact mod_eq_of_modEq (ModEq.pow_totient h) hn

lemma pow_add_totient_mod_eq {x k n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ (k + φ n)) % n = (x ^ k) % n := by
  rw [pow_add, mul_mod, pow_totient_mod_eq_one hn h]
  simp only [mul_one, dvd_refl, mod_mod_of_dvd]

lemma pow_add_mul_totient_mod_eq {x k l n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ (k + l * φ n)) % n = (x ^ k) % n := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [add_mul, one_mul, ← add_assoc, pow_add_totient_mod_eq hn h, ih]

lemma pow_totient_mod {x k n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    x ^ k % n = x ^ (k % φ n) % n := by
  rw [← div_add_mod' k (φ n), add_comm, pow_add_mul_totient_mod_eq hn h, add_mul_mod_self_right,
    mod_mod k (φ n)]

end Nat

/-
Copyright (c) 2025 Aakash Ali. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aakash Ali
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Concrete CRT instances for moduli 7 and 11

This file provides concrete instances of the Chinese Remainder Theorem
for the specific coprime pair (7, 11), with explicit Bezout witnesses.

The general CRT is in Mathlib.RingTheory.ChineseRemainder.

## Main results

- crt_7_11_coprime
- crt_7_11_bezout
- crt_7_11_existence
- crt_7_11_uniqueness
-/

namespace CRT711

/-- 7 and 11 are coprime. -/
theorem crt_7_11_coprime : Nat.Coprime 7 11 := by decide

/-- Bezout coefficients: 2 * 11 % 7 = 1 and 8 * 7 % 11 = 1. -/
theorem crt_7_11_bezout : 2 * 11 % 7 = 1 /\ 8 * 7 % 11 = 1 := by decide

/-- Witness mod 7. -/
theorem crt_7_11_witness_mod7 (a b : Nat) (ha : a < 7) (_ : b < 11) :
    (a * 22 + b * 56) % 77 % 7 = a := by omega

/-- Witness mod 11. -/
theorem crt_7_11_witness_mod11 (a b : Nat) (_ : a < 7) (hb : b < 11) :
    (a * 22 + b * 56) % 77 % 11 = b := by omega

/-- Existence: for any a < 7 and b < 11, there exists x < 77 with x % 7 = a and x % 11 = b. -/
theorem crt_7_11_existence (a b : Nat) (ha : a < 7) (hb : b < 11) :
    Exists (fun x : Nat => x < 77 /\ x % 7 = a /\ x % 11 = b) :=
  ⟨(a * 22 + b * 56) % 77, by omega,
   crt_7_11_witness_mod7 a b ha hb,
   crt_7_11_witness_mod11 a b ha hb⟩

/-- Uniqueness mod 77. -/
theorem crt_7_11_uniqueness (x y : Nat) (h7 : x % 7 = y % 7) (h11 : x % 11 = y % 11) :
    x % 77 = y % 77 := by omega

/-- All 77 pairs have distinct witnesses. -/
theorem crt_7_11_all_pairs :
    forall a1 b1 a2 b2 : Nat, a1 < 7 -> b1 < 11 -> a2 < 7 -> b2 < 11 ->
    (a1 * 22 + b1 * 56) % 77 = (a2 * 22 + b2 * 56) % 77 ->
    a1 = a2 /\ b1 = b2 := by
  intro a1 b1 a2 b2 ha1 hb1 ha2 hb2 heq
  constructor <;> omega

end CRT711

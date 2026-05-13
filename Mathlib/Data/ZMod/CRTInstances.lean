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

The general CRT is in Mathlib.RingTheory.ChineseRemainder. This file
complements it with computable, fully explicit witnesses for the pair
(7, 11), where the modulus is 77 = 7 * 11.

## Main results

- crt_7_11_coprime : Nat.Coprime 7 11
- crt_7_11_bezout : the Bezout identity 2 * 11 % 7 = 1 and 8 * 7 % 11 = 1
- crt_7_11_witness_mod7 : the witness (a * 22 + b * 56) % 77 satisfies x == a (mod 7)
- crt_7_11_witness_mod11 : and satisfies x == b (mod 11)
- crt_7_11_existence : existence of a solution for every pair (a, b) with  < 7,  < 11
- crt_7_11_uniqueness : the solution is unique mod 77

## Notes

The Bezout coefficients used here are 22 = 2 * 11 and 56 = 8 * 7, satisfying:
- 22 == 1 (mod 7), 22 == 0 (mod 11)
- 56 == 0 (mod 7), 56 == 1 (mod 11)
-/

namespace CRT711

/-! ### Coprimality -/

/-- 7 and 11 are coprime. -/
theorem crt_7_11_coprime : Nat.Coprime 7 11 := by decide

/-! ### Bezout identity -/

/-- The Bezout coefficients for (7, 11):
    2 * 11 == 1 (mod 7) and 8 * 7 == 1 (mod 11). -/
theorem crt_7_11_bezout : 2 * 11 % 7 = 1 /\ 8 * 7 % 11 = 1 := by decide

/-! ### The explicit witness -/

/-- The CRT witness for (7, 11) is x = (a * 22 + b * 56) % 77. -/
theorem crt_7_11_witness_mod7 (a b : Nat) (ha : a < 7) (_ : b < 11) :
    (a * 22 + b * 56) % 77 % 7 = a := by omega

/-- See crt_7_11_witness_mod7. -/
theorem crt_7_11_witness_mod11 (a b : Nat) (_ : a < 7) (hb : b < 11) :
    (a * 22 + b * 56) % 77 % 11 = b := by omega

/-! ### Existence and uniqueness -/

/-- For any  < 7 and  < 11, there exists x < 77 with
    x % 7 = a and x % 11 = b. -/
theorem crt_7_11_existence (a b : Nat) (ha : a < 7) (hb : b < 11) :
    Exists (fun x : Nat => x < 77 /\ x % 7 = a /\ x % 11 = b) :=
  ⟨(a * 22 + b * 56) % 77,
   by omega,
   crt_7_11_witness_mod7 a b ha hb,
   crt_7_11_witness_mod11 a b ha hb⟩

/-- The solution is unique mod 77. -/
theorem crt_7_11_uniqueness (x y : Nat) (h7 : x % 7 = y % 7) (h11 : x % 11 = y % 11) :
    x % 77 = y % 77 := by omega

/-- All 77 pairs have distinct witnesses mod 77. -/
theorem crt_7_11_all_pairs :
    forall a1 b1 a2 b2 : Nat, a1 < 7 -> b1 < 11 -> a2 < 7 -> b2 < 11 ->
    (a1 * 22 + b1 * 56) % 77 = (a2 * 22 + b2 * 56) % 77 ->
    a1 = a2 /\ b1 = b2 := by
  intro a1 b1 a2 b2 ha1 hb1 ha2 hb2 heq
  constructor <;> omega

end CRT711

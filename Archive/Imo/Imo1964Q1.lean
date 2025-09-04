/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# IMO 1964 Q1

(a) Find all positive integers $n$ for which $2^n-1$ is divisible by $7$.
(b) Prove that there is no positive integer $n$ for which $2^n+1$ is divisible by $7$.

For (a), we find that the order of $2$ mod $7$ is $3$. Therefore for (b), it suffices to check
$n = 0, 1, 2$.
-/

open Nat

namespace Imo1964Q1

theorem two_pow_mod_seven (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 3) [MOD 7] :=
  let t := n % 3
  calc 2 ^ n = 2 ^ (3 * (n / 3) + t) := by rw [Nat.div_add_mod]
    _ = (2 ^ 3) ^ (n / 3) * 2 ^ t := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (n / 3) * 2 ^ t [MOD 7] := by gcongr; decide
    _ = 2 ^ t := by ring

end Imo1964Q1

open Imo1964Q1

theorem imo1964_q1a (n : ℕ) (_ : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  let t := n % 3
  have : t < 3 := Nat.mod_lt _ (by decide)
  calc 7 ∣ 2 ^ n - 1 ↔ 2 ^ n ≡ 1 [MOD 7] := by
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
        apply Nat.one_le_pow'
    _ ↔ 2 ^ t ≡ 1 [MOD 7] := ⟨(two_pow_mod_seven n).symm.trans, (two_pow_mod_seven n).trans⟩
    _ ↔ t = 0 := by interval_cases t <;> decide
    _ ↔ 3 ∣ n := by rw [dvd_iff_mod_eq_zero]

theorem imo1964_q1b (n : ℕ) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  let t := n % 3
  have : t < 3 := Nat.mod_lt _ (by decide)
  have H : 2 ^ t + 1 ≡ 0 [MOD 7] := calc
    2 ^ t + 1 ≡ 2 ^ n + 1 [MOD 7] := by gcongr ?_ + 1; exact (two_pow_mod_seven n).symm
      _ ≡ 0 [MOD 7] := h.modEq_zero_nat
  interval_cases t <;> contradiction

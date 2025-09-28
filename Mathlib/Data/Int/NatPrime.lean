/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic

/-!
# Lemmas about `Nat.Prime` using `Int`s
-/


open Nat

namespace Int

theorem not_prime_of_int_mul {a b : ℤ} {c : ℕ} (ha : a.natAbs ≠ 1) (hb : b.natAbs ≠ 1)
    (hc : a * b = (c : ℤ)) : ¬Nat.Prime c :=
  not_prime_of_mul_eq (natAbs_mul_natAbs_eq hc) ha hb

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Nat.Prime p) {m n : ℤ}
    {k l : ℕ} (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
  have hpm' : p ^ k ∣ m.natAbs := Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hpm
  have hpn' : p ^ l ∣ n.natAbs := Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
    rw [← Int.natAbs_mul]; apply Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hpmn
  let hsd := Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn'
  hsd.elim (fun hsd1 => Or.inl (by apply Int.dvd_natAbs.1; apply Int.natCast_dvd_natCast.2 hsd1))
    fun hsd2 => Or.inr (by apply Int.dvd_natAbs.1; apply Int.natCast_dvd_natCast.2 hsd2)

theorem Prime.dvd_natAbs_of_coe_dvd_sq {p : ℕ} (hp : p.Prime) (k : ℤ) (h : (p : ℤ) ∣ k ^ 2) :
    p ∣ k.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← natAbs_mul, ← natCast_dvd, ← sq]

end Int

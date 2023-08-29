/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
import Mathlib.Data.Nat.Prime

#align_import data.int.nat_prime from "leanprover-community/mathlib"@"422e70f7ce183d2900c586a8cda8381e788a0c62"

/-!
# Lemmas about `Nat.Prime` using `Int`s
-/


open Nat

namespace Int

theorem not_prime_of_int_mul {a b : ℤ} {c : ℕ} (ha : 1 < a.natAbs) (hb : 1 < b.natAbs)
    (hc : a * b = (c : ℤ)) : ¬Nat.Prime c :=
  not_prime_mul' (natAbs_mul_natAbs_eq hc) ha hb
#align int.not_prime_of_int_mul Int.not_prime_of_int_mul

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Nat.Prime p) {m n : ℤ}
    {k l : ℕ} (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
  have hpm' : p ^ k ∣ m.natAbs := Int.coe_nat_dvd.1 <| Int.dvd_natAbs.2 hpm
  have hpn' : p ^ l ∣ n.natAbs := Int.coe_nat_dvd.1 <| Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
    rw [← Int.natAbs_mul]; apply Int.coe_nat_dvd.1 <| Int.dvd_natAbs.2 hpmn
    -- ⊢ p ^ (k + l + 1) ∣ natAbs (m * n)
                           -- 🎉 no goals
  let hsd := Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn'
  hsd.elim (fun hsd1 => Or.inl (by apply Int.dvd_natAbs.1; apply Int.coe_nat_dvd.2 hsd1))
                                   -- ⊢ ↑(p ^ (k + 1)) ∣ ↑(natAbs m)
                                                           -- 🎉 no goals
    fun hsd2 => Or.inr (by apply Int.dvd_natAbs.1; apply Int.coe_nat_dvd.2 hsd2)
                           -- ⊢ ↑(p ^ (l + 1)) ∣ ↑(natAbs n)
                                                   -- 🎉 no goals
#align int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul

theorem Prime.dvd_natAbs_of_coe_dvd_sq {p : ℕ} (hp : p.Prime) (k : ℤ) (h : (p : ℤ) ∣ k ^ 2) :
    p ∣ k.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  -- ⊢ p ∣ natAbs k ^ 2
  rwa [sq, ← natAbs_mul, ← coe_nat_dvd_left, ← sq]
  -- 🎉 no goals
#align int.prime.dvd_nat_abs_of_coe_dvd_sq Int.Prime.dvd_natAbs_of_coe_dvd_sq

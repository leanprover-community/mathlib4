/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
/-!
# Prime natural numbers and the factorial operator

-/

open Bool Subtype

open Nat

namespace Nat

theorem Prime.dvd_factorial : ∀ {n p : ℕ} (_ : Prime p), p ∣ n ! ↔ p ≤ n
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
    rw [factorial_succ, hp.dvd_mul, Prime.dvd_factorial hp]
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le, fun h =>
        (_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩

theorem coprime_factorial_iff {m n : ℕ} (hm : m ≠ 1) :
    m.Coprime n ! ↔ n < m.minFac := by
  rw [← not_le, iff_not_comm, Nat.Prime.not_coprime_iff_dvd]
  constructor
  · intro h
    exact ⟨m.minFac, minFac_prime hm, minFac_dvd m, Nat.dvd_factorial (minFac_pos m) h⟩
  · rintro ⟨p, hp, hdvd, hdvd'⟩
    exact le_trans (minFac_le_of_dvd hp.two_le hdvd) (hp.dvd_factorial.mp hdvd')

end Nat

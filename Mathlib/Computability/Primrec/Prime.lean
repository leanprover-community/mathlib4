/-
Copyright (c) 2026 Wei-Ting Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei-Ting Li
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Primality is primitive recursive

`Primrec.nat_prime : PrimrecPred Nat.Prime`.

The proof rewrites `Nat.Prime n` as `2 ≤ n ∧ ∀ m < n, ¬ (2 ≤ m ∧ n % m = 0)`
(`Nat.prime_def_lt'`) and closes with the bounded quantifier `PrimrecRel.forall_lt`.

`ComputablePred Nat.Prime` and `REPred Nat.Prime` follow by `Primrec.to_comp` and
`ComputablePred.to_re`; they are not stated here to keep this file inside the `Primrec` layer.
-/

public section

namespace Primrec

/-- Primality is a primitive recursive predicate on `ℕ`. -/
theorem nat_prime : PrimrecPred Nat.Prime := by
  have hR : PrimrecRel fun m n : ℕ => 2 ≤ m ∧ n % m = 0 := by
    unfold PrimrecRel
    exact (nat_le.comp (const 2) fst).and
      (Primrec.eq.comp (nat_mod.comp snd fst) (const 0))
  have h : PrimrecPred fun n : ℕ => 2 ≤ n ∧ ∀ m < n, ¬ (2 ≤ m ∧ n % m = 0) :=
    (nat_le.comp (const 2) Primrec.id).and
      ((PrimrecRel.forall_lt hR.not).comp Primrec.id Primrec.id)
  refine h.of_eq fun n => ?_
  rw [Nat.prime_def_lt']
  simp only [Nat.dvd_iff_mod_eq_zero, not_and]
  exact ⟨fun ⟨h2, hm⟩ => ⟨h2, fun m hm2 hmn => hm m hmn hm2⟩,
    fun ⟨h2, hm⟩ => ⟨h2, fun m hmn hm2 => hm m hm2 hmn⟩⟩

end Primrec

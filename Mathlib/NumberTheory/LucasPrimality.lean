/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Zify
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.IntegralDomain

/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/


/-- If `a^(p-1) = 1 mod p`, but `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`, then `p`
is prime. This is true because `a` has order `p-1` in the multiplicative group mod `p`, so this
group must itself have order `p-1`, which only happens when `p` is prime.
-/

theorem lucas_primality (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : p.Prime := by
  have h0 : p ≠ 0 := by
    rintro ⟨⟩
    exact hd 2 Nat.prime_two (dvd_zero _) (pow_zero _)
  have h1 : p ≠ 1 := by
    rintro ⟨⟩
    exact hd 2 Nat.prime_two (dvd_zero _) (pow_zero _)
  have hp1 : 1 < p := lt_of_le_of_ne h0.bot_lt h1.symm
  have order_of_a : orderOf a = p - 1 := by
    apply orderOf_eq_of_pow_and_pow_div_prime _ ha hd
    exact tsub_pos_of_lt hp1
  haveI : NeZero p := ⟨h0⟩
  rw [Nat.prime_iff_card_units]
  -- Prove cardinality of `Units` of `ZMod p` is both `≤ p-1` and `≥ p-1`
  refine le_antisymm (Nat.card_units_zmod_lt_sub_one hp1) ?_
  have hp' : p - 2 + 1 = p - 1 := tsub_add_eq_add_tsub hp1
  let a' : (ZMod p)ˣ := Units.mkOfMulEqOne a (a ^ (p - 2)) (by rw [← pow_succ', hp', ha])
  calc
    p - 1 = orderOf a := order_of_a.symm
    _ = orderOf a' := (orderOf_injective (Units.coeHom (ZMod p)) Units.ext a')
    _ ≤ Fintype.card (ZMod p)ˣ := orderOf_le_card_univ


/-- If `p` is prime, then there exists an `a`
such that `a^(p-1) = 1 mod p` and `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`,
The multiplicative group mod `p` is cyclic, so `a` can be any generator of the group
(which must have order `p-1`)
-/
theorem reverse_lucas_primality (p : ℕ) (hP : p.Prime):
    ∃ a : ZMod p, a ^ (p - 1) = 1 ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1 := by

  have _: Fact p.Prime := ⟨hP⟩
  have _: 1 < p := by exact Nat.Prime.one_lt hP

  have h0: IsCyclic ((ZMod p)ˣ) := by exact instIsCyclicUnitsOfFinite
  obtain ⟨g, hg⟩ := h0.exists_generator

  have h1: orderOf g = p - 1 := by
    rw [orderOf_generator_eq_natCard, Nat.card_eq_fintype_card, ← Nat.prime_iff_card_units]
    trivial
    trivial

  -- Our generator 'g' works as the witness 'a'
  use g
  rw [
    ← (orderOf_injective (Units.coeHom (ZMod p)) Units.ext _),
    Units.coeHom_apply,
    orderOf_eq_iff
  ] at h1

  constructor

  exact h1.1

  -- Show that 'g^((p-1)/q) ≠ 1', using the fact that '(p-1)/q)' < 'orderOf g'
  intro q hq hq_div
  have _: q ≤ p - 1 := by
    apply Nat.le_of_dvd at hq_div
    exact hq_div
    simp only [tsub_pos_iff_lt]
    trivial
  have q_gt_1: 1 < q := by
    apply Nat.Prime.one_lt
    exact hq
  have p_div_lt: (p - 1) / q < p - 1 := by
    apply Nat.div_lt_self
    simp only [tsub_pos_iff_lt]
    linarith
    exact q_gt_1
  have neq_one: g.val ^ ((p - 1) / q) ≠ 1 := by
    apply h1.2
    exact p_div_lt
    apply Nat.div_pos
    linarith
    linarith

  exact neq_one
  simp
  linarith


/-- A number `p` is prime if and only if there exists an `a` such that
`a^(p-1) = 1 mod p` and `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`
-/
theorem lucas_primality_iff (p : ℕ): p.Prime ↔
    ∃ a : ZMod p, a ^ (p - 1) = 1 ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1 := by
  apply Iff.intro
    (fun hp => reverse_lucas_primality p hp)
    (fun g => by
      obtain ⟨a, ⟨ha, hb⟩⟩ := g
      apply lucas_primality p a ha hb
    )

/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Qq
public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.NumberTheory.LucasPrimality

/-!
# Lucas primality certificates

Proves `Nat.Prime p` by the Lucas test from a primitive root and the prime factors of `p - 1`.
-/

public section

namespace Mathlib.Tactic.Primality

/-- A more kernel-efficient version of `b ^ e % m`, computed four bits of `e` at a time by
`Nat.pow`. Replace with `Nat.powMod` once
[lean4#15167](https://github.com/leanprover/lean4/pull/15167) is available. -/
@[expose] def powMod (b e m : ℕ) : ℕ :=
  if e = 0 then 1 % m else Nat.pow (powMod b (e / 16) m) 16 * Nat.pow b (e % 16) % m

theorem powMod_def (b e m : ℕ) : powMod b e m = b ^ e % m := by
  fun_induction powMod b e m with
  | case1 => simp
  | case2 e _ ih =>
    simp [ih, ← ZMod.natCast_eq_natCast_iff', ← pow_mul, ← pow_add, Nat.div_add_mod']

/-- Compiled code runs core's `Nat.powMod` in place of `powMod` since it is faster there. -/
@[csimp] theorem powMod_eq_natPowMod : @powMod = @Nat.powMod := by
  funext b e m
  rw [powMod_def, Nat.powMod_def]

/-- `lucasCheck p a factorization` checks that `a ^ (p - 1) % p = 1` (via the powMod check for
`q = 2`), that `a ^ ((p - 1) / q) % p ≠ 1` for each `(q, e) ∈ factorization`, and that the
`q ^ e` multiply to `p - 1`. -/
@[expose] def lucasCheck (p a : ℕ) (factorization : List (ℕ × ℕ)) : Bool :=
  p % 2 == 1 && powMod a ((p - 1) / 2) p == p - 1 &&
    factorization.all (fun f ↦ f.1 == 2 || powMod a ((p - 1) / f.1) p != 1) &&
    (factorization.map fun f ↦ f.1 ^ f.2).prod == p - 1

theorem prime_of_lucasCheck {p a : ℕ} {factorization : List (ℕ × ℕ)}
    (hprime : ∀ f ∈ factorization, f.1.Prime) (h : lucasCheck p a factorization = true) :
    p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne] at h
  obtain ⟨⟨⟨hodd, hpow2⟩, hpow⟩, hprod⟩ := h
  have hp : 2 < p := by grind [List.prod_eq_zero_iff, pow_eq_zero_iff', Nat.Prime.ne_zero]
  have hneg : (a : ZMod p) ^ ((p - 1) / 2) = -1 := by
    rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← powMod_def, hpow2, Nat.cast_pred (by lia),
      ZMod.natCast_self, zero_sub]
  refine lucas_primality p a ?_ fun q hq hqp h1 ↦ ?_
  · rw [← Nat.mul_div_cancel' (by lia : 2 ∣ p - 1), pow_mul', hneg, neg_one_sq]
  · obtain ⟨_, hx, hqf⟩ := hq.prime.dvd_prod_iff.mp (hprod ▸ hqp)
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hprime f hf)).mp (hq.dvd_of_dvd_pow hqf)
    rcases hpow f hf with h2 | hne
    · exact absurd (ZMod.neg_one_eq_one_iff.mp (by rwa [h2, hneg] at h1)) (by lia)
    · apply hne
      rw [powMod_def, ← ZMod.val_natCast, Nat.cast_pow, h1, ZMod.val_one'' (by lia)]

/-- A candidate witness of a Lucas certificate for a `p`, which is not recorded in the type. -/
structure LucasWitness where
  /-- A primitive root of `p`. -/
  root : ℕ
  /-- The prime factors of `p - 1`. -/
  primeFactors : List ℕ

/-- The factorization of `p - 1` into the prime factors of `w`, if each of them divides `p - 1`
and `lucasCheck` passes with the root of `w`. -/
def LucasWitness.factorization? (w : LucasWitness) (p : ℕ) : Option (List (ℕ × ℕ)) := do
  let factorization := w.primeFactors.map fun q ↦ (q, (Nat.maxPowDvdDiv q (p - 1)).1)
  guard (factorization.all (·.2 != 0) && lucasCheck p w.root factorization)
  return factorization

end Mathlib.Tactic.Primality

end

public meta section

open Lean Qq

namespace Mathlib.Tactic.Primality

/-- Proves `Nat.Prime p` from the primitive root `root` and the factorization of `p - 1` in
`factorization`, each prime factor with its exponent and proof of primality. -/
def certifyLucas (p root : ℕ) (factorization : List ((q : ℕ) × ℕ × Q(Nat.Prime $q))) :
    Q(Nat.Prime $p) :=
  let ⟨factorizationQ, hprime⟩ := go factorization
  have hcheck : Q(lucasCheck $p $root $factorizationQ = true) := reflBoolTrue
  q(prime_of_lucasCheck $hprime $hcheck)
where
  /-- The list literal of `factorization`, with the primality of its prime factors. -/
  go (factorization : List ((q : ℕ) × ℕ × Q(Nat.Prime $q))) :
      (factorizationQ : Q(List (ℕ × ℕ))) × Q(∀ f ∈ $factorizationQ, f.1.Prime) :=
    match factorization with
    | [] => ⟨q([]), q(List.forall_mem_nil _)⟩
    | ⟨q, e, hq⟩ :: rest =>
      let ⟨factorizationQ, hprime⟩ := go rest
      ⟨q(($q, $e) :: $factorizationQ), q(List.forall_mem_cons.2 ⟨$hq, $hprime⟩)⟩

end Mathlib.Tactic.Primality

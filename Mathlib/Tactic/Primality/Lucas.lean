/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public meta import Mathlib.Util.Qq
public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.NumberTheory.LucasPrimality

/-!
# Lucas primality certificates

Proves `Nat.Prime p` by the Lucas test from a primitive root and certified prime factors of `p - 1`.
-/

public section

namespace Mathlib.Tactic.Primality

/-- `b ^ e % m`, computed four bits of `e` at a time by `Nat.pow`, which the kernel evaluates
natively (`^` unfolds `Monoid.npow`'s instances first). Replace it with `Nat.powMod` once the kernel
evaluates `Nat.powMod` efficiently. -/
@[expose] def powMod (b e m : ℕ) : ℕ :=
  if e = 0 then 1 % m else Nat.pow (powMod b (e / 16) m) 16 * Nat.pow b (e % 16) % m

theorem powMod_def (b e m : ℕ) : powMod b e m = b ^ e % m := by
  fun_induction powMod b e m with
  | case1 => simp
  | case2 e _ ih =>
    simp [ih, ← ZMod.natCast_eq_natCast_iff', ← pow_mul, ← pow_add, Nat.div_add_mod']

/-- `lucasCheck p a fs` checks that `a ^ (p - 1) % p = 1`, that `a ^ ((p - 1) / q) % p ≠ 1` for
each `(q, e) ∈ fs`, and that the `q ^ e` multiply to `p - 1`. -/
@[expose] def lucasCheck (p a : ℕ) (fs : List (Nat.Primes × ℕ)) : Bool :=
  powMod a (p - 1) p == 1 && fs.all (fun f ↦ powMod a ((p - 1) / f.1) p != 1) &&
    (fs.map fun f ↦ (f.1 : ℕ) ^ f.2).prod == p - 1

theorem prime_of_lucasCheck {p a : ℕ} {fs : List (Nat.Primes × ℕ)}
    (h : lucasCheck p a fs = true) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne] at h
  obtain ⟨⟨ha, hpow⟩, hprod⟩ := h
  have hp : p ≠ 1 := by grind [powMod_def]
  refine lucas_primality p a ?_ fun q hq hqp h1 ↦ ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← powMod_def, ha, Nat.cast_one]
  · obtain ⟨_, hx, hqf⟩ := hq.prime.dvd_prod_iff.mp (hprod ▸ hqp)
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq f.1.prop).mp (hq.dvd_of_dvd_pow hqf)
    apply hpow f hf
    rw [powMod_def, ← ZMod.val_natCast, Nat.cast_pow, h1, ZMod.val_one'' hp]

end Mathlib.Tactic.Primality

end

public meta section

open Lean Qq

namespace Mathlib.Tactic.Primality

/-- A candidate witness of a Lucas certificate for `p`. -/
structure LucasWitness where
  /-- A primitive root of `p`. -/
  root : Nat
  /-- The prime factors of `p - 1`. -/
  primeFactors : List Nat

/-- Proves `Nat.Prime p` from the primitive root `root` and the prime factors of `p - 1` in
`factors`, each with its proof of primality. -/
def certifyLucas (p root : Nat) (factors : List ((q : Nat) × Q(Nat.Prime $q))) :
    Q(Nat.Prime $p) :=
  let factorization : Q(List (Nat.Primes × Nat)) := mkListLitQ <| factors.map fun ⟨q, hq⟩ ↦
    q((⟨$q, $hq⟩, $(mkNatLitQ (Nat.maxPowDvdDiv q (p - 1)).1)))
  -- The kernel evaluates `Nat` arithmetic on terms with free variables (such as a hypothesis
  -- proving one of the factors prime) only inside `eagerReduce`.
  have hcheck : Q(lucasCheck $p $root $factorization = true) := eagerReflBoolTrue
  q(prime_of_lucasCheck $hcheck)

end Mathlib.Tactic.Primality

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

Proves `Nat.Prime p` by the Lucas test from a primitive root and prime factors of `p - 1`.
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

/-- `lucasRootCheck p a primeFactors` checks that `a ^ (p - 1) % p = 1` and that
`a ^ ((p - 1) / q) % p ≠ 1` for each `q ∈ primeFactors`. -/
@[expose] def lucasRootCheck (p a : ℕ) (primeFactors : List ℕ) : Bool :=
  powMod a (p - 1) p == 1 && primeFactors.all fun q ↦ powMod a ((p - 1) / q) p != 1

/-- `lucasCheck p a factorization` checks that `a ^ (p - 1) % p = 1`, that
`a ^ ((p - 1) / q) % p ≠ 1` for each `(q, e) ∈ factorization`, and that the `q ^ e` multiply to
`p - 1`. -/
@[expose] def lucasCheck (p a : ℕ) (factorization : List (ℕ × ℕ)) : Bool :=
  lucasRootCheck p a (factorization.map fun f ↦ f.1) &&
    (factorization.map fun f ↦ f.1 ^ f.2).prod == p - 1

theorem prime_of_lucasCheck {p a : ℕ} {factorization : List (ℕ × ℕ)}
    (hprime : ∀ f ∈ factorization, f.1.Prime) (h : lucasCheck p a factorization = true) :
    p.Prime := by
  simp only [lucasCheck, lucasRootCheck, List.all_map, Function.comp_def, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true, bne_iff_ne] at h
  obtain ⟨⟨ha, hpow⟩, hprod⟩ := h
  have hp : p ≠ 1 := by grind [powMod_def]
  refine lucas_primality p a ?_ fun q hq hqp h1 ↦ ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← powMod_def, ha, Nat.cast_one]
  · obtain ⟨_, hx, hqf⟩ := hq.prime.dvd_prod_iff.mp (hprod ▸ hqp)
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hprime f hf)).mp (hq.dvd_of_dvd_pow hqf)
    apply hpow f hf
    rw [powMod_def, ← ZMod.val_natCast, Nat.cast_pow, h1, ZMod.val_one'' hp]

/-- A candidate witness of a Lucas certificate for a `p`, which is not recorded in the type. -/
structure LucasWitness where
  /-- A primitive root of `p`. -/
  root : Nat
  /-- The prime factors of `p - 1`. -/
  primeFactors : List Nat

/-- Whether `w` is a witness for the prime `p`. Its prime factors, divided out of `p - 1` in turn,
must each divide what is left and leave `1`, and its root must pass `lucasRootCheck`. -/
def LucasWitness.certifies (w : LucasWitness) (p : Nat) : Bool :=
  w.primeFactors.foldlM (init := p - 1)
      (fun rest q ↦ if rest % q == 0 then some (rest.divMaxPow q) else none) == some 1 &&
    lucasRootCheck p w.root w.primeFactors

end Mathlib.Tactic.Primality

end

public meta section

open Lean Qq

namespace Mathlib.Tactic.Primality

/-- Proves `Nat.Prime p` from the primitive root `root` and the prime factors of `p - 1` in
`primeFactors`, each with its proof of primality. -/
def certifyLucas (p root : Nat) (primeFactors : List ((q : Nat) × Q(Nat.Prime $q))) :
    Q(Nat.Prime $p) :=
  let ⟨factorization, hprime⟩ := go primeFactors
  have hcheck : Q(lucasCheck $p $root $factorization = true) := reflBoolTrue
  q(prime_of_lucasCheck $hprime $hcheck)
where
  /-- The factorization of `p - 1` with the factors in `primeFactors`, and their primality. -/
  go : List ((q : Nat) × Q(Nat.Prime $q)) →
      (factorization : Q(List (Nat × Nat))) × Q(∀ f ∈ $factorization, f.1.Prime)
    | [] => ⟨q([]), q(List.forall_mem_nil _)⟩
    | ⟨q, hq⟩ :: rest =>
      let ⟨factorization, hprime⟩ := go rest
      have e : Q(Nat) := mkNatLitQ (Nat.maxPowDvdDiv q (p - 1)).1
      ⟨q(($q, $e) :: $factorization), q(List.forall_mem_cons.2 ⟨$hq, $hprime⟩)⟩

end Mathlib.Tactic.Primality

/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Computability.Primrec
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.GCD.Prime
public import Mathlib.NumberTheory.Divisors

/-!
# Particular functions are primitive recursive

While `Primrec/Basic.lean` gives the basic machinery for proving functions primitive recursive,
this file gives particular results for certain functions.
-/

/-- The square root function is primitve recursive. -/
theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt

/-- The factorial function is primitve recursive. -/
theorem Primrec.factorial : Primrec Nat.factorial := by
  convert list_foldl (σ := ℕ) (h := fun n ⟨p, k⟩ ↦ p * (k + 1)) list_range (const 1) ?_
  · rw [← Finset.prod_range_add_one_eq_factorial, ← List.foldl_map, ← List.prod_eq_foldl]
    rw [← List.prod_toFinset _ List.nodup_range, ← List.toFinset_range]
  · refine comp₂ ?_ .right
    exact nat_mul.comp₂ .left (succ.comp₂ .right)

proof_wanted Primrec₂.descFactorial : Primrec₂ Nat.descFactorial

proof_wanted Primrec₂.stirlingFirst : Primrec₂ Nat.stirlingFirst

proof_wanted Primrec₂.stirlingSecond : Primrec₂ Nat.stirlingSecond

proof_wanted Primrec.coprime : Primrec₂ (decide <| Nat.Coprime · ·)

proof_wanted Primrec₂.gcd : Primrec₂ Nat.gcd

proof_wanted Primrec₂.lcm : Primrec₂ Nat.lcm

proof_wanted Primrec.prime : Primrec (decide <| Nat.Prime ·)

proof_wanted Primrec.divisors : Primrec Nat.divisors

proof_wanted Primrec.properDivisors : Primrec Nat.properDivisors

-- proof_wanted Primrec.perfect : Primrec (decide <| Nat.Perfect ·)

proof_wanted Primrec₂.log : Primrec₂ Nat.log

proof_wanted Primrec.log2 : Primrec Nat.log2

proof_wanted Primrec₂.clog : Primrec₂ Nat.clog

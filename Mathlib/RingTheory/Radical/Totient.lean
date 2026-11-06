/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Radical.NatInt

/-!
# The radical and Euler's totient

This file relates the radical of a natural number to Euler's totient function.

## Declarations

- `Nat.totient_eq_div_radical_mul_totient_radical`: Euler's totient of a natural number splits
  into its squarefree and nonsquarefree parts.
-/

@[expose] public section

open UniqueFactorizationMonoid

namespace Nat

variable {n : ℕ}

/-- Euler's totient of a natural number splits into its squarefree and nonsquarefree parts. -/
lemma totient_eq_div_radical_mul_totient_radical :
    n.totient = (n / radical n) * (radical n).totient := by
  have hpf : (radical n).primeFactors = n.primeFactors := by
    have := UniqueFactorizationMonoid.primeFactors_radical (a := n)
    rwa [UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors] at this
  rw [totient_eq_div_primeFactors_mul n, totient_eq_div_primeFactors_mul (radical n), hpf,
    ← radical_eq_prod_primeFactors, Nat.div_self (Nat.pos_of_ne_zero radical_ne_zero), one_mul]

end Nat

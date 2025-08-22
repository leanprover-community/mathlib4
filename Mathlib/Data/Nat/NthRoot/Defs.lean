/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

/-!
# Definition of `Nat.nthRoot`

In this file we define `Nat.nthRoot n a` to be the floor of the `n`th root of `a`.
The function is defined in terms of natural numbers with no dependencies outside of prelude.
-/

/-- `Nat.nthRoot n a = ⌊(a : ℝ) ^ (1 / n : ℝ)⌋₊` defined in terms of natural numbers.

We use Lagrange's method to find a root of $x^n = a$,
so it converges superexponentially fast. -/
def Nat.nthRoot : Nat → Nat → Nat
  | 0, _ => 1
  | 1, a => a
  | n + 2, a =>
    if a ≤ 1 then a else go n a a
    where
      /-- Auxiliary definition for `Nat.nthRoot`. -/
      go n a guess :=
        let next := (a / guess^(n + 1) + (n + 1) * guess) / (n + 2)
        if next < guess then go n a next else guess

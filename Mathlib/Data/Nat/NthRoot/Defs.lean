/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Init

/-!
# Definition of `Nat.nthRoot`

In this file we define `Nat.nthRoot n a` to be the floor of the `n`th root of `a`.
The function is defined in terms of natural numbers with no dependencies outside of prelude.
-/

/-- `Nat.nthRoot n a = ⌊(a : ℝ) ^ (1 / n : ℝ)⌋₊` defined in terms of natural numbers.

We use Newton's method to find a root of $x^n = a$,
so it converges superexponentially fast. -/
def Nat.nthRoot : Nat → Nat → Nat
  | 0, _ => 1
  | 1, a => a
  | n + 2, a =>
    go n a a a
    where
      /-- Auxiliary definition for `Nat.nthRoot`.

      Given natural numbers `n`, `a`, `fuel`, `guess`
      such that `⌊(a : ℝ) ^ (1 / (n + 2) : ℝ)⌋₊ ≤ guess ≤ fuel`,
      returns `⌊(a : ℝ) ^ (1 / (n + 2) : ℝ)⌋₊`.

      The auxiliary number `guess` is the current approximation in Newton's method,
      tracked in the arguments so that the definition uses a tail recursion
      which is unfolded into a loop by the compiler.

      The auxiliary number `fuel` is an upper estimate on the number of steps in Newton's method.
      Any number `fuel ≥ guess` is guaranteed to work, but smaller numbers may work as well.
      If `fuel` is too small, then `Nat.nthRoot.go` returns the result of the `fuel`th step
      of Newton's method.
      -/
      go (n a : Nat)
      | 0, guess => guess
      | fuel + 1, guess =>
        let next := (a / guess ^ (n + 1) + (n + 1) * guess) / (n + 2)
        if next < guess then go n a fuel next else guess

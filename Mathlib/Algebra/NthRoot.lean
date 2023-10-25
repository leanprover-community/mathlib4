/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
import Mathlib.Util.Superscript
import Mathlib.Tactic.Basic
/-!
# Notation for the `n`-th root

This file defines a typeclass and notation for `n`-th root of a number.
An instance of `NthRoot R n` defines the `n`-th root operation `NthRoot.nthRoot : R → R`,
available using notation `ⁿ√`.

Notation uses the superscript parser, so `ⁿ√x` is `nthRoot n x` and `⁴²√x` is `nthRoot 42 x`.
Without a superscript argument, notation mean square root.
We also allow `∛` and `∜` for the cubic root and the fourth root.
-/

/-- Notation typeclass for the "`n`-th root" operation. -/
class NthRoot (R : Type*) (n : Nat) where
  /-- `n`-th root of a number. -/
  nthRoot : R → R

syntax:arg "√" term:max : term
syntax:arg "∛" term:max : term
syntax:arg "∜" term:max : term
syntax:arg superscript(term) "√" term:max : term
macro_rules | `(√ $r:term) => `(NthRoot.nthRoot 2 $r)
macro_rules | `(∛ $r:term) => `(NthRoot.nthRoot 3 $r)
macro_rules | `(∜ $r:term) => `(NthRoot.nthRoot 4 $r)
macro_rules | `($n:superscript √ $r:term) => `(NthRoot.nthRoot $n $r)

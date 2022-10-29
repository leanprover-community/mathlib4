/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.ZifyAttr

namespace Mathlib.Tactic

open Lean
open Lean.Parser.Tactic

/--
The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.
```lean4
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : false := by
  zify [hab] at h
  /- h : ↑a - ↑b < ↑c -/
```
`zify` makes use of the `@[zify_simps]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℤ`-valued expressions.
`zify` is in some sense dual to the `lift` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
syntax (name := zify) "zify" (simpArgs)? (ppSpace location)? : tactic

macro_rules
| `(tactic| zify $[at $location]?) =>
  `(tactic| simp only [zify_simps, push_cast] $[at $location]?)
| `(tactic| zify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [zify_simps, push_cast, $args,*] $[at $location]?)

@[zify_simps] lemma zify.intOfNat_eq (a b : ℕ) : a = b ↔ (a : ℤ) = (b : ℤ) := Int.ofNat_inj.symm
@[zify_simps] lemma zify.intOfNat_le (a b : ℕ) : a ≤ b ↔ (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.symm
@[zify_simps] lemma zify.intOfNat_lt (a b : ℕ) : a < b ↔ (a : ℤ) < (b : ℤ) := Int.ofNat_lt.symm
@[zify_simps] lemma zify.intOfNat_ne (a b : ℕ) : a ≠ b ↔ (a : ℤ) ≠ (b : ℤ) := by simp

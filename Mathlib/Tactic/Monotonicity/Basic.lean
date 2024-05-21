/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Lean.Elab.Tactic.SolveByElim
import Mathlib.Tactic.Monotonicity.Attr

/-! # Monotonicity tactic

The tactic `mono` applies monotonicity rules (collected through the library by being tagged
`@[mono]`).

The version of the tactic here is a cheap partial port of the `mono` tactic from Lean 3, which had
many more options and features.  It is implemented as a wrapper on top of `solve_by_elim`.

Temporary syntax change: Lean 3 `mono` applied a single monotonicity rule, then applied local
hypotheses and the `rfl` tactic as many times as it could.  This is hard to implement on top of
`solve_by_elim` because the counting system used in the `maxDepth` field of its configuration would
count these as separate steps, throwing off the count in the desired configuration
`maxDepth := 1`.  So instead we just implement a version of `mono` in which monotonicity rules,
local hypotheses and `rfl` are all applied repeatedly until nothing more is applicable.  The syntax
for this in Lean 3 was `mono*`. Both `mono` and `mono*` implement this behavior for now.
-/

open Lean Elab Tactic Parser Tactic
open Tactic SolveByElim

namespace Mathlib.Tactic.Monotonicity

/--
`mono` applies monotonicity rules and local hypotheses repetitively.  For example,
```lean
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  mono
```
-/
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

elab_rules : tactic
| `(tactic| mono $[*]? $[$h:mono.side]? $[ with%$w $a:term,*]? $[ using%$u $s,*]? ) => do
  let msg (s : String) := s ++ " syntax is not yet supported in 'mono'"
  if let some h := h then throwErrorAt h (msg "'left'/'right'/'both'")
  if let some w := w then throwErrorAt w (msg "'with'")
  if let some u := u then throwErrorAt u (msg "'using'")
  let cfg ← elabApplyRulesConfig <| mkNullNode #[]
  let cfg := { cfg with
    backtracking := false
    transparency := .reducible
    exfalso := false }
  liftMetaTactic fun g => do processSyntax cfg false false [] [] #[mkIdent `mono] [g]

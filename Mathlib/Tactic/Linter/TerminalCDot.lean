/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Michael Rothgang
-/
module

public import Mathlib.Tactic.TacticAnalysis

/-!
# Terminal cdot linter

This linter flags uses of the focus dot (`·`) where there is only one goal,
and where the preceding tactic is not wrapped in a focus dot.
A sequence of tactics each starting with `·` is allowed because it looks nice.

Usually, the `·` can simply be removed

## Implementation notes

This linter has to look at the preceding tactic, so it is hard to integrate
into the unused tactic linter. Instead, we implement it using the `tacticAnalysis` framework,
because that already computes the tactic sequences for us.
-/

public meta section

open Lean Mathlib

/--
The `terminalCDot` linter flags redundant uses of the `·` focus dot, such as in
```
example : True := by
  · trivial
```

This does not flag terminal focus dots that follow other focus dots, such as in
```
example (n : Nat) : True := by
  by_cases hn : n > 2
  · trivial
  · trivial
```
-/
register_option linter.style.terminalCDot : Bool := {
  defValue := true
  descr := "enable the `terminalCDot` linter"
}

@[tacticAnalysis linter.style.terminalCDot, inherit_doc linter.style.terminalCDot]
def terminalCDotLinter : TacticAnalysis.Config where run seq := do
  let some last := seq.back? | return
  unless last.tacI.stx.isOfKind ``cdot && last.tacI.goalsBefore matches [_] do return
  if h : 2 ≤ seq.size then
    if seq[seq.size - 2].tacI.stx.isOfKind ``cdot then
      return
  logWarningAt last.tacI.stx[0]
    m!"Unnecessary focusing dot `·`: you should be able to remove it, \
    or move it earlier up in the proof, as necessary."

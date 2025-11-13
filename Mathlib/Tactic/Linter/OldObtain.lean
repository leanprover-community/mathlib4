/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# The `oldObtain` linter, against stream-of-consciousness `obtain`

The `oldObtain` linter flags any occurrences of "stream-of-consciousness" `obtain`,
i.e. uses of the `obtain` tactic which do not immediately provide a proof.

## Example

There are six different kinds of `obtain` uses. In one example, they look like this.
```
theorem foo : True := by
  -- These cases are fine.
  obtain := trivial
  obtain h := trivial
  obtain : True := trivial
  obtain h : True := trivial
  -- These are linted against.
  obtain : True
  · trivial
  obtain h : True
  · trivial
```
We allow the first four (since an explicit proof is provided), but lint against the last two.

## Why is this bad?

This is similar to removing all uses of `Tactic.Replace` and `Tactic.Have`
from mathlib: in summary,
- this version is a Lean3-ism, which can be unlearned now
- the syntax `obtain foo : type := proof` is slightly shorter;
  particularly so when the first tactic of the proof is `exact`
- when using the old syntax as `obtain foo : type; · proof`, there is an intermediate state with
multiple goals right before the focusing dot. This can be confusing.
(This gets amplified with the in-flight "multiple goal linter", which seems generally desired ---
for many reasons, including teachability. Granted, the linter could be tweaked to not lint in this
case... but by now, the "old" syntax is not clearly better.)
- the old syntax *could* be slightly nicer when deferring goals: however, this is rare.
In the 30 replacements of the last PR, this occurred twice. In both cases, the `suffices` tactic
could also be used, as was in fact clearer. -/

open Lean Elab Linter

namespace Mathlib.Linter.Style

/-- Whether a syntax element is an `obtain` tactic call without a provided proof. -/
def isObtainWithoutProof : Syntax → Bool
  -- Using the `obtain` tactic without a proof requires proving a type;
  -- a pattern is optional.
  | `(tactic|obtain : $_type) | `(tactic|obtain $_pat : $_type) => true
  | _ => false

/-- The `oldObtain` linter emits a warning upon uses of the "stream-of-consciousness" variants
of the `obtain` tactic, i.e. with the proof postponed. -/
register_option linter.oldObtain : Bool := {
  defValue := false
  descr := "enable the `oldObtain` linter"
}

/-- The `oldObtain` linter: see docstring above -/
def oldObtainLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterValue linter.oldObtain (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some head := stx.find? isObtainWithoutProof then
      Linter.logLint linter.oldObtain head m!"Please remove stream-of-consciousness `obtain` syntax"

initialize addLinter oldObtainLinter

end Mathlib.Linter.Style

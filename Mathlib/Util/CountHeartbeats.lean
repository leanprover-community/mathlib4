/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Util.Heartbeats
import Lean.Meta.Tactic.TryThis

/-!
Defines a command wrapper that prints the number of heartbeats used in the enclosed command.

For example
```
#count_heartbeats in
theorem foo : 42 = 6 * 7 := rfl
```
will produce an info message containing a number around 51.
If this number is above the current `maxHeartbeats`, we also print a `Try this:` suggestion.
-/


open Lean Elab Command Meta Linter

namespace Mathlib.CountHeartbeats

-- This file mentions bare `set_option maxHeartbeats` by design: do not warn about this.
set_option linter.style.setOption false

open Tactic

/--
Run a tactic, optionally restoring the original state, and report just the number of heartbeats.
-/
def runTacForHeartbeats (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (revert : Bool := true) :
    TacticM Nat := do
  let start ← IO.getNumHeartbeats
  let s ← saveState
  evalTactic tac
  if revert then restoreState s
  return (← IO.getNumHeartbeats) - start

/--
Given a `List Nat`, return the minimum, maximum, and standard deviation.
-/
def variation (counts : List Nat) : List Nat :=
  let min := counts.min?.getD 0
  let max := counts.max?.getD 0
  let toFloat (n : Nat) := n.toUInt64.toFloat
  let toNat (f : Float) := f.toUInt64.toNat
  let counts' := counts.map toFloat
  let μ : Float := counts'.foldl (· + ·) 0 / toFloat counts.length
  let stddev : Float := Float.sqrt <|
    ((counts'.map fun i => (i - μ)^2).foldl (· + ·) 0) / toFloat counts.length
  [min, max, toNat stddev]

/--
Given a `List Nat`, log an info message with the minimum, maximum, and standard deviation.
-/
def logVariation {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (counts : List Nat) : m Unit := do
  if let [min, max, stddev] := variation counts then
  -- convert `[min, max, stddev]` to user-facing heartbeats
  logInfo s!"Min: {min / 1000} Max: {max / 1000} StdDev: {stddev / 10}%"

/-- Count the heartbeats used by a tactic, e.g.: `#count_heartbeats simp`. -/
elab "#count_heartbeats " tac:tacticSeq : tactic => do
  logInfo s!"{← runTacForHeartbeats tac (revert := false)}"

/--
`#count_heartbeats! in tac` runs a tactic 10 times, counting the heartbeats used, and logs the range
and standard deviation. The tactic `#count_heartbeats! n in tac` runs it `n` times instead.
-/
elab "#count_heartbeats! " n:(num)? "in" ppLine tac:tacticSeq : tactic => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  -- First run the tactic `n-1` times, reverting the state.
  let counts ← (List.range (n - 1)).mapM fun _ => runTacForHeartbeats tac
  -- Then run once more, keeping the state.
  let counts := (← runTacForHeartbeats tac (revert := false)) :: counts
  logVariation counts

/--
Round down the number `n` to the nearest thousand, if `approx` is `true`.
-/
def roundDownIf (n : Nat) (approx : Bool) : String :=
  if approx then s!"approximately {(n / 1000) * 1000}" else s!"{n}"

set_option linter.style.maxHeartbeats false in
/--
`#count_heartbeats in cmd` counts the heartbeats used in the enclosed command `cmd`.
Use `#count_heartbeats` to count the heartbeats in *all* the following declarations.

This is most useful for setting sufficient but reasonable limits via `set_option maxHeartbeats`
for long running declarations.

If you do so, please resist the temptation to set the limit as low as possible.
As the `simp` set and other features of the library evolve,
other contributors will find that their (likely unrelated) changes
have pushed the declaration over the limit.
`count_heartbearts in` will automatically suggest a `set_option maxHeartbeats` via "Try this:"
using the least number of the form `2^k * 200000` that suffices.

Note that that internal heartbeat counter accessible via `IO.getNumHeartbeats`
has granularity 1000 times finer that the limits set by `set_option maxHeartbeats`.
As this is intended as a user command, we divide by 1000.

The optional `approximately` keyword rounds down the heartbeats to the nearest thousand.
This helps make the tests more stable to small changes in heartbeats.
To use this functionality, use `#count_heartbeats approximately in cmd`.
-/
elab "#count_heartbeats " approx:(&"approximately ")? "in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    let roundElapsed := roundDownIf elapsed approx.isSome
    let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
    if elapsed < max then
      logInfo
        m!"Used {roundElapsed} heartbeats, which is less than the current maximum of {max}."
    else
      let mut max' := max
      while max' < elapsed do
        max' := 2 * max'
      logInfo
        m!"Used {roundElapsed} heartbeats, which is greater than the current maximum of {max}."
      let m : TSyntax `num := quote max'
      Command.liftCoreM <| MetaM.run' do
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef)
          (← set_option hygiene false in `(command| set_option maxHeartbeats $m in $cmd))

/-- `count_heartbeats` is deprecated in favour of `#count_heartbeats` since "2025-01-12" -/
elab "count_heartbeats" : tactic =>
  logWarning "`count_heartbeats` has been renamed to `#count_heartbeats`"

/-- `count_heartbeats` is deprecated in favour of `#count_heartbeats` since "2025-01-12" -/
elab "count_heartbeats" : command =>
  logWarning "`count_heartbeats` has been renamed to `#count_heartbeats`"

set_option linter.style.maxHeartbeats false in
/--
Guard the minimal number of heartbeats used in the enclosed command.

This is most useful in the context of debugging and minimizing an example of a slow declaration.
By guarding the number of heartbeats used in the slow declaration,
an error message will be generated if a minimization step makes the slow behaviour go away.

The default number of minimal heartbeats is the value of `maxHeartbeats` (typically 200000).
Alternatively, you can specify a number of heartbeats to guard against,
using the syntax `guard_min_heartbeats n in cmd`.

The optional `approximately` keyword rounds down the heartbeats to the nearest thousand.
This helps make the tests more stable to small changes in heartbeats.
To use this functionality, use `guard_min_heartbeats approximately (n)? in cmd`.
-/
elab "guard_min_heartbeats " approx:(&"approximately ")? n:(num)? "in" ppLine cmd:command :
    command => do
  let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
  let n := match n with
           | some j => j.getNat
           | none => max
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    if elapsed < n then
      logInfo m!"Used {roundDownIf elapsed approx.isSome} heartbeats, \
                which is less than the minimum of {n}."

set_option linter.style.maxHeartbeats false in
/--
Run a command, optionally restoring the original state, and report just the number of heartbeats.
-/
def elabForHeartbeats (cmd : TSyntax `command) (revert : Bool := true) : CommandElabM Nat := do
  let start ← IO.getNumHeartbeats
  let s ← get
  elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  if revert then set s
  return (← IO.getNumHeartbeats) - start

/--
`#count_heartbeats! in cmd` runs a command `10` times, reporting the range in heartbeats, and the
standard deviation. The command `#count_heartbeats! n in cmd` runs it `n` times instead.

Example usage:
```
#count_heartbeats! in
def f := 37
```
displays the info message `Min: 7 Max: 8 StdDev: 14%`.
-/
elab "#count_heartbeats! " n:(num)? "in" ppLine cmd:command : command => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  -- First run the command `n-1` times, reverting the state.
  let counts ← (List.range (n - 1)).mapM fun _ => elabForHeartbeats cmd
  -- Then run once more, keeping the state.
  let counts := (← elabForHeartbeats cmd (revert := false)) :: counts
  logVariation counts

end CountHeartbeats

end Mathlib

/-!
#  The "countHeartbeats" linter

The "countHeartbeats" linter counts the heartbeats of every declaration.
-/

namespace Mathlib.Linter

/--
The "countHeartbeats" linter counts the heartbeats of every declaration.

The effect of the linter is similar to `#count_heartbeats in xxx`, except that it applies
to all declarations.

Note that the linter only counts heartbeats in "top-level" declarations:
it looks inside `set_option ... in`, but not, for instance, inside `mutual` blocks.

There is a convenience notation `#count_heartbeats` that simply sets the linter option to true.
-/
register_option linter.countHeartbeats : Bool := {
  defValue := false
  descr := "enable the countHeartbeats linter"
}

/--
An option used by the `countHeartbeats` linter: if set to `true`, then the countHeartbeats linter
rounds down to the nearest 1000 the heartbeat count.
-/
register_option linter.countHeartbeatsApprox : Bool := {
  defValue := false
  descr := "if set to `true`, then the countHeartbeats linter rounds down \
            to the nearest 1000 the heartbeat count"
}

namespace CountHeartbeats

@[inherit_doc Mathlib.Linter.linter.countHeartbeats]
def countHeartbeatsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.countHeartbeats (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mut msgs := #[]
  if [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind then
    let s ← get
    if getLinterValue linter.countHeartbeatsApprox (← getLinterOptions) then
      elabCommand (← `(command| #count_heartbeats approximately in $(⟨stx⟩)))
    else
      elabCommand (← `(command| #count_heartbeats in $(⟨stx⟩)))
    msgs := (← get).messages.unreported.toArray.filter (·.severity != .error)
    set s
  match stx.find? (·.isOfKind ``Parser.Command.declId) with
    | some decl =>
      for msg in msgs do logInfoAt decl m!"'{decl[0].getId}' {(← msg.toString).decapitalize}"
    | none =>
      for msg in msgs do logInfoAt stx m!"{← msg.toString}"

initialize addLinter countHeartbeatsLinter

@[inherit_doc Mathlib.Linter.linter.countHeartbeats]
macro "#count_heartbeats" approx:(&" approximately")? : command => do
  let approx ←
    if approx.isSome then
      `(set_option linter.countHeartbeatsApprox true) else
      `(set_option linter.countHeartbeatsApprox false)
  return ⟨mkNullNode
    #[← `(command| set_option linter.countHeartbeats true),
      approx]⟩


end CountHeartbeats

end Mathlib.Linter

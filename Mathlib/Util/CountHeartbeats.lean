/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Lean.CoreM
import Std.Tactic.TryThis

/-!
Defines a command wrapper that prints the number of heartbeats used in the enclosed command.

For example
```
count_heartbeats in
theorem foo : 42 = 6 * 7 := rfl
```
will produce an info message containing a number around 51.
If this number is above the current `maxHeartbeats`, we also print a `Try this:` suggestion.
-/


open Lean Elab Command Meta

namespace Mathlib.CountHeartbeats


/--
Count the heartbeats used in the enclosed command.

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
-/
elab "count_heartbeats " "in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
    if elapsed < max then
      logInfo m!"Used {elapsed} heartbeats, which is less than the current maximum of {max}."
    else
      let mut max' := max
      while max' < elapsed do
        max' := 2 * max'
      logInfo m!"Used {elapsed} heartbeats, which is greater than the current maximum of {max}."
      let m : TSyntax `num := quote max'
      Command.liftCoreM <| MetaM.run' do
        Std.Tactic.TryThis.addSuggestion (← getRef)
          (← set_option hygiene false in `(command| set_option maxHeartbeats $m in $cmd))

/--
Run a command, but then restore the original state, and report just the number of heartbeats.
-/
def elabForHeartbeats (cmd : TSyntax `command) : CommandElabM Nat := do
  let start ← IO.getNumHeartbeats
  -- FIXME really should revert more state here:
  -- can someone advise how to roll back CommandElabM state?
  let env ← getEnv
  elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  setEnv env
  return (← IO.getNumHeartbeats) - start

elab "heartbeat_variation " "in" ppLine cmd:command : command => do
  let n := 10
  let counts ← (List.range n).mapM fun _ => elabForHeartbeats cmd
  let counts := counts.map fun i => i / 1000 -- convert to user-facing heartbeats
  let counts := counts.toArray.qsort (· < ·)
  let μ := counts.foldl (· + · ) 0 / n
  -- We jump through some hoops here to get access to `Float.sqrt`, to avoid imports.
  let var := Float.sqrt <| UInt64.toFloat <| UInt64.ofNat
    ((counts.map fun i => (i - μ)^2).foldl (· + · ) 0)
  let stddev := var.toUInt64.toNat * 100 / μ
  elabCommand cmd
  logInfo s!"Min: {counts[0]!} Max: {counts[n - 1]!} StdDev: {stddev}%"

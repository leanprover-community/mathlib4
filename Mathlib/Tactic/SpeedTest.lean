/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Util.Heartbeats
import Lean.Meta.Tactic.TryThis

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

namespace Mathlib.CountHeartbeat



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
  let min := counts.minimum?.getD 0
  let max := counts.maximum?.getD 0
  let μ := counts.foldl (· + ·) 0 / counts.length
  -- We jump through some hoops here to get access to Float.sqrt, to avoid imports.
  let stddev := (Float.sqrt <| UInt64.toFloat <| UInt64.ofNat
    -- `i - μ + (μ - i)` really computes `|i - μ|` with non-truncated subtraction
    (((counts.map fun i => (i - μ + (μ - i))^2).foldl (· + ·) 0) / counts.length)).toUInt64.toNat
  [min, max, stddev]

/--
Given a `List Nat`, log an info message with the minimum, maximum, and standard deviation.
-/
def logVariation {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (counts : List Nat) : m Unit := do
  if let [min, max, stddev] := variation counts then
  -- convert `[min, max, stddev]` to user-facing heartbeats
  logInfo s!"Min: {min / 1000} Max: {max / 1000} StdDev: {stddev / 10}%"

/-- Count the heartbeats used by a tactic, e.g.: `count_heartbeats simp`. -/
elab "count_heartbeats " tac:tacticSeq : tactic => do
  logInfo s!"{← runTacForHeartbeats tac (revert := false)}"

/--
Run a tactic 10 times, counting the heartbeats used, and log the range and standard deviation.
-/
elab "count_heartbeats! " n:(num)? "in" ppLine tac:tacticSeq : tactic => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  -- First run the tactic `n-1` times, reverting the state.
  let counts ← (List.range (n - 1)).mapM fun _ => runTacForHeartbeats tac
  -- Then run once more, keeping the state.
  let counts := (← runTacForHeartbeats tac (revert := false)) :: counts
  logVariation counts

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
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef)
          (← set_option hygiene false in `(command| set_option maxHeartbeats $m in $cmd))

/-
elab "speed_test " tac1:tacticSeq colGt &"vs" colGt tac2:tacticSeq : tactic => do
  logWarning m!"{tac1} vs {tac2}"
  let n1 ← runTacForHeartbeats tac1
  let n2 ← runTacForHeartbeats tac2
  logInfoAt (← getRef) m!"{n1} vs {n2}"
  evalTactic tac1

example (vs : Nat) : vs = vs := rfl
-/

--example : True := by
--  speed_test
--    · exact .intro
--    vs
--    · exact .intro


def speedTestElab (tacs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
    TacticM (Array Nat) := do
  tacs.mapM runTacForHeartbeats

/-
elab "speed_test " "[" tacs:tacticSeq,* "]": tactic => do
  let tacs := tacs.getElems
  let ns := (← speedTestElab tacs).zip tacs
  logInfoAt (← getRef) m!"{ns}"
  let sorted := ns.qsort (Prod.fst · < Prod.fst ·)
  if 2 ≤ sorted.size then
    logInfoAt sorted[0]!.2 m!"fastest -- {sorted[0]!.1}"
    logWarningAt sorted[sorted.size - 1]!.2 m!"slowest -- {sorted[sorted.size - 1]!.1}"
  evalTactic (sorted.getD 0 default).2
--  evalTactic tac1
--  logWarning m!"{tac1} vs {tac2}"
-/

elab "exact " t:term : tactic => do
  let exaTac ← `(Lean.Parser.Tactic.tacticSeq | exact $t)
  let refTac ← `(Lean.Parser.Tactic.tacticSeq | refine $t)
  match ← speedTestElab #[refTac, exaTac] with
    | #[re, ex] =>
      if re < ex then logWarning m!"`refine` is faster: {re} vs {ex}"
      else logInfo m!"`exact` is not slower: {ex} vs {re}"
    | _ => logInfo "why are we here?"
      evalTactic (← `(tactic| exact $t))

--example : True := by
--  exact .intro


--example : True := by
--  speed_test [
--    exact   .intro,
--    refine  .intro,
--    refine' .intro,
--    exact   True.intro,
--    refine  True.intro,
--    refine' True.intro
--  ]

--elab "speed_test " colGt cmd1:command colGt cmd2:command : command => do
--  logWarning m!"{cmd1} vs {cmd2}"
--  elabCommand cmd1
--  elabCommand cmd2

--speed_test
--  #eval 0


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
Run a command `10` times, reporting the range in heartbeats, and the standard deviation.

Example usage:
```
count_heartbeats! in
def f := 37
```
displays the info message `Min: 7 Max: 8 StdDev: 14%`.
-/
elab "count_heartbeats! " "in" ppLine cmd:command : command => do
  let n := 10
  -- First run the command `n-1` times, reverting the state.
  let counts ← (List.range (n - 1)).mapM fun _ => elabForHeartbeats cmd
  -- Then run once more, keeping the state.
  let counts := (← elabForHeartbeats cmd (revert := false)) :: counts
  logVariation counts

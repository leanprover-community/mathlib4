module

public import Mathlib
import all Mathlib.Tactic.ClickSuggestions.FindPremises

/-!
# Benchmarking `#click_suggestions`

Measure how long it takes to initialize the discrimination trees.

Interestingly, initializing all 4 discrimination trees at the same time is significantly faster
than initializing them one by one, due to the cost of looping through the environment,
and of telescoping the type of each declaration.

There is a trade-off between two design decisions:
1. Build all discrimination trees at the time of writing `#click_suggestions`
2. Build only the discrimination trees that are needed for any given selection.

(1) takes less time overall, but more time upfront. Currently, we use (2).
-/

meta section
namespace Mathlib.Tactic.ClickSuggestions
open Lean Meta

def measureImport (choice : Choice) : MetaM (Nat × PreDiscrTrees) := do
  let t0 ← IO.monoMsNow
  let (tasks, _) ← foldImportedDecls {} { transparency := .reducible, proj := .no }
    (Entries.addConst choice (← getEnv))
  let pre : PreDiscrTrees ← MonadExcept.ofExcept <| tasks.foldlM (·.append <$> ·.get) {}
  return ((← IO.monoMsNow) - t0, pre)

run_meta
  let (all, _) ← measureImport { rw := true, grw := true, app := true, appAt := true }
  guard (all < 20_000)

def measureEach : MetaM MessageData := do
  let (rw, _) ← measureImport { rw := true, grw := false, app := false, appAt := false }
  let (grw, _) ← measureImport { rw := false, grw := true, app := false, appAt := false }
  let (apply, _) ← measureImport { rw := false, grw := false, app := true, appAt := false }
  let (applyAt, _) ← measureImport { rw := false, grw := false, app := false, appAt := true }
  let (all, _) ← measureImport { rw := true, grw := true, app := true, appAt := true }
  return m!"rw: {rw}ms; grw: {grw}ms; apply: {apply}ms; apply at: {applyAt}ms\n\
    total: {all}ms"

/-
Example output:

rw: 5826ms; grw: 3305ms; apply: 4756ms; apply at: 3959ms
total: 9859ms
-/
-- run_meta logInfo (← measureAll)

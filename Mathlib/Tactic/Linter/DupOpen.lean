/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Tactic.Linter.Header

/-!
#  The "dupOpen" linter

The "dupOpen" linter emits a warning when an `open` command opens an already open namespace.
-/

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
Returns the array of repetitions in the input `l`, where multiple repetitions all get reported.
For instance
```lean
#guard  getRepetitions [1, 2, 3, 2, 1, 2] = #[2, 1, 2]
```
-/
def getRepetitions {α} [BEq α] [Hashable α] (l : List α) (init := (∅ : Std.HashSet α)) :
    Array α := Id.run do
  let mut seen := init
  let mut reps := #[]
  for a in l do
    if seen.contains a then
      reps := reps.push a
    else
      seen := seen.insert a
  return reps

/--
The "dupOpen" linter emits a warning when an `open` command opens an already open namespace.

The linter does *not* check whether the declarations accessible with an `open` are actually used
with the shorter name, but simply whether an `open` namespace is repeated.

The check is almost purely syntactical: the linter reads the namespaces in `open` and `namespace`
commands and compares them with the `openDecls` in scope.
-/
register_option linter.dupOpen : Bool := {
  defValue := false
  descr := "enable the dupOpen linter"
}

namespace DupOpen

@[inherit_doc Mathlib.Linter.linter.dupOpen]
def dupOpenLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.dupOpen (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let s ← getScope
  -- `reps` are the repeated namespaces, `os` is the array of identifiers that could be the
  -- culprits of the repetitions and `isNamespace?` is a boolean that is `true` if the command is
  -- `namespace`, rather than `open`.
  let (reps, os, isNamespace?) :=
    match stx with
    | `(namespace $ns) =>
      let stringSegments := s.openDecls.flatMap (s!"{·}".splitOn ".")
      let os := stringSegments.map (mkIdentFrom ns <| .str .anonymous ·)
      let names := ns.getId.components.map (·.toString)
      let reps := getRepetitions names (.ofList stringSegments)
      (reps, os.toArray, true)
    | `(open $os*) =>
      let reps := getRepetitions (s.openDecls.map (s!"{·}"))
      (reps, os, false)
    | _ => default
  let mut toReport : Std.HashSet (String.Range × Name × String) := ∅
  for rep in reps do
    for o in os do
      if rep.endsWith o.getId.toString then
        toReport := toReport.insert (o.raw.getRange?.get!, o.getId, rep)
  let nsMsg (o : Name) :=
    if isNamespace? then m!"  Probably, a previous `open {o}` is still in scope!" else m!""
  for (rg, o, rep) in toReport do
    Linter.logLint linter.dupOpen (.ofRange rg)
      m!"The namespace '{o}' in '{rep}' is already open.{nsMsg o}"

initialize addLinter dupOpenLinter

end DupOpen

end Mathlib.Linter

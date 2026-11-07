/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-! # The `declaredNames` producer linter

`declaredNames` is a stateful linter (`Lean.Elab.Command.registerStatefulLinter`) that acts as
a producer: it does not emit diagnostics. Its pre phase computes the names that the current
command declares, as a diff of `env.constants.map₂` against the names that earlier commands
declared. Consumer linters read the payload with `readCurrentPreState` and obtain the exact
declarations of the command, including macro-generated ones that syntax heuristics miss.

The pre phase walks `env.constants.map₂` once per command. The map contains only the constants
of the current module, so the walk is proportional to the declarations of the file so far.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
The `declaredNames` producer computes the names that each command declares, as an exact
environment diff. Its persistent state is the set of names that earlier commands declared;
its pre-phase payload is the array of names that the current command adds. Consumers read
the payload with `readCurrentPreState`.
-/
public initialize declaredNames : StatefulLinter NameSet (Array Name) ←
  registerStatefulLinter {}
    (pre := fun _ seen _ => do
      let mut new := #[]
      for (n, _) in (← getEnv).constants.map₂ do
        unless seen.contains n do
          new := new.push n
      return some new)
    (post := fun _ seen new _ _ =>
      return (new.getD #[]).foldl (·.insert ·) seen)

end Mathlib.Linter

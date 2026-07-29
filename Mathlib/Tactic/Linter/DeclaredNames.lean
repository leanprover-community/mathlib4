/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Lean.Elab.Command
-- Import `Mathlib.Init` so that this file has a valid copyright header and module docstring.
public import Mathlib.Init  -- shake: keep

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

/-- Persistent state of the `declaredNames` producer: the local constants seen so far. -/
public structure DeclaredSeen where
  /-- The names of `env.constants.map₂` entries that earlier commands declared. -/
  seen : NameSet := {}
  deriving Inhabited

/-- Pre-phase payload of the `declaredNames` producer: the constants of the current command. -/
public structure DeclaredNew where
  /-- The names that the current command added to the environment. -/
  new : Array Name := #[]
  deriving Inhabited

/--
The `declaredNames` producer computes the names that each command declares, as an exact
environment diff. Consumers read the payload with `readCurrentPreState`.
-/
public initialize declaredNames : StatefulLinter DeclaredSeen DeclaredNew ←
  registerStatefulLinter {}
    (pre := fun _ self _ => do
      let env ← getEnv
      let mut new := #[]
      for (n, _) in env.constants.map₂ do
        unless self.seen.contains n do
          new := new.push n
      return some { new })
    (post := fun _ self selfPre _ _ => do
      let some p := selfPre | return self
      return { seen := p.new.foldl (·.insert ·) self.seen })

end Mathlib.Linter

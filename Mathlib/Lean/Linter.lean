/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean.Elab.Command

/-
# Additional utilities for the `Linter` API
-/

open Lean Elab Command Linter

namespace Lean.Linter

/--
Runs a `CommandElabM` action when the provided linter option is `true`.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter option which has been registered in the same module.
-/
@[macro_inline]
def whenLinterOption (opt : Lean.Option Bool) (x : CommandElabM Unit) : CommandElabM Unit := do
  if getLinterValue opt (← getLinterOptions) then x

/--
Runs a `CommandElabM` action when the provided linter option is `false`.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter option which has been registered in the same module.
-/
@[macro_inline]
def whenNotLinterOption (opt : Lean.Option Bool) (x : CommandElabM Unit) : CommandElabM Unit := do
  unless getLinterValue opt (← getLinterOptions) do x

/--
Processes `set_option ... in`s that wrap the input `stx`, then acts on the inner syntax with
`x` after checking that the provided linter option is `true`.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter option which has been registered in the same module.
-/
@[macro_inline]
def whenLinterActivated (opt : Lean.Option Bool) (x : CommandElab) : CommandElab :=
  withSetOptionIn (whenLinterOption opt ∘ x)

end Lean.Linter

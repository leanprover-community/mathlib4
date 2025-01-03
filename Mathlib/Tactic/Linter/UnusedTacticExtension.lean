/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
This file defines the environment extension to keep track of which tactics are allowed to leave
the tactic state unchanged and not trigger the unused tactic linter.
-/

open Lean Elab Command

namespace Mathlib.Linter.UnusedTactic

/--
Defines the `allowedUnusedTacticExt` extension for adding a `HashSet` of `allowedUnusedTactic`s
to the environment.
-/
initialize allowedUnusedTacticExt :
    SimplePersistentEnvExtension SyntaxNodeKind (Std.HashSet SyntaxNodeKind) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addAllowedUnusedTactic stxNodes` takes as input a `HashSet` of `SyntaxNodeKind`s and extends the
`allowedUnusedTacticExt` environment extension with its content.

These are tactics that the unused tactic linter will ignore, since they are expected to not change
the tactic state.

See the `#allow_unused_tactic! ids` command for dynamically extending the extension as a user-facing
command.
-/
def addAllowedUnusedTactic {m : Type → Type} [Monad m] [MonadEnv m]
    (stxNodes : Std.HashSet SyntaxNodeKind) :
    m Unit :=
  stxNodes.foldM (init := ()) fun _ d => modifyEnv (allowedUnusedTacticExt.addEntry · d)

/--
`#allow_unused_tactic! ids` makes the unused tactic linter ignore the tactics mentioned in `ids`.

This change is *persistent*: the linter continues to ignore these tactics also in files importing
a file where this command is issued.

For a file-local change, use `#allow_unused_tactic ids` instead.
-/
elab "#allow_unused_tactic! " colGt ids:ident* : command => do
  let ids := ← liftCoreM do ids.mapM realizeGlobalConstNoOverload
  addAllowedUnusedTactic (.ofArray ids)

/-- `Parser`s allowed to not change the tactic state.
This can be increased dynamically, using `#allow_unused_tactic`.
-/
initialize allowedRef : IO.Ref (Std.HashSet SyntaxNodeKind) ←
  IO.mkRef <| .ofArray #[
    `Mathlib.Tactic.Says.says,
    `Batteries.Tactic.«tacticOn_goal-_=>_»,
    `by,
    `null,
    `«]»,
    -- the following `SyntaxNodeKind`s play a role in silencing `test`s
    `Mathlib.Tactic.successIfFailWithMsg,
    `Mathlib.Tactic.failIfNoProgress,
    `Mathlib.Tactic.ExtractGoal.extractGoal,
    `Mathlib.Tactic.Propose.propose',
    `Lean.Parser.Tactic.traceState,
    `Mathlib.Tactic.tacticMatch_target_,
    `change?,
    `«tactic#adaptation_note_»,
    `tacticSleep_heartbeats_,
    `Mathlib.Tactic.«tacticRename_bvar_→__»
  ]

/-- `#allow_unused_tactic` takes an input a space-separated list of identifiers.
These identifiers are then allowed by the unused tactic linter:
even if these tactics do not modify goals, there will be no warning emitted.
Note: for this to work, these identifiers should be the `SyntaxNodeKind` of each tactic.

For instance, you can allow the `done` and `skip` tactics using
```lean
#allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip
```
Notice that you should use the `SyntaxNodeKind` of the tactic.
-/
elab "#allow_unused_tactic " ids:ident* : command => do
  let ids := ← Command.liftCoreM do ids.mapM realizeGlobalConstNoOverload
  allowedRef.modify (·.insertMany ids)

end Mathlib.Linter.UnusedTactic

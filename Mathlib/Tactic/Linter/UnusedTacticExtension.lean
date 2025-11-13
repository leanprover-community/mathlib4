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
    `Lean.Parser.Tactic.show,
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

/--
`#allow_unused_tactic` takes as input a space-separated list of identifiers.
These identifiers are then allowed by the unused tactic linter:
even if these tactics do not modify goals, there will be no warning emitted.

Note: for this to work, these identifiers should be the `SyntaxNodeKind` of each tactic.

For instance, you can allow the `done` and `skip` tactics using
```lean
#allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip
```

This change is file-local.  If you want a *persistent* change, then use the `!`-flag:
the command `#allow_unused_tactic! ids` makes the change the linter continues to ignore these
tactics also in files importing a file where this command is issued.

The command `#show_kind tac` may help to find the `SyntaxNodeKind`.
-/
elab "#allow_unused_tactic" pers:("!")? ppSpace colGt ids:ident* : command => do
  try
    let ids ← liftCoreM do ids.mapM realizeGlobalConstNoOverload
    if pers.isSome then
      addAllowedUnusedTactic (.ofArray ids)
    else
      allowedRef.modify (·.insertMany ids)
  catch e => match e with
    | .error ref md =>
      logErrorAt ref (md ++ m!"\n\
        The command `#show_kind {ref}` may help to find the correct `SyntaxNodeKind`.")
    | _ => logError e.toMessageData

/--
`#show_kind tac` takes as input the syntax of a tactic and returns the `SyntaxNodeKind`
at the head of the tactic syntax tree.

The input syntax needs to parse, though it can be *extremely* elided.
For instance, to see the `SyntaxNodeKind` of the `refine` tactic, you could use
```lean
#show_kind refine _
```
The trailing underscore `_` makes the syntax valid, since `refine` expects something else.
-/
elab "#show_kind " t:tactic : command => do
  let stx ← `(tactic| $t)
  Lean.logInfoAt t m!"The `SyntaxNodeKind` is '{stx.raw.getKind}'."

end Mathlib.Linter.UnusedTactic

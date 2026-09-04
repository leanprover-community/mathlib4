/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Linter.Basic
public meta import Lean.Server.InfoUtils
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Linting against internal constructors

Sometimes, we want a constructor to be public for definitional equality reasons, but to discourage
access by the user. However, even internal names (e.g. `_mkInternal`) can be used without error via
anonymous constructor notation `⟨...⟩`. This linter assumes internal constructors are internal for
a reason, and lints against using them.

## Future work

- This linter could be extensible in multiple ways:
  - Custom predicates (e.g. the ability to register non-internal constructors as forbidden)
  - Custom lint messages (e.g. saying "please use `fooMk` instead")
- This linter could be accompanied by an environment linter to ensure that no forbidden constructor
  is used in final expressions. Currently this is an elaboration-time linter.
- This linter could be generalized to allow forbidding other sorts of API besides constructors.
- Performance. Currently, this linter has a small but non-negligible performance cost. Depending on
  where exactly the performance cost is coming from, it might be useful to either:
  - merge the `ContextInfo`s lazily (e.g. only when we need its `Environment`)
  - run this linter in parallel alongside other similar infotree-traversing linters, within a single
    infotree traversal
-/

open Lean Elab Command

namespace Mathlib.Tactic.Linter

public meta section

/--
Forbid internal constructors (e.g. `_mkInternal`) from being referenced during elaboration. By
default, this is `true`, and disallows references arising from notation as well (including e.g.
anonymous constructor notation).

Internal constructors may be used freely in the module in which they were defined.
-/
register_option linter.internalConstructors : Bool := {
  -- Note: unlike style linters which are turned on in `Mathlib.Init`, we make this true
  -- everywhere so that downstream libraries do not accidentally use Mathlib internal constructors.
  defValue := true
  descr := "forbid internal constructors from being referenced during elaboration."
}

/-- Lints against using constructors with internal names during elaboration. -/
def internalConstructor : Linter where
  run := withSetOptionIn fun _ => do
    unless Linter.getLinterValue linter.internalConstructors (← Linter.getLinterOptions) do
      return
    for t in ← getInfoTrees do
      t.foldInfoM (init := ()) fun ctx info _ => do
        match info with
        | .ofTermInfo i =>
          let .const n _ := i.expr.cleanupAnnotations | pure ()
          if
            -- Putting the conjuncts in this order provides a performance benefit.
            n.isInternal && !isPrivateName n && ctx.env.isImportedConst n && ctx.env.isConstructor n
          then
            -- Use `withRef` to fall back to outer ref if `info.stx` has no position info
            withRef info.stx do
              logLintError linter.internalConstructors (← getRef)
                m!"`{.ofConstName n}` is an internal constructor and should not be used directly."
        | _ => pure ()
where
  /-- We inline some of `logLint` so that we can log an error instead of a warning. -/
  logLintError (linterOption) (stx) (msg) := do
    let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} false`"
    logErrorAt stx <|
      .ofOriginatingSyntax stx  <|
      .tagged linterOption.name <|
      .tagged Linter.linterMessageTag m!"{msg}{disable}"

initialize addLinter internalConstructor

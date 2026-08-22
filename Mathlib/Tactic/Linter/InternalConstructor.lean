/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Linter.Basic
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Linting against internal constructors

Sometimes, we want a constructor to be public for definitional equality reasons, but to discourage
access by the user. However, even internal names (e.g. `_mkInternal`) can be used without error via
anonymous constructor notation `⟨...⟩`. This linter assumes internal constructors are internal for
a reason, and lints against using them.

## TODO

- This linter could be extensible in multiple ways:
  - Custom predicates (e.g. the ability to register non-internal constructors as forbidden)
  - Custom lint messages (e.g. saying "please use `fooMk` instead")
- This linter could be accompanied by an environment linter to ensure that no forbidden constructor
  is used in final expressions. Currently this is an elaboration-time linter.
- This linter could be generalized to allow forbidding other sorts of API besides constructors.
-/

open Lean Elab Command

namespace Mathlib.Tactic.Linter

public meta section

/--
Allow internal constructors (e.g. `_mkInternal`) to be referenced during elaboration. By
default, this is `false`, and disallows references arising from notation as well (including e.g.
anonymous constructor notation).

Internal constructors may be used freely in the module in which they were defined.
-/
register_option linter.allowInternalConstructors : Bool := {
  -- Note: unlike style linters which are turned on in `Mathlib.Init`, we make this false
  -- everywhere so that downstream libraries do not accidentally use Mathlib internal constructors.
  defValue := false
  descr := "allow internal constructors to be referenced downstream."
}

private partial def logInternalConstructors (t : InfoTree) (ctx? : Option ContextInfo := none) :
    CommandElabM Unit :=
  match t with
  | .context ctx t =>
    logInternalConstructors t <| ctx.mergeIntoOuter? ctx?
  | .hole _ => return
  | .node t ch => do
    if let some ctx := ctx? then
      match t with
      | .ofTermInfo i =>
        let .const n _ := i.expr.cleanupAnnotations | pure ()
        if
          ctx.env.isImportedConst n && !isPrivateName n &&
          n.isInternal && ctx.env.isConstructor n
        then
          -- Use `withRef` to fall back to outer ref if `t.stx` has no position info
          withRef t.stx do
            logLintErrorSuggestingTrue linter.allowInternalConstructors (← getRef)
              m!"`{.ofConstName n}` is an internal constructor and should not be used directly."
      | _ => pure ()
    withRef t.stx do ch.forM (logInternalConstructors · ctx?)
where
  /-- We inline some of `logLint` so that we can (1) log an error (2) adjust the suggested
  option value from `false` to `true`. -/
  logLintErrorSuggestingTrue (linterOption) (stx) (msg) := do
    let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} true`"
    logErrorAt stx <|
      .ofOriginatingSyntax stx  <|
      .tagged linterOption.name <|
      .tagged Linter.linterMessageTag m!"{msg}{disable}"

/-- Lints against using constructors with internal names during elaboration. -/
def internalConstructor : Linter where
  run := withSetOptionIn fun _ => do
    if Linter.getLinterValue linter.allowInternalConstructors (← Linter.getLinterOptions) then
      return
    for t in ← getInfoTrees do
      logInternalConstructors t

initialize addLinter internalConstructor

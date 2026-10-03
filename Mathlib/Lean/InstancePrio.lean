/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Elab.Declaration

/-!
# Override for the `instance` command that sets priorities automatically.
-/

public meta section

namespace Lean.Elab.Command

open Lean Meta Parser Command

/-- Default priority used for specific instances. -/
def specificInstancePrio := 2000

/-- Wrap the declaration elaborator so more specific instances get declared with a high priority.

An instance counts as unspecific if it has a trivial discrimination tree key
(looking like `[ClassName, *, ..., *]`).
-/
@[command_elab declaration, incremental]
def elabInstanceWithPrio : CommandElab := fun stx => do
  let oldEnv := (← get).env
  -- TODO: this is a bit fragile, what if someone else wants to wrap `elabDeclaration` themselves?
  -- We might like to have some sort of hook instead, which can run one after another,
  -- instead of overriding each other.
  elabDeclaration stx
  let newEnv := (← get).env
  for (name, info) in newEnv.constants do
    -- Check that `name` is an instance in `newEnv` but was not before.
    -- This covers two cases:
    -- * `name` is a new declaration (and so it is not in `oldEnv`, nor in `oldEnv`'s instances)
    -- * `name` is an existing declaration (so it is in `oldEnv`), but it isn't in `oldEnv`'s instances
    -- The first case handles `instance` and `@[instance] def`, but also `class Bar extends Foo`.
    -- I expect the second case does not occur, but it would be useful to cover it anyway.
    let some instEntry :=
        instanceExtension.getState newEnv |>.instanceNames.find? name
      | continue
    if !isInstanceCore oldEnv name &&
        -- Only update the priority if it has not been set already.
        -- TODO: this check is a bit too coarse: `instance (priority := 1000) ...` should count as
        -- a manual override, but we update it anyway.
        instEntry.priority == 1000 then
      -- This is adapted from `mkKey` in the implementation of `#discr_tree_key`.
      let key ← liftTermElabM do
        let (_, _, type) ← withReducible <| forallMetaTelescopeReducing info.type
        let type ← whnfR type
        DiscrTree.mkPath type
      -- If the key doesn't look like `[ClassName, *, ..., *]`, raise the priority.
      if key[1:].any (· != .star) then
        instanceExtension.add
          { instEntry with priority := specificInstancePrio }
          (← liftCoreM <| getInstanceAttrKind? name).get!

end Lean.Elab.Command

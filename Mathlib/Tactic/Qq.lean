/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Init
import Qq

/-!
# Extra Qq tooling

These utility functions could be upstreamed to Qq.
-/

open Lean

namespace Qq

/-- Return a local declaration whose type is definitionally equal to `sort`.

This is a Qq version of `Lean.Meta.findLocalDeclWithType?` -/
def findLocalDeclWithType? {u : Level} (sort : Q(Sort u)) : MetaM (Option Q($sort)) := do
  let some fvarId ← Meta.findLocalDeclWithType? q($sort) | return none
  return some <| .fvar fvarId

end Qq

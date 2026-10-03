/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Batteries.Tactic.Lint.Basic

/-!
# The "wellTypedAtReducibility" linter
-/

open Lean Meta Elab.Term

namespace Mathlib.Linter

/-- Checks that definitions are well-typed at their reducibility. -/
@[env_linter] public meta def wellTypedAtReducibility : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "All definitions are well-typed at their reducibility"
  errorsFound := "Found definitions that are ill-typed at their reducibility"
  test declName := do
    if (← getEnv).isAutoDecl declName then return none
    let .defnInfo {value := body, type := type, ..} :=
      (← getEnv).find? declName |>.get! | return none
    let reducibility ← getReducibilityStatus declName
    let transparency : TransparencyMode :=
      match reducibility with
      | .reducible => .reducible
      | .instanceReducible => .instances
      | .implicitReducible => .implicit
      | .semireducible => .default
      | .irreducible => .all
    if transparency matches .all then return none
    let header := m!"This definition is ill-typed at @{reducibility.toAttrString}:\n"
    try
      Meta.check body transparency
    catch ex =>
      return header ++ ex.toMessageData
    let inferredType ← inferType body
    unless ← withTransparency transparency (Meta.isDefEq inferredType type) do
      return header ++ (← Elab.Term.mkTypeMismatchError none body inferredType type)
    return none

end Mathlib.Linter

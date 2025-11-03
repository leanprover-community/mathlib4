/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init
import Lean.Meta.Tactic.Util
import Lean.SubExpr

/-! This file defines some functions for dealing with `SubExpr.GoalsLocation`. -/

namespace Lean.SubExpr.GoalsLocation
/-- The root expression of the position specified by the `GoalsLocation`. -/
def rootExpr : GoalsLocation → MetaM Expr
  | ⟨_, .hyp fvarId⟩        => do instantiateMVars (← fvarId.getType)
  | ⟨_, .hypType fvarId _⟩  => do instantiateMVars (← fvarId.getType)
  | ⟨_, .hypValue fvarId _⟩ => do instantiateMVars (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩     => do instantiateMVars (← mvarId.getType)

/-- The `SubExpr.Pos` specified by the `GoalsLocation`. -/
def pos : GoalsLocation → Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

/-- The hypothesis specified by the `GoalsLocation`. -/
def fvarId? : GoalsLocation → Option FVarId
  | ⟨_, .hyp fvarId⟩        => fvarId
  | ⟨_, .hypType fvarId _⟩  => fvarId
  | ⟨_, .hypValue fvarId _⟩ => fvarId
  | ⟨_, .target _⟩          => none

end Lean.SubExpr.GoalsLocation

/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean.Elab.Tactic.Basic
/-!
# Additions to `Lean.Elab.Tactic.Basic`
-/

open Lean Elab Tactic

namespace Lean.Elab.Tactic

/-- Return expected type for the main goal, cleaning up annotations.
Remark: note that `MVarId.getType'` uses `whnf` instead of `cleanupAnnotations`, and
`MVarId.getType''` also uses `cleanupAnnotations` -/
def getMainTarget' : TacticM Expr :=
  return (← getMainTarget).cleanupAnnotations

end Lean.Elab.Tactic

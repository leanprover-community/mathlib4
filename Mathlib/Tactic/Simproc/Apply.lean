/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Util.AtLocation

/-!
# Procedure to execute a custom Simproc

The only function `Simproc.apply` defined in this file takes a `s : Simproc` and executes it on the
goal.
-/

namespace Lean.Meta.Simp.Simproc

open Elab.Tactic Mathlib.Tactic

/-- Execute the given `Simproc` on the goal. -/
def apply (s : Simproc) (proc : String) (loc : Option Location) : TacticM Unit := do
  let ctx ← mkContext (simpTheorems := #[])
  transformAtLocation ((·.1) <$> mainCore · ctx (methods := {post := s}))
    debug (loc.getD (.targets #[] true))

end Lean.Meta.Simp.Simproc

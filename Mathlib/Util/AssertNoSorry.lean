/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Lean.Elab.Print
import Lean.Environment

/-!
# Defines `assert_no_sorry` command.

Throws an error if the given identifier uses sorryAx.
-/

/-- Throws an error if the given identifier uses sorryAx. -/
elab "assert_no_sorry " n:ident : command => do
  let env ← Lean.getEnv
  let (_, s) := ((Lean.Elab.Command.CollectAxioms.collect n.getId).run env).run {}
  if s.axioms.contains ``sorryAx
  then throwError "{n} contains sorry"

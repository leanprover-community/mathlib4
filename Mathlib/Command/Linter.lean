/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

/-! # A test linter. -/
open Lean

initialize addLinter {
  name := `testLinter
  run := fun stx => do
    let mut n := 1
    for stx in stx.topDown do
      n := n + stx.getNumArgs
      if n == 0 then logInfo s!"impossible..."
}

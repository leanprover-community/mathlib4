/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Elab.Command
import Mathlib.Lean.Elab.InfoTree

/-! For benching. -/

open Lean Elab

namespace Mathlib.Tactic

/-- Does work. -/
def workLinter : Linter where
  run _ := do
    for t in ← getInfoTrees do
      let _ := t.getDeclsByBody

initialize addLinter workLinter

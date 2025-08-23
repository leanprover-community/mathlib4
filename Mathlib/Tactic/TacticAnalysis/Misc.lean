/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Tactic.TacticAnalysis.FunProp

/-!
# Tactic linters

This file defines passes to run from the tactic analysis framework.
-/

open Lean Mathlib

/-- Suggest replacing the `aesop` tactic with `simp_all` if that also solves the goal.
`aesop` runs `simp_all` internally, so using `simp_all` is simply faster. -/
register_option linter.tacticAnalysis.aesopToSimpall : Bool := {
  defValue := false
}

-- TODO: double-check the aesop parser is right; add tests for all of this!
@[tacticAnalysis linter.tacticAnalysis.aesopToSimpall,
  inherit_doc linter.tacticAnalysis.aesopToSimpall]
def aesopToSimpall :=
  tacticReplacementWith #[`Aesop.Frontend.Parser.aesop] (`(tactic| simp_all)) m!"simp_all"
    m!"'simp_all' can already solve this, so will be a bit faster"

-- XXX: try a different operation first?
/-- Suggest replacing the `simp_all` tactic with `simp` if that also solves the goal.
This is simply faster. -/
register_option linter.tacticAnalysis.simpallToSimp : Bool := {
  defValue := false
}

-- TODO: double-check the aesop parser is right; add tests for all of this!
@[tacticAnalysis linter.tacticAnalysis.simpallToSimp,
  inherit_doc linter.tacticAnalysis.simpallToSimp]
def simpallToSimp :=
  tacticReplacementWith #[`simp_all] (`(tactic| simp)) m!"simp"
    m!"'simp' can already solve this, so will be a bit faster"

-- XXX: this linter might be more contentious
-- Note that `norm_num1` does not call simp, so is fine. Add a test for this!
/-- Suggest replacing the `norm_num` tactic with `simp` if that also solves the goal.
`norm_num` runs `simp` internally, so using `simp` is simply faster and perhaps clearer. -/
register_option linter.tacticAnalysis.normnumToSimp : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.normnumToSimp,
  inherit_doc linter.tacticAnalysis.normnumToSimp]
def normnumToSimp :=
  tacticReplacementWith #[`Mathlib.Tactic.normNum] (`(tactic| simp)) m!"simp"
    m!"'simp' can already solve this, so will be a bit faster"

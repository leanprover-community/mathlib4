/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.DiagnoseDefEq

/-!
# Tests for `#diagnoseDefEqI`

A minimal example: `myNatAdd` wraps `Nat.add` but is NOT `@[reducible]` and NOT an instance.
So at `reducibleAndInstances` transparency it cannot be unfolded, while the synthesized
`Add Nat` instance (which IS an instance) can. The tool should identify `myNatAdd` as the blocker.
-/

private def myNatAdd : Add Nat := ⟨Nat.add⟩

#diagnoseDefEqI myNatAdd vs (inferInstance : Add Nat)

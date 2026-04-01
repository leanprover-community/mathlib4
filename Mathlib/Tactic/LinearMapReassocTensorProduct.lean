/-
Copyright (c) 2026 Cody Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Mitchell
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Tactic.LinearMapReassoc

/-! Additional `TensorProduct` reassoc exports for linear maps. -/
attribute [reassoc] TensorProduct.comm_comp_comm
attribute [simp] TensorProduct.comm_comp_comm_assoc

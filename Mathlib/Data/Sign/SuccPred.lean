/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Sign.Defs
public import Mathlib.Order.SuccPred.Basic

/-!
# Successor and predecessor order instances

This file defines the `SuccOrder` and `PredOrder` instances for `SignType`.
-/

@[expose] public section

instance : SuccOrder SignType where
  succ
  | -1 => 0
  | _ => 1
  le_succ := by decide
  max_of_succ_le := by unfold IsMax; decide
  succ_le_of_lt := by decide

-- TODO: use `to_dual`
instance : PredOrder SignType where
  pred
  | 1 => 0
  | _ => -1
  pred_le := by decide
  min_of_le_pred := by unfold IsMin; decide
  le_pred_of_lt := by decide

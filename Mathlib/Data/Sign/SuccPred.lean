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

open Order

namespace SignType

instance : SuccOrder SignType where
  succ
  | -1 => 0
  | _ => 1
  le_succ := by decide
  max_of_succ_le := by unfold IsMax; decide
  succ_le_of_lt := by decide

@[simp] theorem succ_neg_one : succ -1 = 0 := rfl
@[simp] theorem succ_zero : succ 0 = 1 := rfl
@[simp] theorem succ_one : succ 1 = 1 := rfl

-- TODO: use `to_dual`
instance : PredOrder SignType where
  pred
  | 1 => 0
  | _ => -1
  pred_le := by decide
  min_of_le_pred := by unfold IsMin; decide
  le_pred_of_lt := by decide

@[simp] theorem pred_neg_one : pred -1 = -1 := rfl
@[simp] theorem pred_zero : pred 0 = -1 := rfl
@[simp] theorem pred_one : pred 1 = 0 := rfl

end SignType

/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap.Basic
import Std.Lean.SMap
import Mathlib.Lean.Expr.Basic

/-!
# Additional functions on `Lean.Name`.

We provide `Name.getModule`,
and `allNames` and `allNamesByModule`.
-/

open Lean Meta Elab

/-- Returns the very first part of a name: for `Mathlib.Data.Set.Basic` it returns `Mathlib`. -/
def getModule (name : Name) (s := "") : Name :=
  match name with
    | .anonymous => s
    | .num _ _ => panic s!"panic in `getModule`: did not expect numerical name: {name}."
    | .str pre s => getModule pre s

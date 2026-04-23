/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Sym.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Vector
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Finiteness of vector types
-/

@[expose] public section

variable {α : Type*}

instance List.Vector.finite [Finite α] {n : ℕ} : Finite (Vector α n) := by
  haveI := Fintype.ofFinite α
  infer_instance

instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  classical
  haveI := Fintype.ofFinite α
  infer_instance

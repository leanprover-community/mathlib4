/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Vector

/-!
# Finiteness of vector types
-/

variable {α : Type*}

instance List.Vector.finite [Finite α] {n : ℕ} : Finite (Vector α n) := by
  haveI := Fintype.ofFinite α
  infer_instance

instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  classical
  haveI := Fintype.ofFinite α
  infer_instance

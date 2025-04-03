/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Logic.Equiv.Array

/-!
# `align` information for `Fintype` declarations around mathlib3's `array` (now `Vector`)
-/


variable {α : Type*}

-- Porting note: `DArray` does not exist in std4/mathlib4
-- instance DArray.fintype {n : ℕ} {α : Fin n → Type*} [∀ n, Fintype (α n)] :
--     Fintype (DArray n α) :=
--   Fintype.ofEquiv _ (Equiv.dArrayEquivFin _).symm

-- Porting note: The closest thing to `Array' n α` is `Vector n α`, for which we already have this
-- intance elsewhere.
-- instance Array'.fintype {n : ℕ} {α : Type*} [Fintype α] : Fintype (Array' n α) :=
--   DArray.fintype

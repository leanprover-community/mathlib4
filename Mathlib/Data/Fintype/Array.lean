/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.array
! leanprover-community/mathlib commit 78314d08d707a6338079f00094bbdb90bf11fc41
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Logic.Equiv.Array

/-!
# `align` information for `Fintype` declarations around mathlib3's `array` (now `Vector`)
-/


variable {α : Type _}

-- porting note: `DArray` does not exist in std4/mathlib4
-- instance DArray.fintype {n : ℕ} {α : Fin n → Type _} [∀ n, Fintype (α n)] : Fintype (DArray n α) :=
--   Fintype.ofEquiv _ (Equiv.dArrayEquivFin _).symm
#noalign d_array.fintype

-- porting note: The closest thing to `Array' n α` is `Vector n α`, for which we already have this
-- intance elsewhere.
-- instance Array'.fintype {n : ℕ} {α : Type _} [Fintype α] : Fintype (Array' n α) :=
--   DArray.fintype
#align array.fintype Vector.fintypeₓ

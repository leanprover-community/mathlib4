/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.cast.prod
! leanprover-community/mathlib commit ee0c179cd3c8a45aa5bffbf1b41d8dbede452865
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Group.Prod

/-!
# The product of two `AddMonoidWithOne`s.
-/


variable {α β : Type _}

namespace Prod

variable [AddMonoidWithOne α] [AddMonoidWithOne β]

instance : AddMonoidWithOne (α × β) :=
  { Prod.instAddMonoidSum, @instOneProd α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]
theorem fst_natCast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]
#align prod.fst_nat_cast Prod.fst_natCast

@[simp]
theorem snd_natCast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]
#align prod.snd_nat_cast Prod.snd_natCast

end Prod

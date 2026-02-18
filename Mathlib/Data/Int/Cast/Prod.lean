/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Nat.Cast.Prod

/-!
# The product of two `AddGroupWithOne`s.
-/

@[expose] public section


namespace Prod

variable {α β : Type*} [AddGroupWithOne α] [AddGroupWithOne β]

instance : AddGroupWithOne (α × β) :=
  { Prod.instAddMonoidWithOne, Prod.instAddGroup with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by ext <;> simp
    intCast_negSucc := fun _ => by ext <;> simp }

@[simp]
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl

@[simp]
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl

end Prod

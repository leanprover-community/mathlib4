/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Prod

#align_import data.int.cast.prod from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# The product of two `AddGroupWithOne`s.
-/


namespace Prod

variable {α β : Type*} [AddGroupWithOne α] [AddGroupWithOne β]

instance instIntCast : IntCast (α × β) where
  intCast := fun n => (n,n)

instance instAddGroupWithOne : AddGroupWithOne (α × β) :=
  { Prod.instAddMonoidWithOne, Prod.instAddGroup with
    toIntCast := instIntCast, -- cannot directly infer this instance with ‹IntCast (α × β)›
    intCast_ofNat := fun _ => by simp only [IntCast.intCast, Int.cast_ofNat]; rfl
    intCast_negSucc := fun _ => by
      simp only [IntCast.intCast, Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]; rfl }

@[simp]
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl
#align prod.fst_int_cast Prod.fst_intCast

@[simp]
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl
#align prod.snd_int_cast Prod.snd_intCast

end Prod

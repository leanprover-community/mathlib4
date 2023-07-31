/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Prod

#align_import data.int.cast.prod from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# The product of two `AddGroupWithOne`s.
-/


namespace Prod

variable {α β : Type _} [AddGroupWithOne α] [AddGroupWithOne β]

instance instAddGroupWithOne : AddGroupWithOne (α × β) :=
  -- { Prod.instAddMonoidWithOneProd, Prod.instAddGroupSum with
  { add_left_neg := Prod.instAddGroupSum.add_left_neg
    sub_eq_add_neg := Prod.instAddGroupSum.sub_eq_add_neg
    zsmul := Prod.instAddGroupSum.zsmul
    zsmul_succ' := Prod.instAddGroupSum.zsmul_succ'
    zsmul_zero' := Prod.instAddGroupSum.zsmul_zero'
    zsmul_neg' := Prod.instAddGroupSum.zsmul_neg'
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by simp; rfl
    intCast_negSucc := fun _ => by simp; rfl }

-- instance og : AddGroupWithOne (α × β) :=
--   { Prod.instAddMonoidWithOneProd, Prod.instAddGroupSum with
--     intCast := fun n => (n, n)
--     intCast_ofNat := fun _ => by simp; rfl
--     intCast_negSucc := fun _ => by simp; rfl }
--
-- example : instAddGroupWithOne = og (α := α) (β := β) := rfl

@[simp]
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl
#align prod.fst_int_cast Prod.fst_intCast

@[simp]
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl
#align prod.snd_int_cast Prod.snd_intCast

end Prod

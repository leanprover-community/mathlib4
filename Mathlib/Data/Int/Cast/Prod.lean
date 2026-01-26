import Mathlib.Data.Int.Cast.Defs

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

/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Prod

#align_import data.nat.cast.prod from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# The product of two `AddMonoidWithOne`s.
-/

assert_not_exists MonoidWithZero

variable {α β : Type*}

namespace Prod

variable [AddMonoidWithOne α] [AddMonoidWithOne β]

instance instAddMonoidWithOne : AddMonoidWithOne (α × β) :=
  { Prod.instAddMonoid, @Prod.instOne α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]
theorem fst_natCast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]
#align prod.fst_nat_cast Prod.fst_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem fst_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : α × β)).1 = (OfNat.ofNat n : α) :=
  rfl

@[simp]
theorem snd_natCast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]
#align prod.snd_nat_cast Prod.snd_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem snd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : α × β)).2 = (OfNat.ofNat n : β) :=
  rfl

end Prod

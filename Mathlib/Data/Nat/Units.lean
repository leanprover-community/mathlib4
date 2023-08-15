/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Units

#align_import data.nat.units from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # The units of the natural numbers as a `Monoid` and `AddMonoid` -/


namespace Nat

theorem units_eq_one (u : ℕˣ) : u = 1 :=
  Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩
#align nat.units_eq_one Nat.units_eq_one

theorem addUnits_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1
#align nat.add_units_eq_zero Nat.addUnits_eq_zero

@[simp]
protected theorem isUnit_iff {n : ℕ} : IsUnit n ↔ n = 1 :=
  Iff.intro
    (fun ⟨u, hu⟩ =>
      match n, u, hu, Nat.units_eq_one u with
      | _, _, rfl, rfl => rfl)
    fun h => h.symm ▸ ⟨1, rfl⟩
#align nat.is_unit_iff Nat.isUnit_iff

instance unique_units : Unique ℕˣ where
  default := 1
  uniq := Nat.units_eq_one
#align nat.unique_units Nat.unique_units

instance unique_addUnits : Unique (AddUnits ℕ) where
  default := 0
  uniq := Nat.addUnits_eq_zero
#align nat.unique_add_units Nat.unique_addUnits

end Nat

/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Unique

/-!
# The unit of the natural numbers
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! #### Units -/

lemma units_eq_one (u : ℕˣ) : u = 1 := Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

lemma addUnits_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1

instance unique_units : Unique ℕˣ where
  default := 1
  uniq := Nat.units_eq_one

instance unique_addUnits : Unique (AddUnits ℕ) where
  default := 0
  uniq := Nat.addUnits_eq_zero

/-- Alias of `isUnit_iff_eq_one` for discoverability. -/
protected lemma isUnit_iff {n : ℕ} : IsUnit n ↔ n = 1 := isUnit_iff_eq_one

/-- Alias of `isAddUnit_iff_eq_zero` for discoverability. -/
protected lemma isAddUnit_iff {n : ℕ} : IsAddUnit n ↔ n = 0 := isAddUnit_iff_eq_zero

end Nat


-- Dual/order lemmas discovered by the Manifold Destiny verifier-mediated learner.
-- Paper: https://github.com/sumofagents/manifold-destiny
section
theorem ENat.WithTop.natCast_add_cancel : ∀ {a b : WithTop ℕ∞} {c : ℕ}, ↑c + a = ↑c + b ↔ a = b := by
  open ENat ENat.WithBot Function in
    intro a b c
    exact ((IsAddLeftRegular.all c).withBot.withTop.eq_iff)

theorem ENat.WithTop.one_add_cancel : ∀ {a b : WithTop ℕ∞}, 1 + a = 1 + b ↔ a = b := by
  open ENat ENat.WithBot Function in
    intro a b
    exact ((IsAddLeftRegular.all 1).withBot.withTop.eq_iff)

theorem ENat.WithTop.add_natCast_cancel : ∀ {a b : WithTop ℕ∞} {c : ℕ}, a + ↑c = b + ↑c ↔ a = b := by
  open ENat ENat.WithBot Function in
    intro a b c
    exact ((IsAddRightRegular.all c).withBot.withTop.eq_iff)

theorem ENat.WithTop.add_one_cancel : ∀ {a b : WithTop ℕ∞}, a + 1 = b + 1 ↔ a = b := by
  open ENat ENat.WithBot Function in
    intro a b
    exact ((IsAddRightRegular.all 1).withBot.withTop.eq_iff)

end

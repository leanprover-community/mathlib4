/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice

/-!
# Bounded lattices

This file contains miscellaneous lemmas about lattices with top or bottom elements.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[DistribLattice α] [OrderBot α]`.
  It captures the properties of `Disjoint` that are common to `GeneralizedBooleanAlgebra` and
  `DistribLattice` when `OrderBot`.
* Bounded and distributive lattice. Notated by `[DistribLattice α] [BoundedOrder α]`.
  Typical examples include `Prop` and `Set α`.
-/

public section

open Function OrderDual

variable {α β : Type*}

/-! ### Top, bottom element -/

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α]

@[to_dual] theorem top_sup_eq (a : α) : ⊤ ⊔ a = ⊤ := sup_of_le_left le_top
@[to_dual] theorem sup_top_eq (a : α) : a ⊔ ⊤ = ⊤ := sup_of_le_right le_top

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

@[to_dual] theorem bot_sup_eq (a : α) : ⊥ ⊔ a = a := sup_of_le_right bot_le
@[to_dual] theorem sup_bot_eq (a : α) : a ⊔ ⊥ = a := sup_of_le_left bot_le

@[to_dual (attr := simp, grind =)]
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff]; simp

end SemilatticeSupBot

section LinearOrder

variable [LinearOrder α] [OrderBot α]

-- `simp` can prove these, so they shouldn't be simp-lemmas.

@[to_dual] theorem min_bot_left (a : α) : min ⊥ a = ⊥ := bot_inf_eq _
@[to_dual] theorem min_bot_right (a : α) : min a ⊥ = ⊥ := inf_bot_eq _

@[to_dual] theorem max_bot_left (a : α) : max ⊥ a = a := bot_sup_eq _
@[to_dual] theorem max_bot_right (a : α) : max a ⊥ = a := sup_bot_eq _

@[to_dual] theorem max_eq_bot {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := sup_eq_bot_iff

@[to_dual (attr := simp)]
theorem min_eq_bot {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp_rw [← le_bot_iff, inf_le_iff]

@[to_dual (attr := aesop (rule_sets := [finiteness]) safe apply)]
lemma min_ne_bot {a b : α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : min a b ≠ ⊥ := by
  grind

end LinearOrder

/-! ### Induction on `WellFoundedGT` and `WellFoundedLT` -/

section WellFounded

@[to_dual (attr := elab_as_elim)]
theorem WellFoundedGT.induction_top [Preorder α] [WellFoundedGT α] [OrderTop α]
    {P : α → Prop} (hexists : ∃ M, P M) (hind : ∀ N ≠ ⊤, P N → ∃ M > N, P M) : P ⊤ := by
  contrapose! hexists
  intro M
  induction M using WellFoundedGT.induction with
  | ind x IH =>
    by_cases hx : x = ⊤
    · exact hx ▸ hexists
    · intro hx'
      obtain ⟨M, hM, hM'⟩ := hind x hx hx'
      exact IH _ hM hM'

end WellFounded

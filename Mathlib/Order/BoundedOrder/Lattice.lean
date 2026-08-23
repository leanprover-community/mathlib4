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

variable {α : Type*}

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

/-- Let `r` be a relation on `α`, let `f : α → β` be a function, let `C : β → Prop`, and
let `bot : α`. This induction principle shows that `C (f bot)` holds, given that
* some `a` that is accessible by `r` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
theorem Acc.induction_bot' {α β} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : β → Prop}
    {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) : C (f a) → C (f bot) :=
  (@Acc.recOn _ _ (fun x _ => C (f x) → C (f bot)) _ ha) fun x _ ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) (fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂)

/-- Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and `C c`. -/
theorem Acc.induction_bot {α} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : α → Prop}
    (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  ha.induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `f : α → β` be a function,
let `C : β → Prop`, and let `bot : α`.
This induction principle shows that `C (f bot)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
theorem WellFounded.induction_bot' {α β} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : β → Prop} {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) :
    C (f a) → C (f bot) :=
  (hwf.apply a).induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that `bot` is
the smallest element w.r.t. `r` that satisfies `C`. -/
theorem WellFounded.induction_bot {α} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  hwf.induction_bot' ih

/-- Let `α` be a type with well-founded `<`, let `f : α → β` be a function, and let `C : β → Prop`.
This induction principle shows that `C (f ⊥)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f ⊥` and `C (f b)` holds, there is `c < b` with `C (f c)`. -/
@[to_dual
/-- Let `α` be a type with well-founded `>`, let `f : α → β` be a function, and let `C : β → Prop`.
This induction principle shows that `C (f ⊤)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f ⊤` and `C (f b)` holds, there is `c > b` with `C (f c)`. -/]
theorem WellFoundedLT.induction_bot' {α β} [LT α] [Bot α] [WellFoundedLT α]
    {a : α} {C : β → Prop} {f : α → β} (ih : ∀ b, f b ≠ f ⊥ → C (f b) → ∃ c < b, C (f c)) :
    C (f a) → C (f ⊥) :=
  (wellFounded_lt.apply a).induction_bot' ih

/-- Let `α` be a type with well-founded `<`, and let `C : β → Prop`.
This induction principle shows that `C ⊥` holds, given that
* some `a` satisfies `C a`, and
* for each `b` such that `b ≠ ⊥` and `C b` holds, there is `c < b` with `C c`. -/
@[to_dual
/-- Let `α` be a type with well-founded `>`, and let `C : β → Prop`.
This induction principle shows that `C ⊤` holds, given that
* some `a` satisfies `C a`, and
* for each `b` such that `b ≠ ⊤` and `C b` holds, there is `c > b` with `C c`. -/]
theorem WellFoundedLT.induction_bot {α} [LT α] [Bot α] [WellFoundedLT α]
    {a : α} {C : α → Prop} (ih : ∀ b, b ≠ ⊥ → C b → ∃ c < b, C c) :
    C a → C ⊥ :=
  (wellFounded_lt.apply a).induction_bot' ih
  
end WellFounded

/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Tactic.Coe -- ↥ -- remove?
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Init.Data.Nat.Lemmas -- partial order on ℕ
import Mathlib.Init.Function -- Function.injective

-- to be removed
-- import Mathlib.Tactic.SimpTrace
-- import Mathlib.Tactic.PrintPrefix
-- import Std.Tactic.Lint

/-!
# booleans

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Notations

This file introduces the notation `!b` for `not b`, the boolean "not".

## Tags
bool, boolean, Bool, De Morgan

## TODO

in Lean 3,
decidable.to_bool : Π (p : Prop) [h : decidable p], bool

In Lean 4,
decide : (p : Prop) → [h : Decidable p] → Bool

Lean 3 has init.data.bool.lemmas . Should I be porting these too?

I deleted notation ! because it must be elsewhere
-/

namespace Bool

-- TODO unwanted?
theorem CoeSort_coe_true : (↥ true : Prop) = True :=
  by simp only

-- TODO unwanted?
theorem CoeSort_coe_false : (↥ false : Prop) = False :=
  by simp only

theorem decide_True {h} : @decide True h = true :=
  decide_eq_true True.intro

theorem decide_False {h} : @decide False h = false :=
  decide_eq_false id

@[simp]
theorem decide_coe (b : Bool) {h} : @decide b h = b := by
  cases b
  { exact decide_eq_false $ λ j => by cases j }
  { exact decide_eq_true $ rfl }

theorem coe_decide (p : Prop) [d : Decidable p] : decide p ↔ p :=
  match d with
  | isTrue hp => ⟨λ _ => hp, λ _ => rfl⟩
  | isFalse hnp => ⟨λ h => Bool.noConfusion h, λ hp => (hnp hp).elim⟩

theorem of_decide_iff {p : Prop} [Decidable p] : decide p ↔ p :=
  coe_decide p

@[simp]
theorem true_eq_decide_iff {p : Prop} [Decidable p] : true = decide p ↔ p :=
  eq_comm.trans of_decide_iff

@[simp]
theorem false_eq_decide_iff {p : Prop} [Decidable p] : false = decide p ↔ ¬p :=
  eq_comm.trans (decide_false_iff _)

theorem decide_not (p : Prop) [Decidable p] : (decide ¬p) = not (decide p) := by
  by_cases p <;> simp [*]

-- #align to_bool_not decide_not

@[simp]
theorem decide_and (p q : Prop) [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]

@[simp]
theorem decide_or (p q : Prop) [Decidable p] [Decidable q] : decide (p ∨ q) = (p || q) := by
  by_cases p <;> by_cases q <;> simp [*]

@[simp]
theorem decide_eq {p q : Prop} [Decidable p] [Decidable q] : decide p = decide q ↔ (p ↔ q) :=
  ⟨fun h => (coe_decide p).symm.trans <| by simp [h], decide_congr⟩

theorem not_false' : ¬false := fun.
-- wtf why does ff_ne_tt exist in this form?

@[simp]
theorem default_bool : default = false :=
  rfl

theorem dichotomy (b : Bool) : b = false ∨ b = true := by cases b <;> simp

@[simp]
theorem forall_bool {p : Bool → Prop} : (∀ b, p b) ↔ p false ∧ p true :=
  ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ b => by cases b <;> assumption⟩

@[simp]
theorem exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  ⟨fun ⟨b, h⟩ => by cases b; exact Or.inl h; exact Or.inr h,
  fun h => match h with
  | .inl h => ⟨_, h⟩
  | .inr h => ⟨_, h⟩ ⟩

/-- If `p b` is decidable for all `b : bool`, then `∀ b, p b` is decidable -/
instance decidableForallBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∀ b, p b) :=
  decidable_of_decidable_of_iff forall_bool.symm

/-- If `p b` is decidable for all `b : bool`, then `∃ b, p b` is decidable -/
instance decidableExistsBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∃ b, p b) :=
  decidable_of_decidable_of_iff exists_bool.symm

@[simp]
theorem cond_ff {α} (t e : α) : cond false t e = e :=
  rfl

@[simp]
theorem cond_tt {α} (t e : α) : cond true t e = t :=
  rfl

@[simp]
theorem cond_to_bool {α} (p : Prop) [Decidable p] (t e : α) : cond (decide p) t e = if p then t else e := by
  by_cases p <;> simp [*]

@[simp]
theorem cond_bnot {α} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by cases b <;> rfl

theorem bnot_ne_id : not ≠ id := fun h => ff_ne_tt <| congrFun h true

theorem coe_bool_iff : ∀ {a b : Bool}, (a ↔ b) ↔ a = b := by decide

theorem eq_true_of_ne_false : ∀ {a : Bool}, a ≠ false → a = true := by decide
-- #align eq_tt_of_ne_ff with eq_true_of_ne_false

theorem eq_false_of_ne_true : ∀ {a : Bool}, a ≠ true → a = false := by decide
-- #align eq_ff_of_ne_tt with eq_false_of_ne_true

theorem or_comm : ∀ a b, (a || b) = (b || a) := by decide
-- #align bor_comm or_comm

-- #align bor_assoc or_assoc if it's not aligned already

theorem or_left_comm : ∀ a b c, (a || (b || c)) = (b || (a || c)) := by decide
-- all this stuff needs to be aligned

theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]

theorem or_inr {a b : Bool} (H : b) : a || b := by cases a <;> simp [H]

theorem and_comm : ∀ a b, (a && b) = (b && a) := by decide

theorem and_left_comm : ∀ a b c, (a && (b && c)) = (b && (a && c)) := by decide

theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide

theorem and_intro : ∀ {a b : Bool}, a → b → a && b := by decide

theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide

theorem and_or_distrib_left (a b c : Bool) : (a && (b || c)) = (a && b || a && c) := by
  cases a <;> simp

theorem and_or_distrib_right (a b c : Bool) : ((a || b) && c) = (a && c || b && c) := by
  cases a <;> cases b <;> cases c <;> simp

theorem or_and_distrib_left (a b c : Bool) : (a || b && c) = ((a || b) && (a || c)) := by
  cases a <;> simp

theorem or_and_distrib_right (a b c : Bool) : (a && b || c) = ((a || c) && (b || c)) := by
  cases a <;> cases b <;> cases c <;> simp

@[simp]
theorem Not_eq_not : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by decide
-- Lean 3 not_eq_bnot is Lean 4 Not_eq_not

@[simp]
theorem Not_not_eq : ∀ {a b : Bool}, ¬(!a) = b ↔ a = b := by decide

theorem ne_not {a b : Bool} : a ≠ !b ↔ a = b :=
  Not_eq_not

theorem not_ne : ∀ {a b : Bool}, (!a) ≠ b ↔ a = b := Not_not_eq

@[simp]
theorem not_iff_Not : ∀ {b : Bool}, !b ↔ ¬b := by decide

@[simp]
theorem and_not_self : ∀ x, (x && !x) = false := by decide

@[simp]
theorem not_and_self : ∀ x, (!x && x) = false := by decide

@[simp]
theorem or_not_self : ∀ x, (x || !x) = true := by decide

@[simp]
theorem not_or_self : ∀ x, (!x || x) = true := by decide

theorem xor_comm : ∀ a b, xor a b = xor b a := by decide

@[simp]
theorem xor_assoc : ∀ a b c, xor (xor a b) c = xor a (xor b c) := by decide

theorem xor_left_comm : ∀ a b c, xor a (xor b c) = xor b (xor a c) := by decide

@[simp]
theorem xor_not_left : ∀ a, xor (!a) a = true := by decide

@[simp]
theorem xor_not_right : ∀ a, xor a (!a) = true := by decide

@[simp]
theorem xor_not_not : ∀ a b, xor (!a) (!b) = xor a b := by decide

@[simp]
theorem xor_ff_left : ∀ a, xor false a = a := by decide

@[simp]
theorem xor_ff_right : ∀ a, xor a false = a := by decide

theorem and_xor_distrib_left (a b c : Bool) : (a && xor b c) = xor (a && b) (a && c) := by
  cases a <;> simp

theorem and_xor_distrib_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> simp

theorem xor_iff_ne : ∀ {x y : Bool}, xor x y = true ↔ x ≠ y := by decide

/-! ### De Morgan's laws for booleans-/


@[simp]
theorem not_and : ∀ a b : Bool, !(a && b) = (!a || !b) := by decide

@[simp]
theorem not_or : ∀ a b : Bool, !(a || b) = (!a && !b) := by decide

theorem not_inj : ∀ {a b : Bool}, !a = !b → a = b := by decide

-- *TODO* This is horrible
instance : LinearOrder Bool where
  le := fun a b => a = false ∨ b = true
  le_refl := by unfold LE.le; decide
  le_trans := by unfold LE.le; decide
  le_antisymm := by unfold LE.le Preorder.toLE; decide
  le_total := by unfold LE.le Preorder.toLE PartialOrder.toPreorder; decide
  decidable_le := by unfold LE.le Preorder.toLE PartialOrder.toPreorder; exact inferInstance
  decidable_eq := inferInstance
  lt_iff_le_not_le := λ _ _ => Iff.rfl

@[simp]
theorem false_le {x : Bool} : false ≤ x :=
  Or.intro_left _ rfl

@[simp]
theorem le_true {x : Bool} : x ≤ true :=
  Or.intro_right _ rfl

theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide

@[simp]
theorem false_lt_true : false < true :=
  lt_iff.2 ⟨rfl, rfl⟩

theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by decide

theorem and_le_left : ∀ x y : Bool, (x && y) ≤ x := by decide

theorem and_le_right : ∀ x y : Bool, (x && y) ≤ y := by decide

theorem le_and : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by decide

theorem left_le_or : ∀ x y : Bool, x ≤ (x || y) := by decide

theorem right_le_or : ∀ x y : Bool, y ≤ (x || y) := by decide

theorem or_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by decide

/-- convert a `bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def toNat (b : Bool) : Nat :=
  cond b 1 0

/-- convert a `ℕ` to a `bool`, `0 -> false`, everything else -> `true` -/
def ofNat (n : Nat) : Bool :=
  decide (n ≠ 0)

theorem ofNat_le_ofNat {n m : Nat} (h : n ≤ m) : ofNat n ≤ ofNat m := by
  simp only [ofNat, ne_eq, _root_.decide_not];
  cases Nat.decEq n 0 with
  | isTrue hn => rw [decide_eq_true hn]; exact false_le
  | isFalse hn =>
    cases Nat.decEq m 0 with
    | isFalse hm => rw [decide_eq_false hm]; exact le_true
    | isTrue hm => subst hm; have h := le_antisymm h (Nat.zero_le n); contradiction

theorem toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : toNat b₀ ≤ toNat b₁ := by
  cases h with
  | inl h => subst h; exact Nat.zero_le _
  | inr h => subst h; cases b₀ <;> simp;

theorem ofNat_toNat (b : Bool) : ofNat (toNat b) = b := by
  cases b <;> rfl

@[simp]
theorem injective_iff {α : Sort _} {f : Bool → α} : Function.injective f ↔ f false ≠ f true :=
  ⟨fun Hinj Heq => ff_ne_tt (Hinj Heq), fun H x y hxy => by
    cases x <;> cases y
    exacts[rfl, (H hxy).elim, (H hxy.symm).elim, rfl]⟩

/-- **Kaminski's Equation** -/
theorem apply_apply_apply (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x <;> cases h₁ : f true <;> cases h₂ : f false <;> simp only [h₁, h₂]

end Bool

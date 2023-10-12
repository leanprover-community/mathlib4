/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Function

#align_import data.bool.basic from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Booleans

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Tags
bool, boolean, Bool, De Morgan

-/

set_option autoImplicit true

namespace Bool

theorem decide_True {h} : @decide True h = true :=
  decide_eq_true True.intro
#align bool.to_bool_true Bool.decide_True

theorem decide_False {h} : @decide False h = false :=
  decide_eq_false id
#align bool.to_bool_false Bool.decide_False

@[simp]
theorem decide_coe (b : Bool) {h} : @decide b h = b := by
  cases b
  · exact decide_eq_false $ λ j => by cases j
  · exact decide_eq_true $ rfl
#align bool.to_bool_coe Bool.decide_coe

theorem coe_decide (p : Prop) [d : Decidable p] : decide p ↔ p :=
  match d with
  | isTrue hp => ⟨λ _ => hp, λ _ => rfl⟩
  | isFalse hnp => ⟨λ h => Bool.noConfusion h, λ hp => (hnp hp).elim⟩
#align bool.coe_to_bool Bool.coe_decide

theorem of_decide_iff {p : Prop} [Decidable p] : decide p ↔ p :=
  coe_decide p
#align bool.of_to_bool_iff Bool.of_decide_iff

@[simp]
theorem true_eq_decide_iff {p : Prop} [Decidable p] : true = decide p ↔ p :=
  eq_comm.trans of_decide_iff
#align bool.tt_eq_to_bool_iff Bool.true_eq_decide_iff

@[simp]
theorem false_eq_decide_iff {p : Prop} [Decidable p] : false = decide p ↔ ¬p :=
  eq_comm.trans (decide_false_iff _)
#align bool.ff_eq_to_bool_iff Bool.false_eq_decide_iff

theorem decide_not (p : Prop) [Decidable p] : (decide ¬p) = !(decide p) := by
  by_cases p <;> simp [*]
#align bool.to_bool_not Bool.decide_not

@[simp]
theorem decide_and (p q : Prop) [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]
#align bool.to_bool_and Bool.decide_and

@[simp]
theorem decide_or (p q : Prop) [Decidable p] [Decidable q] : decide (p ∨ q) = (p || q) := by
  by_cases p <;> by_cases q <;> simp [*]
#align bool.to_bool_or Bool.decide_or

#align bool.to_bool_eq decide_eq_decide

theorem not_false' : ¬false := fun.
#align bool.not_ff Bool.not_false'

-- Porting note: new theorem
theorem eq_iff_eq_true_iff {a b : Bool} : a = b ↔ ((a = true) ↔ (b = true)) := by
  cases a <;> cases b <;> simp

-- Porting note: new theorem
theorem beq_eq_decide_eq [DecidableEq α]
    (a b : α) : (a == b) = decide (a = b) := rfl

-- Porting note: new theorem
theorem beq_comm [BEq α] [LawfulBEq α] {a b : α} : (a == b) = (b == a) :=
  eq_iff_eq_true_iff.2 (by simp [@eq_comm α])

@[simp]
theorem default_bool : default = false :=
  rfl
#align bool.default_bool Bool.default_bool

theorem dichotomy (b : Bool) : b = false ∨ b = true := by cases b <;> simp
#align bool.dichotomy Bool.dichotomy

@[simp]
theorem forall_bool {p : Bool → Prop} : (∀ b, p b) ↔ p false ∧ p true :=
  ⟨fun h ↦ by simp [h], fun ⟨h₁, h₂⟩ b ↦ by cases b <;> assumption⟩
#align bool.forall_bool Bool.forall_bool

@[simp]
theorem exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  ⟨fun ⟨b, h⟩ ↦ by cases b; exact Or.inl h; exact Or.inr h,
  fun h ↦ match h with
  | .inl h => ⟨_, h⟩
  | .inr h => ⟨_, h⟩ ⟩
#align bool.exists_bool Bool.exists_bool

/-- If `p b` is decidable for all `b : Bool`, then `∀ b, p b` is decidable -/
instance decidableForallBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∀ b, p b) :=
  decidable_of_decidable_of_iff forall_bool.symm
#align bool.decidable_forall_bool Bool.decidableForallBool

/-- If `p b` is decidable for all `b : Bool`, then `∃ b, p b` is decidable -/
instance decidableExistsBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∃ b, p b) :=
  decidable_of_decidable_of_iff exists_bool.symm
#align bool.decidable_exists_bool Bool.decidableExistsBool

theorem cond_eq_ite {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  cases b <;> simp
#align bool.cond_eq_ite Bool.cond_eq_ite

@[simp]
theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  by_cases p <;> simp [*]
#align bool.cond_to_bool Bool.cond_decide

@[simp]
theorem cond_not {α} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by cases b <;> rfl
#align bool.cond_bnot Bool.cond_not

theorem not_ne_id : not ≠ id := fun h ↦ false_ne_true <| congrFun h true
#align bool.bnot_ne_id Bool.not_ne_id

theorem coe_bool_iff : ∀ {a b : Bool}, (a ↔ b) ↔ a = b := by decide
#align bool.coe_bool_iff Bool.coe_bool_iff

theorem eq_true_of_ne_false : ∀ {a : Bool}, a ≠ false → a = true := by decide
#align bool.eq_tt_of_ne_ff Bool.eq_true_of_ne_false

theorem eq_false_of_ne_true : ∀ {a : Bool}, a ≠ true → a = false := by decide
#align bool.eq_ff_of_ne_tt Bool.eq_false_of_ne_true

theorem or_comm : ∀ a b, (a || b) = (b || a) := by decide
#align bool.bor_comm Bool.or_comm

#align bool.bor_assoc Bool.or_assoc

theorem or_left_comm : ∀ a b c, (a || (b || c)) = (b || (a || c)) := by decide
#align bool.bor_left_comm Bool.or_left_comm

theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]
#align bool.bor_inl Bool.or_inl

theorem or_inr {a b : Bool} (H : b) : a || b := by cases a <;> simp [H]
#align bool.bor_inr Bool.or_inr

theorem and_comm : ∀ a b, (a && b) = (b && a) := by decide
#align bool.band_comm Bool.and_comm

#align bool.band_assoc Bool.and_assoc

theorem and_left_comm : ∀ a b c, (a && (b && c)) = (b && (a && c)) := by decide
#align bool.band_left_comm Bool.and_left_comm

theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide
#align bool.band_elim_left Bool.and_elim_left

theorem and_intro : ∀ {a b : Bool}, a → b → a && b := by decide
#align bool.band_intro Bool.and_intro

theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide
#align bool.band_elim_right Bool.and_elim_right

theorem and_or_distrib_left (a b c : Bool) : (a && (b || c)) = (a && b || a && c) := by
  cases a <;> simp
#align bool.band_bor_distrib_left Bool.and_or_distrib_left

theorem and_or_distrib_right (a b c : Bool) : ((a || b) && c) = (a && c || b && c) := by
  cases a <;> cases b <;> cases c <;> simp
#align bool.band_bor_distrib_right Bool.and_or_distrib_right

theorem or_and_distrib_left (a b c : Bool) : (a || b && c) = ((a || b) && (a || c)) := by
  cases a <;> simp
#align bool.bor_band_distrib_left Bool.or_and_distrib_left

theorem or_and_distrib_right (a b c : Bool) : (a && b || c) = ((a || c) && (b || c)) := by
  cases a <;> cases b <;> cases c <;> simp
#align bool.bor_band_distrib_right Bool.or_and_distrib_right

#align bool.bnot_ff Bool.not_false
#align bool.bnot_tt Bool.not_true

lemma eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b := by decide
#align bool.eq_bnot_iff Bool.eq_not_iff

lemma not_eq_iff : ∀ {a b : Bool}, !a = b ↔ a ≠ b := by decide
#align bool.bnot_eq_iff Bool.not_eq_iff

-- Porting note: this is a case where our naming scheme is less than ideal.
-- The two `not`s in this name are different.
-- For now we're going with consistency at the expense of ambiguity.
@[simp]
theorem not_eq_not : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by decide
#align bool.not_eq_bnot Bool.not_eq_not

-- Porting note: and here again.
@[simp]
theorem not_not_eq : ∀ {a b : Bool}, ¬(!a) = b ↔ a = b := by decide
#align bool.bnot_not_eq Bool.not_not_eq

theorem ne_not {a b : Bool} : a ≠ !b ↔ a = b :=
  not_eq_not
#align bool.ne_bnot Bool.ne_not

theorem not_ne : ∀ {a b : Bool}, (!a) ≠ b ↔ a = b := not_not_eq
#align bool.bnot_ne Bool.not_ne

lemma not_ne_self : ∀ b : Bool, (!b) ≠ b := by decide
#align bool.bnot_ne_self Bool.not_ne_self

lemma self_ne_not : ∀ b : Bool, b ≠ !b := by decide
#align bool.self_ne_bnot Bool.self_ne_not

lemma eq_or_eq_not : ∀ a b, a = b ∨ a = !b := by decide
#align bool.eq_or_eq_bnot Bool.eq_or_eq_not

-- Porting note: naming issue again: these two `not` are different.
theorem not_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by simp
#align bool.bnot_iff_not Bool.not_iff_not

theorem eq_true_of_not_eq_false' {a : Bool} : !a = false → a = true := by
  cases a <;> decide
#align bool.eq_tt_of_bnot_eq_ff Bool.eq_true_of_not_eq_false'

theorem eq_false_of_not_eq_true' {a : Bool} : !a = true → a = false := by
  cases a <;> decide
#align bool.eq_ff_of_bnot_eq_tt Bool.eq_false_of_not_eq_true'

@[simp]
theorem and_not_self : ∀ x, (x && !x) = false := by decide
#align bool.band_bnot_self Bool.and_not_self

@[simp]
theorem not_and_self : ∀ x, (!x && x) = false := by decide
#align bool.bnot_band_self Bool.not_and_self

@[simp]
theorem or_not_self : ∀ x, (x || !x) = true := by decide
#align bool.bor_bnot_self Bool.or_not_self

@[simp]
theorem not_or_self : ∀ x, (!x || x) = true := by decide
#align bool.bnot_bor_self Bool.not_or_self

theorem xor_comm : ∀ a b, xor a b = xor b a := by decide
#align bool.bxor_comm Bool.xor_comm

@[simp]
theorem xor_assoc : ∀ a b c, xor (xor a b) c = xor a (xor b c) := by decide
#align bool.bxor_assoc Bool.xor_assoc

theorem xor_left_comm : ∀ a b c, xor a (xor b c) = xor b (xor a c) := by decide
#align bool.bxor_left_comm Bool.xor_left_comm

@[simp]
theorem xor_not_left : ∀ a, xor (!a) a = true := by decide
#align bool.bxor_bnot_left Bool.xor_not_left

@[simp]
theorem xor_not_right : ∀ a, xor a (!a) = true := by decide
#align bool.bxor_bnot_right Bool.xor_not_right

@[simp]
theorem xor_not_not : ∀ a b, xor (!a) (!b) = xor a b := by decide
#align bool.bxor_bnot_bnot Bool.xor_not_not

@[simp]
theorem xor_false_left : ∀ a, xor false a = a := by decide
#align bool.bxor_ff_left Bool.xor_false_left

@[simp]
theorem xor_false_right : ∀ a, xor a false = a := by decide
#align bool.bxor_ff_right Bool.xor_false_right

theorem and_xor_distrib_left (a b c : Bool) : (a && xor b c) = xor (a && b) (a && c) := by
  cases a <;> simp
#align bool.band_bxor_distrib_left Bool.and_xor_distrib_left

theorem and_xor_distrib_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> simp
#align bool.band_bxor_distrib_right Bool.and_xor_distrib_right

theorem xor_iff_ne : ∀ {x y : Bool}, xor x y = true ↔ x ≠ y := by decide
#align bool.bxor_iff_ne Bool.xor_iff_ne

/-! ### De Morgan's laws for booleans-/

@[simp]
theorem not_and : ∀ a b : Bool, (!(a && b)) = (!a || !b) := by decide
#align bool.bnot_band Bool.not_and

@[simp]
theorem not_or : ∀ a b : Bool, (!(a || b)) = (!a && !b) := by decide
#align bool.bnot_bor Bool.not_or

theorem not_inj : ∀ {a b : Bool}, (!a) = !b → a = b := by decide
#align bool.bnot_inj Bool.not_inj

-- Porting note: having to unfold here is not pretty.
-- There is a discussion on zulip about this at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/LinearOrder.20in.20mathlib3.2F4/near/308228493
instance linearOrder : LinearOrder Bool where
  le := fun a b ↦ a = false ∨ b = true
  le_refl := by unfold LE.le; decide
  le_trans := by unfold LE.le; decide
  le_antisymm := by unfold LE.le Preorder.toLE; decide
  le_total := by unfold LE.le Preorder.toLE PartialOrder.toPreorder; decide
  decidableLE := by unfold LE.le Preorder.toLE PartialOrder.toPreorder; exact inferInstance
  decidableEq := inferInstance
  max := or
  max_def := λ a b => by cases a <;> cases b <;> decide
  min := and
  min_def := λ a b => by cases a <;> cases b <;> decide
#align bool.linear_order Bool.linearOrder

@[simp]
theorem false_le {x : Bool} : false ≤ x :=
  Or.intro_left _ rfl
#align bool.ff_le Bool.false_le

@[simp]
theorem le_true {x : Bool} : x ≤ true :=
  Or.intro_right _ rfl
#align bool.le_tt Bool.le_true

theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide
#align bool.lt_iff Bool.lt_iff

@[simp]
theorem false_lt_true : false < true :=
  lt_iff.2 ⟨rfl, rfl⟩
#align bool.ff_lt_tt Bool.false_lt_true

theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by decide
#align bool.le_iff_imp Bool.le_iff_imp

theorem and_le_left : ∀ x y : Bool, (x && y) ≤ x := by decide
#align bool.band_le_left Bool.and_le_left

theorem and_le_right : ∀ x y : Bool, (x && y) ≤ y := by decide
#align bool.band_le_right Bool.and_le_right

theorem le_and : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by decide
#align bool.le_band Bool.le_and

theorem left_le_or : ∀ x y : Bool, x ≤ (x || y) := by decide
#align bool.left_le_bor Bool.left_le_or

theorem right_le_or : ∀ x y : Bool, y ≤ (x || y) := by decide
#align bool.right_le_bor Bool.right_le_or

theorem or_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by decide
#align bool.bor_le Bool.or_le

/-- convert a `Bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def toNat (b : Bool) : Nat :=
  cond b 1 0
#align bool.to_nat Bool.toNat

/-- convert a `ℕ` to a `Bool`, `0 -> false`, everything else -> `true` -/
def ofNat (n : Nat) : Bool :=
  decide (n ≠ 0)
#align bool.of_nat Bool.ofNat

theorem ofNat_le_ofNat {n m : Nat} (h : n ≤ m) : ofNat n ≤ ofNat m := by
  simp only [ofNat, ne_eq, _root_.decide_not]
  cases Nat.decEq n 0 with
  | isTrue hn => rw [decide_eq_true hn]; exact false_le
  | isFalse hn =>
    cases Nat.decEq m 0 with
    | isFalse hm => rw [decide_eq_false hm]; exact le_true
    | isTrue hm => subst hm; have h := le_antisymm h (Nat.zero_le n); contradiction
#align bool.of_nat_le_of_nat Bool.ofNat_le_ofNat

theorem toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : toNat b₀ ≤ toNat b₁ := by
  cases h with
  | inl h => subst h; exact Nat.zero_le _
  | inr h => subst h; cases b₀ <;> simp
#align bool.to_nat_le_to_nat Bool.toNat_le_toNat

theorem ofNat_toNat (b : Bool) : ofNat (toNat b) = b := by
  cases b <;> rfl
#align bool.of_nat_to_nat Bool.ofNat_toNat

@[simp]
theorem injective_iff {α : Sort*} {f : Bool → α} : Function.Injective f ↔ f false ≠ f true :=
  ⟨fun Hinj Heq ↦ false_ne_true (Hinj Heq), fun H x y hxy ↦ by
    cases x <;> cases y
    exacts [rfl, (H hxy).elim, (H hxy.symm).elim, rfl]⟩
#align bool.injective_iff Bool.injective_iff

/-- **Kaminski's Equation** -/
theorem apply_apply_apply (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x <;> cases h₁ : f true <;> cases h₂ : f false <;> simp only [h₁, h₂]
#align bool.apply_apply_apply Bool.apply_apply_apply

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
protected def xor3 (x y c : Bool) :=
  xor (xor x y) c
#align bitvec.xor3 Bool.xor3

/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c
#align bitvec.carry Bool.carry

end Bool

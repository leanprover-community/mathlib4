/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson, Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Tactic.Common
public import Batteries.Tactic.SeqFocus

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(Comm)` `Monoid`s.

## Main definitions

* `semigroupDvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/

@[expose] public section


variable {α : Type*}

section Semigroup

variable [Semigroup α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `CommMonoid`.
This matches the convention for ordinals. -/
instance (priority := 100) semigroupDvd : Dvd α :=
  Dvd.mk fun a b => ∃ c, b = a * c

-- TODO: this used to not have `c` explicit, but that seems to be important
--       for use with tactics, similar to `Exists.intro`
theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
  Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c :=
  h

theorem dvd_def : a ∣ b ↔ ∃ c, b = a * c :=
  Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  Exists.elim H₁ H₂

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[trans]
theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans <| mul_assoc a d e⟩

alias Dvd.dvd.trans := dvd_trans

/-- Transitivity of `|` for use in `calc` blocks. -/
instance : IsTrans α Dvd.dvd :=
  ⟨fun _ _ _ => dvd_trans⟩

@[simp]
theorem dvd_mul_right (a b : α) : a ∣ a * b :=
  Dvd.intro b rfl

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
  h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
  (dvd_mul_right a b).trans h

/-- An element `a` in a semigroup is primal if whenever `a` is a divisor of `b * c`, it can be
factored as the product of a divisor of `b` and a divisor of `c`. -/
def IsPrimal (a : α) : Prop := ∀ ⦃b c⦄, a ∣ b * c → ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂

variable (α) in
/-- A monoid is a decomposition monoid if every element is primal. An integral domain whose
multiplicative monoid is a decomposition monoid, is called a pre-Schreier domain; it is a
Schreier domain if it is moreover integrally closed. -/
@[mk_iff] class DecompositionMonoid : Prop where
  primal (a : α) : IsPrimal a

theorem exists_dvd_and_dvd_of_dvd_mul [DecompositionMonoid α] {b c a : α} (H : a ∣ b * c) :
    ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂ := DecompositionMonoid.primal a H

@[gcongr]
theorem mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

theorem IsLeftRegular.dvd_cancel_left (h : IsLeftRegular a) : a * b ∣ a * c ↔ b ∣ c :=
  ⟨fun dvd ↦ have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

/-- Right divisibility relation. `RightDvd a b` means `a` right-divides `b`,
i.e., `∃ c, b = c * a`. -/
def RightDvd (a b : α) : Prop := ∃ c, b = c * a

@[inherit_doc]
infix:50 " ∣ᵣ " => RightDvd

@[trans]
protected theorem RightDvd.trans : a ∣ᵣ b → b ∣ᵣ c → a ∣ᵣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨e * d, h₁ ▸ h₂.trans <| (mul_assoc e d a).symm⟩

/-- Transitivity of `RightDvd` for use in `calc` blocks. -/
instance : IsTrans α RightDvd :=
  ⟨fun _ _ _ => RightDvd.trans⟩

@[simp]
theorem RightDvd.mul_self (a b : α) : a ∣ᵣ b * a :=
  ⟨b, rfl⟩

theorem RightDvd.mul_left (h : a ∣ᵣ b) (c : α) : a ∣ᵣ c * b :=
  h.trans (RightDvd.mul_self b c)

theorem RightDvd.of_mul_left (h : b * a ∣ᵣ c) : a ∣ᵣ c :=
  (RightDvd.mul_self a b).trans h

@[gcongr]
theorem mul_rightDvd_mul_right (a : α) (h : b ∣ᵣ c) : b * a ∣ᵣ c * a := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

theorem IsRightRegular.rightDvd_cancel_right (h : IsRightRegular a) :
    b * a ∣ᵣ c * a ↔ b ∣ᵣ c :=
  ⟨fun dvd ↦ have ⟨d, eq⟩ := dvd
    ⟨d, h (eq.trans <| (mul_assoc ..).symm)⟩, mul_rightDvd_mul_right a⟩

theorem rightDvd_iff_op_dvd_op : a ∣ᵣ b ↔ MulOpposite.op a ∣ MulOpposite.op b :=
  ⟨fun ⟨c, hc⟩ => ⟨MulOpposite.op c, by simp [hc]⟩,
   fun ⟨c, hc⟩ => ⟨MulOpposite.unop c, by simpa using congrArg MulOpposite.unop hc⟩⟩

end Semigroup

section RightCancelSemigroup

variable [RightCancelSemigroup α] {a b c : α}

@[simp]
theorem mul_rightDvd_mul_iff_right : b * a ∣ᵣ c * a ↔ b ∣ᵣ c :=
  ⟨fun ⟨d, eq⟩ ↦ ⟨d, mul_right_cancel (eq.trans (mul_assoc ..).symm)⟩, mul_rightDvd_mul_right a⟩

end RightCancelSemigroup

section Monoid
variable [Monoid α] {a b c : α} {m n : ℕ}

@[refl, simp]
theorem dvd_refl (a : α) : a ∣ a :=
  Dvd.intro 1 (mul_one a)

theorem dvd_rfl : ∀ {a : α}, a ∣ a := fun {a} => dvd_refl a

instance : @Std.Refl α (· ∣ ·) :=
  ⟨dvd_refl⟩

theorem one_dvd (a : α) : 1 ∣ a :=
  Dvd.intro a (one_mul a)

theorem dvd_of_eq (h : a = b) : a ∣ b := by rw [h]

alias Eq.dvd := dvd_of_eq

@[gcongr]
lemma pow_dvd_pow (a : α) (h : m ≤ n) : a ^ m ∣ a ^ n :=
  ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩

lemma dvd_pow (hab : a ∣ b) : ∀ {n : ℕ} (_ : n ≠ 0), a ∣ b ^ n
  | 0, hn => (hn rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact hab.mul_right _

alias Dvd.dvd.pow := dvd_pow

lemma dvd_pow_self (a : α) {n : ℕ} (hn : n ≠ 0) : a ∣ a ^ n := dvd_rfl.pow hn

@[refl, simp]
protected theorem RightDvd.refl (a : α) : a ∣ᵣ a :=
  ⟨1, (one_mul a).symm⟩

protected theorem RightDvd.rfl {a : α} : a ∣ᵣ a := .refl _

instance : IsPreorder α RightDvd where
  refl := .refl
  trans _ _ _ := .trans

theorem RightDvd.of_eq (h : a = b) : a ∣ᵣ b := by rw [h]

alias Eq.rightDvd := RightDvd.of_eq

end Monoid

section CommSemigroup

variable [CommSemigroup α] {a b c : α}

theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
  Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
  Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))

theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a :=
  ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

@[simp]
theorem dvd_mul_left (a b : α) : a ∣ b * a :=
  Dvd.intro b (mul_comm a b)

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by
  rw [mul_comm]; exact h.mul_right _

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[gcongr]
theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
  | a, _, c, _, ⟨e, rfl⟩, ⟨f, rfl⟩ => ⟨e * f, by simp⟩

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
  Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])

theorem dvd_mul [DecompositionMonoid α] {k m n : α} :
    k ∣ m * n ↔ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  gcongr

@[simp]
theorem rightDvd_iff_dvd : a ∣ᵣ b ↔ a ∣ b :=
  exists_congr fun c ↦ by rw [mul_comm]

end CommSemigroup

section CommMonoid

variable [CommMonoid α] {a b : α}

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c := by
  gcongr

theorem pow_dvd_pow_of_dvd (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n := by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ, pow_succ]
    gcongr

@[gcongr]
lemma pow_dvd_pow_of_dvd_of_le {m n : ℕ} (hab : a ∣ b) (hmn : m ≤ n) : a ^ m ∣ b ^ n := by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

end CommMonoid

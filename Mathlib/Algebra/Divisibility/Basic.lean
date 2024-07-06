/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Common

#align_import algebra.divisibility.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

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


variable {α : Type*}

section Semigroup

variable [Semigroup α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `CommMonoid`.
    This matches the convention for ordinals. -/
instance (priority := 100) semigroupDvd : Dvd α :=
  Dvd.mk fun a b => ∃ c, b = a * c
#align semigroup_has_dvd semigroupDvd

-- TODO: this used to not have `c` explicit, but that seems to be important
--       for use with tactics, similar to `Exists.intro`
theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
  Exists.intro c h.symm
#align dvd.intro Dvd.intro

alias dvd_of_mul_right_eq := Dvd.intro
#align dvd_of_mul_right_eq dvd_of_mul_right_eq

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c :=
  h
#align exists_eq_mul_right_of_dvd exists_eq_mul_right_of_dvd

theorem dvd_def : a ∣ b ↔ ∃ c, b = a * c :=
  Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  Exists.elim H₁ H₂
#align dvd.elim Dvd.elim

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[trans]
theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans <| mul_assoc a d e⟩
#align dvd_trans dvd_trans

alias Dvd.dvd.trans := dvd_trans

/-- Transitivity of `|` for use in `calc` blocks. -/
instance : IsTrans α Dvd.dvd :=
  ⟨fun _ _ _ => dvd_trans⟩

@[simp]
theorem dvd_mul_right (a b : α) : a ∣ a * b :=
  Dvd.intro b rfl
#align dvd_mul_right dvd_mul_right

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
  h.trans (dvd_mul_right b c)
#align dvd_mul_of_dvd_left dvd_mul_of_dvd_left

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
  (dvd_mul_right a b).trans h
#align dvd_of_mul_right_dvd dvd_of_mul_right_dvd

section map_dvd

variable {M N : Type*}

theorem map_dvd [Semigroup M] [Semigroup N] {F : Type*} [FunLike F M N] [MulHomClass F M N]
    (f : F) {a b} : a ∣ b → f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩
#align map_dvd map_dvd

theorem MulHom.map_dvd [Semigroup M] [Semigroup N] (f : M →ₙ* N) {a b} : a ∣ b → f a ∣ f b :=
  _root_.map_dvd f
#align mul_hom.map_dvd MulHom.map_dvd

theorem MonoidHom.map_dvd [Monoid M] [Monoid N] (f : M →* N) {a b} : a ∣ b → f a ∣ f b :=
  _root_.map_dvd f
#align monoid_hom.map_dvd MonoidHom.map_dvd

end map_dvd

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
#align exists_dvd_and_dvd_of_dvd_mul exists_dvd_and_dvd_of_dvd_mul

end Semigroup

section Monoid
variable [Monoid α] {a b c : α} {m n : ℕ}

@[refl, simp]
theorem dvd_refl (a : α) : a ∣ a :=
  Dvd.intro 1 (mul_one a)
#align dvd_refl dvd_refl

theorem dvd_rfl : ∀ {a : α}, a ∣ a := fun {a} => dvd_refl a
#align dvd_rfl dvd_rfl

instance : IsRefl α (· ∣ ·) :=
  ⟨dvd_refl⟩

theorem one_dvd (a : α) : 1 ∣ a :=
  Dvd.intro a (one_mul a)
#align one_dvd one_dvd

theorem dvd_of_eq (h : a = b) : a ∣ b := by rw [h]
#align dvd_of_eq dvd_of_eq

alias Eq.dvd := dvd_of_eq
#align eq.dvd Eq.dvd

lemma pow_dvd_pow (a : α) (h : m ≤ n) : a ^ m ∣ a ^ n :=
  ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩
#align pow_dvd_pow pow_dvd_pow

lemma dvd_pow (hab : a ∣ b) : ∀ {n : ℕ} (_ : n ≠ 0), a ∣ b ^ n
  | 0,     hn => (hn rfl).elim
  | n + 1, _  => by rw [pow_succ']; exact hab.mul_right _
#align dvd_pow dvd_pow

alias Dvd.dvd.pow := dvd_pow

lemma dvd_pow_self (a : α) {n : ℕ} (hn : n ≠ 0) : a ∣ a ^ n := dvd_rfl.pow hn
#align dvd_pow_self dvd_pow_self

theorem mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]
#align mul_dvd_mul_left mul_dvd_mul_left

end Monoid

section CommSemigroup

variable [CommSemigroup α] {a b c : α}

theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
  Dvd.intro _ (by rw [mul_comm] at h; apply h)
#align dvd.intro_left Dvd.intro_left

alias dvd_of_mul_left_eq := Dvd.intro_left
#align dvd_of_mul_left_eq dvd_of_mul_left_eq

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
  Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))
#align exists_eq_mul_left_of_dvd exists_eq_mul_left_of_dvd

theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a :=
  ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩
#align dvd_iff_exists_eq_mul_left dvd_iff_exists_eq_mul_left

theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃
#align dvd.elim_left Dvd.elim_left

@[simp]
theorem dvd_mul_left (a b : α) : a ∣ b * a :=
  Dvd.intro b (mul_comm a b)
#align dvd_mul_left dvd_mul_left

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by
  rw [mul_comm]; exact h.mul_right _
#align dvd_mul_of_dvd_right dvd_mul_of_dvd_right

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

attribute [local simp] mul_assoc mul_comm mul_left_comm

theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
  | a, _, c, _, ⟨e, rfl⟩, ⟨f, rfl⟩ => ⟨e * f, by simp⟩
#align mul_dvd_mul mul_dvd_mul

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
  Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])
#align dvd_of_mul_left_dvd dvd_of_mul_left_dvd

theorem dvd_mul [DecompositionMonoid α] {k m n : α} :
    k ∣ m * n ↔ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  exact mul_dvd_mul hy hz
#align dvd_mul dvd_mul

end CommSemigroup

section CommMonoid

variable [CommMonoid α] {a b : α}

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
  mul_dvd_mul h (dvd_refl c)
#align mul_dvd_mul_right mul_dvd_mul_right

theorem pow_dvd_pow_of_dvd (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
  | 0 => by rw [pow_zero, pow_zero]
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd h n) h
#align pow_dvd_pow_of_dvd pow_dvd_pow_of_dvd

end CommMonoid

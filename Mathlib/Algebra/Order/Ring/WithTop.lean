/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Canonical

/-! # Structures involving `*` and `0` on `with_top` and `with_bot`
The main results of this section are `with_top.canonically_ordered_comm_semiring` and
`with_bot.comm_monoid_with_zero`.
-/


variable {α : Type _}

namespace WithTop

instance [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithTop α) where
  zero := 0
  mul m n := if m = 0 ∨ n = 0 then 0 else m.bind fun a => n.bind fun b => ↑(a * b)
  zero_mul a := if_pos <| Or.inl rfl
  mul_zero a := if_pos <| Or.inr rfl

theorem mul_def {a b : WithTop α} :
    a * b = if a = 0 ∨ b = 0 then 0 else a.bind fun a => b.bind fun b => ↑(a * b) :=
  rfl
#align with_top.mul_def WithTop.mul_def

@[simp]
theorem mul_top {a : WithTop α} (h : a ≠ 0) : a * ⊤ = ⊤ := by cases a <;> simp [mul_def, h] <;> rfl
#align with_top.mul_top WithTop.mul_top

@[simp]
theorem top_mul {a : WithTop α} (h : a ≠ 0) : ⊤ * a = ⊤ := by cases a <;> simp [mul_def, h] <;> rfl
#align with_top.top_mul WithTop.top_mul

@[simp]
theorem top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ :=
  top_mul top_ne_zero
#align with_top.top_mul_top WithTop.top_mul_top

end Mul

section MulZeroClass

variable [MulZeroClass α]

@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithTop α) = a * b :=
  (Decidable.byCases fun this : a = 0 => by simp [this]) fun ha =>
    (Decidable.byCases fun this : b = 0 => by simp [this]) fun hb => by
      simp [*, mul_def]
      rfl
#align with_top.coe_mul WithTop.coe_mul

theorem mul_coe {b : α} (hb : b ≠ 0) : ∀ {a : WithTop α}, a * b = a.bind fun a : α => ↑(a * b)
  | none =>
    show (if (⊤ : WithTop α) = 0 ∨ (b : WithTop α) = 0 then 0 else ⊤ : WithTop α) = ⊤ by simp [hb]
  | some a => show ↑a * ↑b = ↑(a * b) from coe_mul.symm
#align with_top.mul_coe WithTop.mul_coe

@[simp]
theorem mul_eq_top_iff {a b : WithTop α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by
  cases a <;> cases b <;> simp only [none_eq_top, some_eq_coe]
  · simp [← coe_mul]
  · by_cases hb : b = 0 <;> simp [hb]
  · by_cases ha : a = 0 <;> simp [ha]
  · simp [← coe_mul]
#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iff

theorem mul_lt_top [Preorder α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ := by
  lift a to α using ha
  lift b to α using hb
  simp only [← coe_mul, coe_lt_top]
#align with_top.mul_lt_top WithTop.mul_lt_top

@[simp]
theorem untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
  induction a using WithTop.recTopCoe; · rw [top_mul hb, untop'_top, zero_mul]
  induction b using WithTop.recTopCoe; · rw [mul_top ha, untop'_top, mul_zero]
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
#align with_top.untop'_zero_mul WithTop.untop'_zero_mul

end MulZeroClass

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) :=
  { WithTop.mulZeroClass with mul := (· * ·), one := 1, zero := 0,
    one_mul := fun a =>
      match a with
      | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, one_mul],
    mul_one := fun a =>
      match a with
      | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, mul_one] }

/-- A version of `with_top.map` for `monoid_with_zero_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def MonoidWithZeroHom.withTopMap {R S : Type _} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.with_top_map, f.toMonoidHom.toOneHom.with_top_map with toFun := WithTop.map f,
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.to_zero_hom.with_top_map.map_zero
      rcases eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases eq_or_ne y 0 with (rfl | hy)
      · simp
      induction x using WithTop.recTopCoe
      · simp [hy, this]
      induction y using WithTop.recTopCoe
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [hx, this]
      simp [← coe_mul] }
#align monoid_with_zero_hom.with_top_map MonoidWithZeroHom.withTopMap

instance [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithTop α) :=
  ⟨fun a b => by
    cases a <;> cases b <;> dsimp [mul_def] <;> split_ifs <;>
      simp_all [none_eq_top, some_eq_coe, mul_eq_zero]⟩

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithTop α) :=
  { WithTop.mulZeroClass with mul := (· * ·), zero := 0,
    mul_assoc := fun a b c => by
      rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
      rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
      rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
      induction a using WithTop.recTopCoe; · simp [hb, hc]
      induction b using WithTop.recTopCoe; · simp [ha, hc]
      induction c using WithTop.recTopCoe; · simp [ha, hb]
      simp only [← coe_mul, mul_assoc] }

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithTop α) :=
  { WithTop.mulZeroOneClass, WithTop.semigroupWithZero with }

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) :=
  { WithTop.monoidWithZero with mul := (· * ·), zero := 0,
    mul_comm := fun a b => by simp only [or_comm', mul_def, Option.bind_comm a b, mul_comm] }

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c := by
  induction c using WithTop.recTopCoe
  · by_cases ha : a = 0 <;> simp [ha]
  · by_cases hc : c = 0
    · simp [hc]
    simp [mul_coe hc]
    cases a <;> cases b
    repeat' first |rfl|exact congr_arg some (add_mul _ _ _)
#align with_top.distrib' with_top.distrib'

/-- This instance requires `canonically_ordered_comm_semiring` as it is the smallest class
that derives from both `non_assoc_non_unital_semiring` and `canonically_ordered_add_monoid`, both
of which are required for distributivity. -/
instance [Nontrivial α] : CommSemiring (WithTop α) :=
  { WithTop.addCommMonoidWithOne, WithTop.commMonoidWithZero with right_distrib := distrib',
    left_distrib := fun a b c => by
      rw [mul_comm, distrib', mul_comm b, mul_comm c]
      rfl }

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddMonoid, WithTop.no_zero_divisors with }

/-- A version of `with_top.map` for `ring_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def RingHom.withTopMap {R S : Type _} [CanonicallyOrderedCommSemiring R] [DecidableEq R]
    [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  { f.toMonoidWithZeroHom.with_top_map hf, f.toAddMonoidHom.with_top_map with
    toFun := WithTop.map f }
#align ring_hom.with_top_map RingHom.withTopMap

end WithTop

namespace WithBot

instance [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithBot α) :=
  WithTop.mulZeroClass

theorem mul_def {a b : WithBot α} :
    a * b = if a = 0 ∨ b = 0 then 0 else a.bind fun a => b.bind fun b => ↑(a * b) :=
  rfl
#align with_bot.mul_def WithBot.mul_def

@[simp]
theorem mul_bot {a : WithBot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
  WithTop.mul_top h
#align with_bot.mul_bot WithBot.mul_bot

@[simp]
theorem bot_mul {a : WithBot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
  WithTop.top_mul h
#align with_bot.bot_mul WithBot.bot_mul

@[simp]
theorem bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ :=
  WithTop.top_mul_top
#align with_bot.bot_mul_bot WithBot.bot_mul_bot

end Mul

section MulZeroClass

variable [MulZeroClass α]

@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithBot α) = a * b :=
  (Decidable.byCases fun this : a = 0 => by simp [this]) fun ha =>
    (Decidable.byCases fun this : b = 0 => by simp [this]) fun hb => by
      simp [*, mul_def]
      rfl
#align with_bot.coe_mul WithBot.coe_mul

theorem mul_coe {b : α} (hb : b ≠ 0) {a : WithBot α} : a * b = a.bind fun a : α => ↑(a * b) :=
  WithTop.mul_coe hb
#align with_bot.mul_coe WithBot.mul_coe

@[simp]
theorem mul_eq_bot_iff {a b : WithBot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iff

theorem bot_lt_mul [Preorder α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b := by
  lift a to α using ne_bot_of_gt ha
  lift b to α using ne_bot_of_gt hb
  simp only [← coe_mul, bot_lt_coe]
#align with_bot.bot_lt_mul WithBot.bot_lt_mul

end MulZeroClass

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  WithTop.mulZeroOneClass

instance [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.no_zero_divisors

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithBot α) :=
  WithTop.semigroupWithZero

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithBot α) :=
  WithTop.monoidWithZero

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  WithTop.commMonoidWithZero

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : CommSemiring (WithBot α) :=
  WithTop.commSemiring

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : PosMulMono (WithBot α) :=
  posMulMono_iff_covariant_pos.2
    ⟨by
      rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
      lift x to α using x0.ne_bot
      induction a using WithBot.recBotCoe; · simp_rw [mul_bot x0.ne.symm, bot_le]
      induction b using WithBot.recBotCoe; · exact absurd h (bot_lt_coe a).not_le
      simp only [← coe_mul, coe_le_coe] at *
      exact mul_le_mul_left' h x⟩

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : MulPosMono (WithBot α) :=
  posMulMono_iff_mulPosMono.mp inferInstance

end WithBot

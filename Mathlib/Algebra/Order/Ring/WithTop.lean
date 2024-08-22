/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.MonoidWithZero.WithTop
import Mathlib.Algebra.Order.Ring.Canonical

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.canonicallyOrderedCommSemiring` and
`WithBot.orderedCommSemiring`.
-/

variable {α : Type*}

namespace WithTop

variable [DecidableEq α] [CanonicallyOrderedCommSemiring α]

/-- This instance requires `CanonicallyOrderedCommSemiring` as it is the smallest class
that derives from both `NonAssocNonUnitalSemiring` and `CanonicallyOrderedAddCommMonoid`, both
of which are required for distributivity. -/
instance commSemiring [Nontrivial α] : CommSemiring (WithTop α) :=
  WithTop.commSemiringOfAddEqZero add_eq_zero.mp

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddCommMonoid with
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero}

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps (config := .asFn)]
protected def _root_.RingHom.withTopMap {R S : Type*} [CanonicallyOrderedCommSemiring R]
    [DecidableEq R] [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  {MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with}

end WithTop

namespace WithBot

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithBot α}

instance : MulZeroClass (WithBot α) := WithTop.instMulZeroClass

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithBot α) = a * b := rfl

lemma mul_bot' : ∀ (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm

@[simp] lemma mul_bot (h : a ≠ 0) : a * ⊥ = ⊥ := by rw [mul_bot', if_neg h]

lemma bot_mul' : ∀ (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm

@[simp] lemma bot_mul (hb : b ≠ 0) : ⊥ * b = ⊥ := by rw [bot_mul', if_neg hb]

@[simp] lemma bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ := rfl

lemma mul_def (a b : WithBot α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithBot.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

lemma mul_eq_bot_iff : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 := by rw [mul_def]; aesop

lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithBot α) = a.bind fun a ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, hb, not_false_eq_true, bot_mul]; rfl
  | (a : α) => rfl

lemma coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithBot α) = b.bind fun b ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, ha, not_false_eq_true, mul_bot]; rfl
  | (b : α) => rfl

@[simp]
lemma unbot'_zero_mul (a b : WithBot α) : (a * b).unbot' 0 = a.unbot' 0 * b.unbot' 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbot'_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbot'_coe, mul_zero]
  induction a; · rw [bot_mul hb, unbot'_bot, zero_mul]
  induction b; · rw [mul_bot ha, unbot'_bot, mul_zero]
  rw [← coe_mul, unbot'_coe, unbot'_coe, unbot'_coe]

theorem bot_lt_mul' [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  WithTop.mul_lt_top' (α := αᵒᵈ) ha hb

theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : ⊥ < a * b :=
  WithTop.mul_lt_top (α := αᵒᵈ) ha hb

instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.instNoZeroDivisors

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  WithTop.instMulZeroOneClass

instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithBot α) := WithTop.instSemigroupWithZero

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]

instance instMonoidWithZero : MonoidWithZero (WithBot α) := WithTop.instMonoidWithZero

@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithBot α) = a ^ n := rfl

end MonoidWithZero

instance commMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) := WithTop.instCommMonoidWithZero

instance commSemiring [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    CommSemiring (WithBot α) :=
  WithTop.commSemiring

instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk]
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction a
    · simp_rw [mul_bot x0', bot_le]
    induction b
    · exact absurd h (bot_lt_coe _).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_left h x0 ⟩

instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk]
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction a
    · simp_rw [bot_mul x0', bot_le]
    induction b
    · exact absurd h (bot_lt_coe _).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_right h x0 ⟩

instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk]
    lift x to α using x0.ne_bot
    induction b
    · exact absurd h not_lt_bot
    induction a
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_left h x0 ⟩

instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk]
    lift x to α using x0.ne_bot
    induction b
    · exact absurd h not_lt_bot
    induction a
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_right h x0 ⟩

instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk] at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction b
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_lt
    induction a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_left h x0 ⟩

instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk] at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction b
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_lt
    induction a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_right h x0 ⟩

instance [MulZeroClass α] [Preorder α] [PosMulReflectLE α] : PosMulReflectLE (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk] at h
    lift x to α using x0.ne_bot
    induction a
    · exact bot_le
    induction b
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_left h x0 ⟩

instance [MulZeroClass α] [Preorder α] [MulPosReflectLE α] : MulPosReflectLE (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk] at h
    lift x to α using x0.ne_bot
    induction a
    · exact bot_le
    induction b
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_right h x0 ⟩

instance orderedCommSemiring [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    OrderedCommSemiring (WithBot α) :=
  { WithBot.zeroLEOneClass, WithBot.orderedAddCommMonoid, WithBot.commSemiring with
    mul_le_mul_of_nonneg_left  := fun _ _ _ => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun _ _ _ => mul_le_mul_of_nonneg_right }

end WithBot

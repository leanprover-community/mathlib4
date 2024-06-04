/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Ring.Hom.Defs
import Batteries.Data.Option.Lemmas

#align_import algebra.order.ring.with_top from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.canonicallyOrderedCommSemiring` and
`WithBot.orderedCommSemiring`.
-/

variable {α : Type*}

namespace WithTop

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithTop α}

instance instMulZeroClass : MulZeroClass (WithTop α) where
  zero := 0
  mul a b := match a, b with
    | (a : α), (b : α) => ↑(a * b)
    | (a : α), ⊤ => if a = 0 then 0 else ⊤
    | ⊤, (b : α) => if b = 0 then 0 else ⊤
    | ⊤, ⊤ => ⊤
  mul_zero a := match a with
    | (a : α) => congr_arg some $ mul_zero _
    | ⊤ => if_pos rfl
  zero_mul b := match b with
    | (b : α) => congr_arg some $ zero_mul _
    | ⊤ => if_pos rfl

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithTop α) = a * b := rfl
#align with_top.coe_mul WithTop.coe_mul

lemma mul_top' : ∀ (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm
#align with_top.mul_top' WithTop.mul_top'

@[simp] lemma mul_top (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]
#align with_top.mul_top WithTop.mul_top

lemma top_mul' : ∀ (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm
#align with_top.top_mul' WithTop.top_mul'

@[simp] lemma top_mul (hb : b ≠ 0) : ⊤ * b = ⊤ := by rw [top_mul', if_neg hb]
#align with_top.top_mul WithTop.top_mul

-- eligible for dsimp
@[simp, nolint simpNF] lemma top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := rfl
#align with_top.top_mul_top WithTop.top_mul_top

lemma mul_def (a b : WithTop α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop
#align with_top.mul_def WithTop.mul_def

lemma mul_eq_top_iff : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by rw [mul_def]; aesop
#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iff

lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithTop α) = a.bind fun a ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, hb]; rfl
  | (a : α) => rfl
#align with_top.mul_coe WithTop.mul_coe_eq_bind

lemma coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithTop α) = b.bind fun b ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, ha]; rfl
  | (b : α) => rfl

@[simp] lemma untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
  induction a; · rw [top_mul hb, untop'_top, zero_mul]
  induction b; · rw [mul_top ha, untop'_top, mul_zero]
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
#align with_top.untop'_zero_mul WithTop.untop'_zero_mul

theorem mul_lt_top' [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  simp only [Ne, mul_eq_top_iff, *, and_false, false_and, or_self, not_false_eq_true]
#align with_top.mul_lt_top' WithTop.mul_lt_top'

theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
  mul_lt_top' (WithTop.lt_top_iff_ne_top.2 ha) (WithTop.lt_top_iff_ne_top.2 hb)
#align with_top.mul_lt_top WithTop.mul_lt_top

instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α) := by
  refine ⟨fun h₁ => Decidable.by_contradiction fun h₂ => ?_⟩
  rw [mul_def, if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) where
  __ := instMulZeroClass
  one_mul a := match a with
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one a := match a with
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps (config := .asFn)]
protected def _root_.MonoidWithZeroHom.withTopMap {R S : Type*} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction' x with x
      · simp [hy, this]
      induction' y with y
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      · -- Porting note (#11215): TODO: `simp [← coe_mul]` times out
        simp only [map_coe, ← coe_mul, map_mul] }
#align monoid_with_zero_hom.with_top_map MonoidWithZeroHom.withTopMap

instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithTop α) where
  __ := instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
  -- Porting note: below needed to be rewritten due to changed `simp` behaviour for `coe`
    induction' a with a; · simp [hb, hc]
    induction' b with b; · simp [mul_top ha, top_mul hc]
    induction' c with c
    · rw [mul_top hb, mul_top ha]
      rw [← coe_zero, ne_eq, coe_eq_coe] at ha hb
      simp [ha, hb]
    simp only [← coe_mul, mul_assoc]

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]

instance instMonoidWithZero : MonoidWithZero (WithTop α) where
  __ := instMulZeroOneClass
  __ := instSemigroupWithZero
  npow n a := match a, n with
    | (a : α), n => ↑(a ^ n)
    | ⊤, 0 => 1
    | ⊤, _n + 1 => ⊤
  npow_zero a := by cases a <;> simp
  npow_succ n a := by cases n <;> cases a <;> simp [pow_succ]

@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithTop α) = a ^ n := rfl

end MonoidWithZero

instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) where
  __ := instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c := by
  induction' c with c
  · by_cases ha : a = 0 <;> simp [ha]
  · by_cases hc : c = 0
    · simp [hc]
    simp only [mul_coe_eq_bind hc]
    cases a <;> cases b
    repeat' first | rfl |exact congr_arg some (add_mul _ _ _)

/-- This instance requires `CanonicallyOrderedCommSemiring` as it is the smallest class
that derives from both `NonAssocNonUnitalSemiring` and `CanonicallyOrderedAddCommMonoid`, both
of which are required for distributivity. -/
instance commSemiring [Nontrivial α] : CommSemiring (WithTop α) :=
  { addCommMonoidWithOne, instCommMonoidWithZero with
    right_distrib := distrib'
    left_distrib := fun a b c => by
      rw [mul_comm, distrib', mul_comm b, mul_comm c] }

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddCommMonoid with
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero}

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps (config := .asFn)]
protected def _root_.RingHom.withTopMap {R S : Type*} [CanonicallyOrderedCommSemiring R]
    [DecidableEq R] [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  {MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with}
#align ring_hom.with_top_map RingHom.withTopMap

end WithTop

namespace WithBot

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithBot α}

instance : MulZeroClass (WithBot α) := WithTop.instMulZeroClass

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithBot α) = a * b := rfl
#align with_bot.coe_mul WithBot.coe_mul

lemma mul_bot' : ∀ (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm
#align with_bot.mul_bot' WithBot.mul_bot'

@[simp] lemma mul_bot (h : a ≠ 0) : a * ⊥ = ⊥ := by rw [mul_bot', if_neg h]
#align with_bot.mul_bot WithBot.mul_bot

lemma bot_mul' : ∀ (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm
#align with_bot.bot_mul' WithBot.bot_mul'

@[simp] lemma bot_mul (hb : b ≠ 0) : ⊥ * b = ⊥ := by rw [bot_mul', if_neg hb]
#align with_bot.bot_mul WithBot.bot_mul

-- eligible for dsimp
@[simp, nolint simpNF] lemma bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ := rfl
#align with_bot.bot_mul_bot WithBot.bot_mul_bot

lemma mul_def (a b : WithBot α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithBot.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop
#align with_bot.mul_def WithBot.mul_def

lemma mul_eq_bot_iff : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 := by rw [mul_def]; aesop
#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iff

lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithBot α) = a.bind fun a ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, hb, not_false_eq_true, bot_mul]; rfl
  | (a : α) => rfl
#align with_bot.mul_coe WithBot.mul_coe_eq_bind

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
#align with_bot.unbot'_zero_mul WithBot.unbot'_zero_mul

theorem bot_lt_mul' [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  WithTop.mul_lt_top' (α := αᵒᵈ) ha hb
#align with_bot.bot_lt_mul' WithBot.bot_lt_mul'

theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : ⊥ < a * b :=
  WithTop.mul_lt_top (α := αᵒᵈ) ha hb
#align with_bot.bot_lt_mul WithBot.bot_lt_mul

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

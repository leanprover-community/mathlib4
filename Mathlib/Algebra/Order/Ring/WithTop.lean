/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Canonical
import Std.Data.Option.Lemmas

#align_import algebra.order.ring.with_top from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.canonicallyOrderedCommSemiring` and
`WithBot.orderedCommSemiring`.
-/

variable {α : Type*}

namespace WithTop

variable [DecidableEq α]

instance : DecidableEq (WithTop α) := instDecidableEqOption

section Mul

variable [Zero α] [Mul α]

instance instMulZeroClassWithTop : MulZeroClass (WithTop α) where
  zero := 0
  mul m n := if m = 0 ∨ n = 0 then 0 else Option.map₂ (· * ·) m n
  zero_mul _ := if_pos <| Or.inl rfl
  mul_zero _ := if_pos <| Or.inr rfl

theorem mul_def {a b : WithTop α} :
    a * b = (if a = 0 ∨ b = 0 then 0 else Option.map₂ (· * ·) a b : WithTop α) :=
  rfl
#align with_top.mul_def WithTop.mul_def

-- Porting note: commented out @[simp] to placate the `simp can prove this` linter
-- @[simp]
theorem top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := by simp [mul_def]; rfl
                                                    -- ⊢ Option.map₂ (fun x x_1 => x * x_1) ⊤ ⊤ = ⊤
                                                                    -- 🎉 no goals
#align with_top.top_mul_top WithTop.top_mul_top

theorem mul_top' (a : WithTop α) : a * ⊤ = if a = 0 then 0 else ⊤ := by
  induction a using recTopCoe <;> simp [mul_def] <;> rfl
  -- ⊢ ⊤ * ⊤ = if ⊤ = 0 then 0 else ⊤
                                  -- ⊢ Option.map₂ (fun x x_1 => x * x_1) ⊤ ⊤ = ⊤
                                  -- ⊢ (if a✝ = 0 then 0 else Option.map₂ (fun x x_1 => x * x_1) ↑a✝ ⊤) = if a✝ = 0 …
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
#align with_top.mul_top' WithTop.mul_top'

@[simp] theorem mul_top {a : WithTop α} (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]
                                                                      -- 🎉 no goals
#align with_top.mul_top WithTop.mul_top

theorem top_mul' (a : WithTop α) : ⊤ * a = if a = 0 then 0 else ⊤ := by
  induction a using recTopCoe <;> simp [mul_def] <;> rfl
  -- ⊢ ⊤ * ⊤ = if ⊤ = 0 then 0 else ⊤
                                  -- ⊢ Option.map₂ (fun x x_1 => x * x_1) ⊤ ⊤ = ⊤
                                  -- ⊢ (if a✝ = 0 then 0 else Option.map₂ (fun x x_1 => x * x_1) ⊤ ↑a✝) = if a✝ = 0 …
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
#align with_top.top_mul' WithTop.top_mul'

@[simp] theorem top_mul {a : WithTop α} (h : a ≠ 0) : ⊤ * a = ⊤ := by rw [top_mul', if_neg h]
                                                                      -- 🎉 no goals
#align with_top.top_mul WithTop.top_mul

theorem mul_eq_top_iff {a b : WithTop α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by
  rw [mul_def, ite_eq_iff, ← none_eq_top, Option.map₂_eq_none_iff]
  -- ⊢ (a = 0 ∨ b = 0) ∧ 0 = none ∨ ¬(a = 0 ∨ b = 0) ∧ (a = none ∨ b = none) ↔ a ≠  …
  have ha : a = 0 → a ≠ none := fun h => h.symm ▸ zero_ne_top
  -- ⊢ (a = 0 ∨ b = 0) ∧ 0 = none ∨ ¬(a = 0 ∨ b = 0) ∧ (a = none ∨ b = none) ↔ a ≠  …
  have hb : b = 0 → b ≠ none := fun h => h.symm ▸ zero_ne_top
  -- ⊢ (a = 0 ∨ b = 0) ∧ 0 = none ∨ ¬(a = 0 ∨ b = 0) ∧ (a = none ∨ b = none) ↔ a ≠  …
  tauto
  -- 🎉 no goals
#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iff

theorem mul_lt_top' [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  -- ⊢ a * b ≠ ⊤
  simp only [Ne.def, mul_eq_top_iff, *, and_false, false_and, false_or]
  -- 🎉 no goals
#align with_top.mul_lt_top' WithTop.mul_lt_top'

theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
  mul_lt_top' (WithTop.lt_top_iff_ne_top.2 ha) (WithTop.lt_top_iff_ne_top.2 hb)
#align with_top.mul_lt_top WithTop.mul_lt_top

instance noZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α) := by
  refine ⟨fun h₁ => Decidable.by_contradiction <| fun h₂ => ?_⟩
  -- ⊢ False
  rw [mul_def, if_neg h₂] at h₁
  -- ⊢ False
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  -- ⊢ False
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))
  -- 🎉 no goals

end Mul

section MulZeroClass

variable [MulZeroClass α]

@[simp, norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithTop α) = a * b := by
  by_cases ha : a = 0
  -- ⊢ ↑(a * b) = ↑a * ↑b
  · simp [ha]
    -- 🎉 no goals
  · by_cases hb : b = 0
    -- ⊢ ↑(a * b) = ↑a * ↑b
    · simp [hb]
      -- 🎉 no goals
    · simp [*, mul_def]
      -- ⊢ ↑(a * b) = Option.map₂ (fun x x_1 => x * x_1) ↑a ↑b
      rfl
      -- 🎉 no goals
#align with_top.coe_mul WithTop.coe_mul

theorem mul_coe {b : α} (hb : b ≠ 0) : ∀ {a : WithTop α},
    a * (b : WithTop α) = a.bind fun a : α => ↑(a * b)
  | none =>
    show (if (⊤ : WithTop α) = 0 ∨ (b : WithTop α) = 0 then 0 else ⊤ : WithTop α) = ⊤ by simp [hb]
                                                                                         -- 🎉 no goals
  | Option.some a => by
    rw [some_eq_coe, ← coe_mul]
    -- ⊢ ↑(a * b) = Option.bind ↑a fun a => Option.some (a * b)
    rfl
    -- 🎉 no goals
#align with_top.mul_coe WithTop.mul_coe

@[simp]
theorem untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
  -- ⊢ untop' 0 (a * b) = untop' 0 a * untop' 0 b
                         -- 🎉 no goals
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
  -- ⊢ untop' 0 (a * b) = untop' 0 a * untop' 0 b
                         -- 🎉 no goals
  induction a using WithTop.recTopCoe; · rw [top_mul hb, untop'_top, zero_mul]
  -- ⊢ untop' 0 (⊤ * b) = untop' 0 ⊤ * untop' 0 b
                                         -- 🎉 no goals
  induction b using WithTop.recTopCoe; · rw [mul_top ha, untop'_top, mul_zero]
  -- ⊢ untop' 0 (↑a✝ * ⊤) = untop' 0 ↑a✝ * untop' 0 ⊤
                                         -- 🎉 no goals
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
  -- 🎉 no goals
#align with_top.untop'_zero_mul WithTop.untop'_zero_mul

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance instMulZeroOneClassWithTop [MulZeroOneClass α] [Nontrivial α] :
    MulZeroOneClass (WithTop α) :=
  { WithTop.instMulZeroClassWithTop with
    mul := (· * ·)
    one := 1, zero := 0
    one_mul := fun a =>
      match a with
      | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, one_mul],
                      -- 🎉 no goals
    mul_one := fun a =>
      match a with
      | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, mul_one] }
                      -- 🎉 no goals

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps (config := { fullyApplied := false })]
protected def _root_.MonoidWithZeroHom.withTopMap {R S : Type*} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      -- ⊢ ZeroHom.toFun { toFun := map ↑f, map_zero' := (_ : ZeroHom.toFun src✝¹ 0 = 0 …
      · simp
        -- 🎉 no goals
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      -- ⊢ ZeroHom.toFun { toFun := map ↑f, map_zero' := (_ : ZeroHom.toFun src✝¹ 0 = 0 …
      · simp
        -- 🎉 no goals
      induction' x using WithTop.recTopCoe with x
      -- ⊢ ZeroHom.toFun { toFun := map ↑f, map_zero' := (_ : ZeroHom.toFun src✝¹ 0 = 0 …
      · simp [hy, this]
        -- 🎉 no goals
      induction' y using WithTop.recTopCoe with y
      -- ⊢ ZeroHom.toFun { toFun := map ↑f, map_zero' := (_ : ZeroHom.toFun src✝¹ 0 = 0 …
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        -- ⊢ ZeroHom.toFun { toFun := map ↑f, map_zero' := (_ : ZeroHom.toFun src✝¹ 0 = 0 …
        simp [mul_top hx, mul_top this]
        -- 🎉 no goals
      · -- porting note: todo: `simp [← coe_mul]` times out
        simp only [map_coe, ← coe_mul, map_mul] }
        -- 🎉 no goals
#align monoid_with_zero_hom.with_top_map MonoidWithZeroHom.withTopMap

instance instSemigroupWithZeroWithTop [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithTop α) :=
  { WithTop.instMulZeroClassWithTop with
    mul := (· * ·)
    zero := 0
    mul_assoc := fun a b c => by
      rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
      -- ⊢ 0 * b * c = 0 * (b * c)
                                             -- 🎉 no goals
      rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
      -- ⊢ a * 0 * c = a * (0 * c)
                                             -- 🎉 no goals
      rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
      -- ⊢ a * b * 0 = a * (b * 0)
                                             -- 🎉 no goals
    -- Porting note: below needed to be rewritten due to changed `simp` behaviour for `coe`
      induction' a using WithTop.recTopCoe with a; · simp [hb, hc]
      -- ⊢ ⊤ * b * c = ⊤ * (b * c)
                                                     -- 🎉 no goals
      induction' b using WithTop.recTopCoe with b; · simp [mul_top ha, top_mul hc]
      -- ⊢ ↑a * ⊤ * c = ↑a * (⊤ * c)
                                                     -- 🎉 no goals
      induction' c using WithTop.recTopCoe with c
      -- ⊢ ↑a * ↑b * ⊤ = ↑a * (↑b * ⊤)
      · rw [mul_top hb, mul_top ha]
        -- ⊢ ↑a * ↑b * ⊤ = ⊤
        rw [← coe_zero, ne_eq, coe_eq_coe] at ha hb
        -- ⊢ ↑a * ↑b * ⊤ = ⊤
        simp [ha, hb]
        -- 🎉 no goals
      simp only [← coe_mul, mul_assoc] }
      -- 🎉 no goals

instance monoidWithZero [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    MonoidWithZero (WithTop α) :=
  { WithTop.instMulZeroOneClassWithTop, WithTop.instSemigroupWithZeroWithTop with }

instance commMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) :=
  { WithTop.monoidWithZero with
    mul := (· * ·)
    zero := 0,
    mul_comm := fun _ _ => ite_congr (propext or_comm) (fun _ => rfl)
      (fun _ => Option.map₂_comm mul_comm) }

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c := by
  induction' c using WithTop.recTopCoe with c
  -- ⊢ (a + b) * ⊤ = a * ⊤ + b * ⊤
  · by_cases ha : a = 0 <;> simp [ha]
    -- ⊢ (a + b) * ⊤ = a * ⊤ + b * ⊤
                            -- 🎉 no goals
                            -- 🎉 no goals
  · by_cases hc : c = 0
    -- ⊢ (a + b) * ↑c = a * ↑c + b * ↑c
    · simp [hc]
      -- 🎉 no goals
    simp [mul_coe hc]
    -- ⊢ (Option.bind (a + b) fun a => Option.some (a * c)) = (Option.bind a fun a => …
    cases a <;> cases b
    -- ⊢ (Option.bind (none + b) fun a => Option.some (a * c)) = (Option.bind none fu …
                -- ⊢ (Option.bind (none + none) fun a => Option.some (a * c)) = (Option.bind none …
                -- ⊢ (Option.bind (Option.some val✝ + none) fun a => Option.some (a * c)) = (Opti …
    repeat' first | rfl |exact congr_arg some (add_mul _ _ _)
    -- 🎉 no goals

/-- This instance requires `CanonicallyOrderedCommSemiring` as it is the smallest class
that derives from both `NonAssocNonUnitalSemiring` and `CanonicallyOrderedAddMonoid`, both
of which are required for distributivity. -/
instance commSemiring [Nontrivial α] : CommSemiring (WithTop α) :=
  { WithTop.addCommMonoidWithOne, WithTop.commMonoidWithZero with
    right_distrib := distrib'
    left_distrib := fun a b c => by
      rw [mul_comm, distrib', mul_comm b, mul_comm c] }
      -- 🎉 no goals

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddMonoid with
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero}

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps (config := { fullyApplied := false })]
protected def _root_.RingHom.withTopMap {R S : Type*} [CanonicallyOrderedCommSemiring R]
    [DecidableEq R] [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  {MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with}
#align ring_hom.with_top_map RingHom.withTopMap

end WithTop

namespace WithBot

variable [DecidableEq α]

instance : DecidableEq (WithBot α) := instDecidableEqOption

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithBot α) :=
  WithTop.instMulZeroClassWithTop

theorem mul_def {a b : WithBot α} :
    a * b = if a = 0 ∨ b = 0 then (0 : WithBot α) else Option.map₂ (· * ·) a b :=
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

theorem mul_eq_bot_iff {a b : WithBot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iff

theorem bot_lt_mul' [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  WithTop.mul_lt_top' (α := αᵒᵈ) ha hb
#align with_bot.bot_lt_mul' WithBot.bot_lt_mul'

theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : ⊥ < a * b :=
  WithTop.mul_lt_top (α := αᵒᵈ) ha hb
#align with_bot.bot_lt_mul WithBot.bot_lt_mul

end Mul

section MulZeroClass

variable [MulZeroClass α]

@[simp, norm_cast] -- porting note: added `simp`
theorem coe_mul {a b : α} : (↑(a * b) : WithBot α) = a * b :=
  WithTop.coe_mul
#align with_bot.coe_mul WithBot.coe_mul

theorem mul_coe {b : α} (hb : b ≠ 0) {a : WithBot α} :
    a * (b : WithBot α) = a.bind fun a : α => ↑(a * b) :=
  WithTop.mul_coe hb
#align with_bot.mul_coe WithBot.mul_coe

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  WithTop.instMulZeroOneClassWithTop

instance [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.noZeroDivisors

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithBot α) :=
  WithTop.instSemigroupWithZeroWithTop

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithBot α) :=
  WithTop.monoidWithZero

instance commMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  WithTop.commMonoidWithZero

instance commSemiring [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    CommSemiring (WithBot α) :=
  WithTop.commSemiring

instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ (fun x y => ↑x * y) { val := x, property := x0 } a ≤ (fun x y => ↑x * y) { v …
    simp only [Subtype.coe_mk]
    -- ⊢ x * a ≤ x * b
    rcases eq_or_ne x 0 with rfl | x0'
    -- ⊢ 0 * a ≤ 0 * b
    · simp
      -- 🎉 no goals
    lift x to α
    -- ⊢ x ≠ ⊥
    · rintro rfl
      -- ⊢ False
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
      -- 🎉 no goals
    induction a using WithBot.recBotCoe
    -- ⊢ ↑x * ⊥ ≤ ↑x * b
    · simp_rw [mul_bot x0', bot_le]
      -- 🎉 no goals
    induction b using WithBot.recBotCoe
    -- ⊢ ↑x * ↑a✝ ≤ ↑x * ⊥
    · exact absurd h (bot_lt_coe _).not_le
      -- 🎉 no goals
    simp only [← coe_mul, coe_le_coe] at *
    -- ⊢ x * a✝¹ ≤ x * a✝
    norm_cast at x0
    -- ⊢ x * a✝¹ ≤ x * a✝
    exact mul_le_mul_of_nonneg_left h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ (fun x y => y * ↑x) { val := x, property := x0 } a ≤ (fun x y => y * ↑x) { v …
    simp only [Subtype.coe_mk]
    -- ⊢ a * x ≤ b * x
    rcases eq_or_ne x 0 with rfl | x0'
    -- ⊢ a * 0 ≤ b * 0
    · simp
      -- 🎉 no goals
    lift x to α
    -- ⊢ x ≠ ⊥
    · rintro rfl
      -- ⊢ False
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
      -- 🎉 no goals
    induction a using WithBot.recBotCoe
    -- ⊢ ⊥ * ↑x ≤ b * ↑x
    · simp_rw [bot_mul x0', bot_le]
      -- 🎉 no goals
    induction b using WithBot.recBotCoe
    -- ⊢ ↑a✝ * ↑x ≤ ⊥ * ↑x
    · exact absurd h (bot_lt_coe _).not_le
      -- 🎉 no goals
    simp only [← coe_mul, coe_le_coe] at *
    -- ⊢ a✝¹ * x ≤ a✝ * x
    norm_cast at x0
    -- ⊢ a✝¹ * x ≤ a✝ * x
    exact mul_le_mul_of_nonneg_right h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ (fun x y => ↑x * y) { val := x, property := x0 } a < (fun x y => ↑x * y) { v …
    simp only [Subtype.coe_mk]
    -- ⊢ x * a < x * b
    lift x to α using x0.ne_bot
    -- ⊢ ↑x * a < ↑x * b
    induction b using WithBot.recBotCoe
    -- ⊢ ↑x * a < ↑x * ⊥
    · exact absurd h not_lt_bot
      -- 🎉 no goals
    induction a using WithBot.recBotCoe
    -- ⊢ ↑x * ⊥ < ↑x * ↑a✝
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
      -- 🎉 no goals
    simp only [← coe_mul, coe_lt_coe] at *
    -- ⊢ x * a✝ < x * a✝¹
    norm_cast at x0
    -- ⊢ x * a✝ < x * a✝¹
    exact mul_lt_mul_of_pos_left h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ (fun x y => y * ↑x) { val := x, property := x0 } a < (fun x y => y * ↑x) { v …
    simp only [Subtype.coe_mk]
    -- ⊢ a * x < b * x
    lift x to α using x0.ne_bot
    -- ⊢ a * ↑x < b * ↑x
    induction b using WithBot.recBotCoe
    -- ⊢ a * ↑x < ⊥ * ↑x
    · exact absurd h not_lt_bot
      -- 🎉 no goals
    induction a using WithBot.recBotCoe
    -- ⊢ ⊥ * ↑x < ↑a✝ * ↑x
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
      -- 🎉 no goals
    simp only [← coe_mul, coe_lt_coe] at *
    -- ⊢ a✝ * x < a✝¹ * x
    norm_cast at x0
    -- ⊢ a✝ * x < a✝¹ * x
    exact mul_lt_mul_of_pos_right h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ a < b
    simp only [Subtype.coe_mk] at h
    -- ⊢ a < b
    rcases eq_or_ne x 0 with rfl | x0'
    -- ⊢ a < b
    · simp at h
      -- 🎉 no goals
    lift x to α
    -- ⊢ x ≠ ⊥
    · rintro rfl
      -- ⊢ False
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
      -- 🎉 no goals
    induction b using WithBot.recBotCoe
    -- ⊢ a < ⊥
    · rw [mul_bot x0'] at h
      -- ⊢ a < ⊥
      exact absurd h bot_le.not_lt
      -- 🎉 no goals
    induction a using WithBot.recBotCoe
    -- ⊢ ⊥ < ↑a✝
    · exact WithBot.bot_lt_coe _
      -- 🎉 no goals
    simp only [← coe_mul, coe_lt_coe] at *
    -- ⊢ a✝ < a✝¹
    norm_cast at x0
    -- ⊢ a✝ < a✝¹
    exact lt_of_mul_lt_mul_left h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ a < b
    simp only [Subtype.coe_mk] at h
    -- ⊢ a < b
    rcases eq_or_ne x 0 with rfl | x0'
    -- ⊢ a < b
    · simp at h
      -- 🎉 no goals
    lift x to α
    -- ⊢ x ≠ ⊥
    · rintro rfl
      -- ⊢ False
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
      -- 🎉 no goals
    induction b using WithBot.recBotCoe
    -- ⊢ a < ⊥
    · rw [bot_mul x0'] at h
      -- ⊢ a < ⊥
      exact absurd h bot_le.not_lt
      -- 🎉 no goals
    induction a using WithBot.recBotCoe
    -- ⊢ ⊥ < ↑a✝
    · exact WithBot.bot_lt_coe _
      -- 🎉 no goals
    simp only [← coe_mul, coe_lt_coe] at *
    -- ⊢ a✝ < a✝¹
    norm_cast at x0
    -- ⊢ a✝ < a✝¹
    exact lt_of_mul_lt_mul_right h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [PosMulMonoRev α] : PosMulMonoRev (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ a ≤ b
    simp only [Subtype.coe_mk] at h
    -- ⊢ a ≤ b
    lift x to α using x0.ne_bot
    -- ⊢ a ≤ b
    induction a using WithBot.recBotCoe
    -- ⊢ ⊥ ≤ b
    · exact bot_le
      -- 🎉 no goals
    induction b using WithBot.recBotCoe
    -- ⊢ ↑a✝ ≤ ⊥
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      -- ⊢ ↑a✝ ≤ ⊥
      exact absurd h (bot_lt_coe _).not_le
      -- 🎉 no goals
    simp only [← coe_mul, coe_le_coe] at *
    -- ⊢ a✝¹ ≤ a✝
    norm_cast at x0
    -- ⊢ a✝¹ ≤ a✝
    exact le_of_mul_le_mul_left h x0 ⟩
    -- 🎉 no goals

instance [MulZeroClass α] [Preorder α] [MulPosMonoRev α] : MulPosMonoRev (WithBot α) :=
  ⟨by
    intro ⟨x, x0⟩ a b h
    -- ⊢ a ≤ b
    simp only [Subtype.coe_mk] at h
    -- ⊢ a ≤ b
    lift x to α using x0.ne_bot
    -- ⊢ a ≤ b
    induction a using WithBot.recBotCoe
    -- ⊢ ⊥ ≤ b
    · exact bot_le
      -- 🎉 no goals
    induction b using WithBot.recBotCoe
    -- ⊢ ↑a✝ ≤ ⊥
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      -- ⊢ ↑a✝ ≤ ⊥
      exact absurd h (bot_lt_coe _).not_le
      -- 🎉 no goals
    simp only [← coe_mul, coe_le_coe] at *
    -- ⊢ a✝¹ ≤ a✝
    norm_cast at x0
    -- ⊢ a✝¹ ≤ a✝
    exact le_of_mul_le_mul_right h x0 ⟩
    -- 🎉 no goals

instance orderedCommSemiring [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    OrderedCommSemiring (WithBot α) :=
  { WithBot.zeroLEOneClass, WithBot.orderedAddCommMonoid, WithBot.commSemiring with
    mul_le_mul_of_nonneg_left  := fun _ _ _ => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun _ _ _ => mul_le_mul_of_nonneg_right }

end WithBot

/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.instOrderedCommSemiring` and
`WithBot.instOrderedCommSemiring`.
-/

variable {α : Type*}

namespace WithTop

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithTop α}

instance instMulZeroClass : MulZeroClass (WithTop α) where
  mul
    | (a : α), (b : α) => ↑(a * b)
    | (a : α), ⊤ => if a = 0 then 0 else ⊤
    | ⊤, (b : α) => if b = 0 then 0 else ⊤
    | ⊤, ⊤ => ⊤
  mul_zero
    | (a : α) => congr_arg some <| mul_zero _
    | ⊤ => if_pos rfl
  zero_mul
    | (b : α) => congr_arg some <| zero_mul _
    | ⊤ => if_pos rfl

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithTop α) = a * b := rfl

lemma mul_top' : ∀ (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm

@[simp] lemma mul_top (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]

lemma top_mul' : ∀ (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm

@[simp] lemma top_mul (hb : b ≠ 0) : ⊤ * b = ⊤ := by rw [top_mul', if_neg hb]

@[simp] lemma top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := rfl

lemma mul_def (a b : WithTop α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

lemma mul_eq_top_iff : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by rw [mul_def]; aesop

lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithTop α) = a.bind fun a ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, hb]; rfl
  | (a : α) => rfl

lemma coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithTop α) = b.bind fun b ↦ ↑(a * b)
  | ⊤ => by simp [ha]; rfl
  | (b : α) => rfl

@[simp]
lemma untopD_zero_mul (a b : WithTop α) : (a * b).untopD 0 = a.untopD 0 * b.untopD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untopD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untopD_coe, mul_zero]
  cases a; · rw [top_mul hb, untopD_top, zero_mul]
  cases b; · rw [mul_top ha, untopD_top, mul_zero]
  rw [← coe_mul, untopD_coe, untopD_coe, untopD_coe]

theorem mul_ne_top {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b ≠ ⊤ := by
  simp [mul_eq_top_iff, *]

theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  exact mul_ne_top ha hb

instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α) := by
  refine ⟨fun h₁ => Decidable.byContradiction fun h₂ => ?_⟩
  rw [mul_def, if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

variable [Preorder α]

protected lemma mul_right_strictMono [PosMulStrictMono α] (h₀ : 0 < a) (hinf : a ≠ ⊤) :
    StrictMono (a * ·) := by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, mul_top h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  exact mul_lt_mul_of_pos_left hbc h₀

protected lemma mul_left_strictMono [MulPosStrictMono α] (h₀ : 0 < a) (hinf : a ≠ ⊤) :
    StrictMono (· * a) := by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, top_mul h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  exact mul_lt_mul_of_pos_right hbc h₀

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) where
  __ := instMulZeroClass
  one_mul
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
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
      cases x with | top => simp [hy, this] | coe x => ?_
      cases y with
      | top =>
        have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      | coe y => simp [← coe_mul] }

instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithTop α) where
  __ := instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
    cases a with | top => simp [hb, hc] | coe a => ?_
    cases b with | top => simp [mul_top ha, top_mul hc] | coe b => ?_
    cases c with
    | top =>
      rw [mul_top hb, mul_top ha]
      rw [← coe_zero, ne_eq, coe_eq_coe] at ha hb
      simp [ha, hb]
    | coe c => simp only [← coe_mul, mul_assoc]

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : ℕ}

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

@[simp] lemma top_pow : ∀ {n : ℕ}, n ≠ 0 → (⊤ : WithTop α) ^ n = ⊤ | _ + 1, _ => rfl

@[simp] lemma pow_eq_top_iff : x ^ n = ⊤ ↔ x = ⊤ ∧ n ≠ 0 := by
  cases x <;> cases n <;> simp [← coe_pow]

lemma pow_ne_top_iff : x ^ n ≠ ⊤ ↔ x ≠ ⊤ ∨ n = 0 := by simp [pow_eq_top_iff, or_iff_not_imp_left]

@[simp] lemma pow_lt_top_iff [Preorder α] : x ^ n < ⊤ ↔ x < ⊤ ∨ n = 0 := by
  simp_rw [WithTop.lt_top_iff_ne_top, pow_ne_top_iff]

lemma eq_top_of_pow (n : ℕ) (hx : x ^ n = ⊤) : x = ⊤ := (pow_eq_top_iff.1 hx).1
lemma pow_ne_top (hx : x ≠ ⊤) : x ^ n ≠ ⊤ := pow_ne_top_iff.2 <| .inl hx
lemma pow_lt_top [Preorder α] (hx : x < ⊤) : x ^ n < ⊤ := pow_lt_top_iff.2 <| .inl hx

end MonoidWithZero

instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) where
  __ := instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] : NonUnitalNonAssocSemiring (WithTop α) where
  toAddCommMonoid := WithTop.addCommMonoid
  __ := WithTop.instMulZeroClass
  right_distrib a b c := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [mul_coe_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (add_mul _ _ _)
  left_distrib c a b := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [coe_mul_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (mul_add _ _ _)

instance instNonAssocSemiring [NonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [Nontrivial α] : NonAssocSemiring (WithTop α) where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := WithTop.instMulZeroOneClass
  __ := WithTop.addCommMonoidWithOne

instance instNonUnitalSemiring [NonUnitalSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] : NonUnitalSemiring (WithTop α) where
  toNonUnitalNonAssocSemiring := WithTop.instNonUnitalNonAssocSemiring
  __ := WithTop.instSemigroupWithZero

instance instSemiring [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : Semiring (WithTop α) where
  toNonUnitalSemiring := WithTop.instNonUnitalSemiring
  __ := WithTop.instMonoidWithZero
  __ := WithTop.addCommMonoidWithOne

instance instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : CommSemiring (WithTop α) where
  toSemiring := WithTop.instSemiring
  __ := WithTop.instCommMonoidWithZero

instance instIsOrderedRing [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : IsOrderedRing (WithTop α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps -fullyApplied]
protected def _root_.RingHom.withTopMap {R S : Type*}
    [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
    [DecidableEq R] [Nontrivial R]
    [NonAssocSemiring S] [PartialOrder S] [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  {MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with}

variable [CommSemiring α] [PartialOrder α] [OrderBot α]
  [CanonicallyOrderedAdd α] [PosMulStrictMono α]
  {a a₁ a₂ b₁ b₂ : WithTop α}

@[gcongr]
protected lemma mul_lt_mul (ha : a₁ < a₂) (hb : b₁ < b₂) : a₁ * b₁ < a₂ * b₂ := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  lift a₁ to α using ha.lt_top.ne
  lift b₁ to α using hb.lt_top.ne
  obtain rfl | ha₂ := eq_or_ne a₂ ⊤
  · rw [top_mul (by simpa [bot_eq_zero] using hb.bot_lt.ne')]
    exact coe_lt_top _
  obtain rfl | hb₂ := eq_or_ne b₂ ⊤
  · rw [mul_top (by simpa [bot_eq_zero] using ha.bot_lt.ne')]
    exact coe_lt_top _
  lift a₂ to α using ha₂
  lift b₂ to α using hb₂
  norm_cast at *
  obtain rfl | hb₁ := eq_zero_or_pos b₁
  · rw [mul_zero]
    exact mul_pos (by simpa [bot_eq_zero] using ha.bot_lt) hb
  · exact mul_lt_mul ha hb.le hb₁ (zero_le _)

variable [NoZeroDivisors α] [Nontrivial α] {a b : WithTop α}

protected lemma pow_right_strictMono : ∀ {n : ℕ}, n ≠ 0 → StrictMono fun a : WithTop α ↦ a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simpa only [pow_one] using strictMono_id
  | n + 2, _ => fun x y h ↦ by
    simp_rw [pow_succ _ (n + 1)]
    exact WithTop.mul_lt_mul (WithTop.pow_right_strictMono n.succ_ne_zero h) h

@[gcongr] protected lemma pow_lt_pow_left (hab : a < b) {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n :=
  WithTop.pow_right_strictMono hn hab

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
lemma unbotD_zero_mul (a b : WithBot α) : (a * b).unbotD 0 = a.unbotD 0 * b.unbotD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbotD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbotD_coe, mul_zero]
  cases a; · rw [bot_mul hb, unbotD_bot, zero_mul]
  cases b; · rw [mul_bot ha, unbotD_bot, mul_zero]
  rw [← coe_mul, unbotD_coe, unbotD_coe, unbotD_coe]

theorem mul_ne_bot {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a * b ≠ ⊥ :=
  WithTop.mul_ne_top (α := αᵒᵈ) ha hb

theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
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

instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  WithTop.instCommMonoidWithZero

instance instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] :
    CommSemiring (WithBot α) :=
  WithTop.instCommSemiring

instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) where
  mul_le_mul_of_nonneg_left x x0 a b h := by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [mul_bot x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_left h x0

instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) where
  mul_le_mul_of_nonneg_right x x0 a b h := by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [bot_mul x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_right h x0

instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) where
  mul_lt_mul_of_pos_left x x0 a b h := by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_left h x0

instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) where
  mul_lt_mul_of_pos_right x x0 a b h := by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_right h x0

instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_left h x0

instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_right h x0

instance [MulZeroClass α] [Preorder α] [PosMulReflectLE α] : PosMulReflectLE (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_left h x0

instance [MulZeroClass α] [Preorder α] [MulPosReflectLE α] : MulPosReflectLE (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_right h x0

instance instIsOrderedRing [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    [CanonicallyOrderedAdd α] [NoZeroDivisors α] [Nontrivial α] :
    IsOrderedRing (WithBot α) where

end WithBot

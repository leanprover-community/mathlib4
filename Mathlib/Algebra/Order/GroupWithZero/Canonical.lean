/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Algebra.Order.ZeroLEOne

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `NNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

variable {α : Type*}

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type*) extends LinearOrderedCommMonoid α,
  CommMonoidWithZero α where
  /-- `0 ≤ 1` in any linearly ordered commutative monoid. -/
  zero_le_one : (0 : α) ≤ 1

/-- A linearly ordered commutative group with a zero element. -/
class LinearOrderedCommGroupWithZero (α : Type*) extends LinearOrderedCommMonoidWithZero α,
  CommGroupWithZero α

instance (priority := 100) LinearOrderedCommMonoidWithZero.toZeroLeOneClass
    [LinearOrderedCommMonoidWithZero α] : ZeroLEOneClass α :=
  { ‹LinearOrderedCommMonoidWithZero α› with }

instance (priority := 100) canonicallyOrderedAddCommMonoid.toZeroLeOneClass
    [CanonicallyOrderedAddCommMonoid α] [One α] : ZeroLEOneClass α :=
  ⟨zero_le 1⟩

section LinearOrderedCommMonoidWithZero
variable [LinearOrderedCommMonoidWithZero α] {a b c d x y z : α} {n : ℕ}

/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/
/-- Pullback a `LinearOrderedCommMonoidWithZero` under an injective map.
See note [reducible non-instances]. -/
abbrev Function.Injective.linearOrderedCommMonoidWithZero {β : Type*} [Zero β] [One β] [Mul β]
    [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoidWithZero β :=
  { LinearOrder.lift f hf hsup hinf, hf.orderedCommMonoid f one mul npow,
    hf.commMonoidWithZero f zero one mul npow with
    zero_le_one :=
      show f 0 ≤ f 1 by simp only [zero, one, LinearOrderedCommMonoidWithZero.zero_le_one] }

@[simp] lemma zero_le' : 0 ≤ a := by
  simpa only [mul_zero, mul_one] using mul_le_mul_left' (zero_le_one' α) a

@[simp]
theorem not_lt_zero' : ¬a < 0 :=
  not_lt_of_le zero_le'

@[simp]
theorem le_zero_iff : a ≤ 0 ↔ a = 0 :=
  ⟨fun h ↦ le_antisymm h zero_le', fun h ↦ h ▸ le_rfl⟩

theorem zero_lt_iff : 0 < a ↔ a ≠ 0 :=
  ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne zero_le' h.symm⟩

theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 ↦ not_lt_zero' <| show b < 0 from h1 ▸ h

instance instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual :
    LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) :=
  { Additive.orderedAddCommMonoid, Additive.linearOrder with
    top := (0 : α)
    top_add' := fun a ↦ zero_mul (Additive.toMul a)
    le_top := fun _ ↦ zero_le' }

variable [NoZeroDivisors α]

lemma pow_pos_iff (hn : n ≠ 0) : 0 < a ^ n ↔ 0 < a := by simp_rw [zero_lt_iff, pow_ne_zero_iff hn]

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero
variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

-- TODO: Do we really need the following two?
/-- Alias of `mul_le_one'` for unification. -/
theorem mul_le_one₀ (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_one' ha hb

/-- Alias of `one_le_mul'` for unification. -/
theorem one_le_mul₀ (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  one_le_mul ha hb

theorem le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b := by
  simpa only [mul_inv_cancel_right₀ h] using mul_le_mul_right' hab c⁻¹

theorem le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
  le_of_le_mul_right h (by simpa [h] using hab)

theorem mul_inv_le_of_le_mul (hab : a ≤ b * c) : a * c⁻¹ ≤ b := by
  by_cases h : c = 0
  · simp [h]
  · exact le_of_le_mul_right h (by simpa [h] using hab)

theorem inv_le_one₀ (ha : a ≠ 0) : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  inv_le_one' (a := Units.mk0 a ha)

theorem one_le_inv₀ (ha : a ≠ 0) : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  one_le_inv' (a := Units.mk0 a ha)

theorem le_mul_inv_iff₀ (hc : c ≠ 0) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
  ⟨fun h ↦ inv_inv c ▸ mul_inv_le_of_le_mul h, le_mul_inv_of_mul_le hc⟩

theorem mul_inv_le_iff₀ (hc : c ≠ 0) : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
  ⟨fun h ↦ inv_inv c ▸ le_mul_inv_of_mul_le (inv_ne_zero hc) h, mul_inv_le_of_le_mul⟩

theorem div_le_div₀ (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) :
    a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b := by
  rw [mul_inv_le_iff₀ hb, mul_right_comm, le_mul_inv_iff₀ hd]

@[simp]
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  zero_lt_iff.2 <| u.ne_zero

theorem mul_lt_mul_of_lt_of_le₀ (hab : a ≤ b) (hb : b ≠ 0) (hcd : c < d) : a * c < b * d :=
  have hd : d ≠ 0 := ne_zero_of_lt hcd
  if ha : a = 0 then by
    rw [ha, zero_mul, zero_lt_iff]
    exact mul_ne_zero hb hd
  else
    if hc : c = 0 then by
      rw [hc, mul_zero, zero_lt_iff]
      exact mul_ne_zero hb hd
    else
      show Units.mk0 a ha * Units.mk0 c hc < Units.mk0 b hb * Units.mk0 d hd from
        mul_lt_mul_of_le_of_lt hab hcd

theorem mul_lt_mul₀ (hab : a < b) (hcd : c < d) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le₀ hab.le (ne_zero_of_lt hab) hcd

theorem mul_inv_lt_of_lt_mul₀ (h : a < b * c) : a * c⁻¹ < b := by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul h

theorem inv_mul_lt_of_lt_mul₀ (h : a < b * c) : b⁻¹ * a < c := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

theorem mul_lt_right₀ (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c := by
  contrapose! h
  exact le_of_le_mul_right hc h

theorem inv_lt_one₀ (ha : a ≠ 0) : a⁻¹ < 1 ↔ 1 < a :=
  inv_lt_one' (a := Units.mk0 a ha)

theorem one_lt_inv₀ (ha : a ≠ 0) : 1 < a⁻¹ ↔ a < 1 :=
  one_lt_inv' (a := Units.mk0 a ha)

theorem inv_lt_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
  show (Units.mk0 a ha)⁻¹ < (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb < Units.mk0 a ha from
    have : CovariantClass αˣ αˣ (· * ·) (· < ·) :=
      IsLeftCancelMul.covariant_mul_lt_of_covariant_mul_le αˣ
    inv_lt_inv_iff

theorem inv_le_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  show (Units.mk0 a ha)⁻¹ ≤ (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb ≤ Units.mk0 a ha from
    inv_le_inv_iff

theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  simp_rw [← inv_le_inv₀ ha (ne_of_gt hc)] at hh
  have := mul_lt_mul_of_lt_of_le₀ hh (inv_ne_zero (ne_of_gt hc)) h
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ (ne_of_gt hc)] using this

theorem mul_le_mul_right₀ (hc : c ≠ 0) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨le_of_le_mul_right hc, fun hab ↦ mul_le_mul_right' hab _⟩

theorem mul_le_mul_left₀ (ha : a ≠ 0) : a * b ≤ a * c ↔ b ≤ c := by
  simp only [mul_comm a]
  exact mul_le_mul_right₀ ha

theorem div_le_div_right₀ (hc : c ≠ 0) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_le_mul_right₀ (inv_ne_zero hc)]

theorem div_le_div_left₀ (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_left₀ ha, inv_le_inv₀ hb hc]

theorem le_div_iff₀ (hc : c ≠ 0) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

theorem div_le_iff₀ (hc : c ≠ 0) : a / c ≤ b ↔ a ≤ b * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- `Equiv.mulLeft₀` as an `OrderIso` on a `LinearOrderedCommGroupWithZero.`.

Note that `OrderIso.mulLeft₀` refers to the `LinearOrderedField` version. -/
@[simps! (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulLeft₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulLeft₀ a ha with map_rel_iff' := mul_le_mul_left₀ ha }

theorem OrderIso.mulLeft₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulLeft₀' ha).symm = OrderIso.mulLeft₀' (inv_ne_zero ha) := by
  ext
  rfl

/-- `Equiv.mulRight₀` as an `OrderIso` on a `LinearOrderedCommGroupWithZero.`.

Note that `OrderIso.mulRight₀` refers to the `LinearOrderedField` version. -/
@[simps! (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulRight₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulRight₀ a ha with map_rel_iff' := mul_le_mul_right₀ ha }

theorem OrderIso.mulRight₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulRight₀' ha).symm = OrderIso.mulRight₀' (inv_ne_zero ha) := by
  ext
  rfl

#adaptation_note /-- 2024-04-23
After https://github.com/leanprover/lean4/pull/3965,
we need to either write `@inv_zero (G₀ := α) (_)` in `neg_top`,
or use `set_option backward.isDefEq.lazyProjDelta false`.
See https://github.com/leanprover-community/mathlib4/issues/12535 -/
instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) :=
  { Additive.subNegMonoid, instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual,
    Additive.instNontrivial with
    neg_top := set_option backward.isDefEq.lazyProjDelta false in @inv_zero _ (_)
    add_neg_cancel := fun a ha ↦ mul_inv_cancel (G₀ := α) (id ha : Additive.toMul a ≠ 0) }

lemma pow_lt_pow_succ (ha : 1 < a) : a ^ n < a ^ n.succ := by
  rw [← one_mul (a ^ n), pow_succ']
  exact mul_lt_right₀ _ ha (pow_ne_zero _ (zero_lt_one.trans ha).ne')

lemma pow_lt_pow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n := by
  induction' hmn with n _ ih; exacts [pow_lt_pow_succ ha, lt_trans ih (pow_lt_pow_succ ha)]

@[deprecated (since := "2023-12-23")] alias pow_lt_pow₀ := pow_lt_pow_right₀

end LinearOrderedCommGroupWithZero

instance instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
    [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.linearOrder with
    zero := Multiplicative.ofAdd (⊤ : α)
    zero_mul := @top_add _ (_)
    -- Porting note:  Here and elsewhere in the file, just `zero_mul` worked in Lean 3. See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Type.20synonyms
    mul_zero := @add_top _ (_)
    zero_le_one := (le_top : (0 : α) ≤ ⊤) }

instance [LinearOrderedAddCommGroupWithTop α] :
    LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.divInvMonoid, instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual,
    Multiplicative.instNontrivial with
    inv_zero := @LinearOrderedAddCommGroupWithTop.neg_top _ (_)
    mul_inv_cancel := @LinearOrderedAddCommGroupWithTop.add_neg_cancel _ (_) }

namespace WithZero
section Preorder
variable [Preorder α] {a b : α}

instance preorder : Preorder (WithZero α) := WithBot.preorder
instance orderBot : OrderBot (WithZero α) := WithBot.orderBot

lemma zero_le (a : WithZero α) : 0 ≤ a := bot_le

lemma zero_lt_coe (a : α) : (0 : WithZero α) < a := WithBot.bot_lt_coe a

lemma zero_eq_bot : (0 : WithZero α) = ⊥ := rfl

@[simp, norm_cast] lemma coe_lt_coe : (a : WithZero α) < b ↔ a < b := WithBot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe : (a : WithZero α) ≤ b ↔ a ≤ b := WithBot.coe_le_coe

@[simp, norm_cast] lemma one_lt_coe [One α] : 1 < (a : WithZero α) ↔ 1 < a := coe_lt_coe

@[simp, norm_cast] lemma one_le_coe [One α] : 1 ≤ (a : WithZero α) ↔ 1 ≤ a := coe_le_coe

@[simp, norm_cast] lemma coe_lt_one [One α] : (a : WithZero α) < 1 ↔ a < 1 := coe_lt_coe

@[simp, norm_cast] lemma coe_le_one [One α] : (a : WithZero α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

theorem coe_le_iff {x : WithZero α} : (a : WithZero α) ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b :=
  WithBot.coe_le_iff

instance covariantClass_mul_le [Mul α] [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a; · exact zero_le _
  induction b; · exact zero_le _
  rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul _ c, ← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' _

protected lemma covariantClass_add_le [AddZeroClass α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (h : ∀ a : α, 0 ≤ a) : CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a
  · rwa [zero_add, zero_add]
  induction b
  · rw [add_zero]
    induction c
    · rw [add_zero]
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add, ← coe_add _ c, coe_le_coe]
    exact add_le_add_left hbc' _

instance existsAddOfLE [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithZero α) :=
  ⟨fun {a b} => by
    induction a
    · exact fun _ => ⟨b, (zero_add b).symm⟩
    induction b
    · exact fun h => (WithBot.not_coe_le_bot _ h).elim
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩

end Preorder

section PartialOrder
variable [PartialOrder α]

instance partialOrder : PartialOrder (WithZero α) := WithBot.partialOrder

instance contravariantClass_mul_lt [Mul α] [ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (WithZero α) (WithZero α) (· * ·) (· < ·) := by
  refine ⟨fun a b c h => ?_⟩
  have := ((zero_le _).trans_lt h).ne'
  induction a
  · simp at this
  induction c
  · simp at this
  induction b
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

end PartialOrder

instance lattice [Lattice α] : Lattice (WithZero α) := WithBot.lattice

section LinearOrder
variable [LinearOrder α] {a b c : α}

instance linearOrder : LinearOrder (WithZero α) := WithBot.linearOrder

-- Porting note (#10618): @[simp] can prove this
protected lemma le_max_iff : (a : WithZero α) ≤ max (b : WithZero α) c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]

-- Porting note (#10618): @[simp] can prove this
protected lemma min_le_iff : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]

end LinearOrder

instance orderedCommMonoid [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero.toCommMonoid, WithZero.partialOrder with
    mul_le_mul_left := fun _ _ => mul_le_mul_left' }

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `WithZero α` is an `OrderedAddCommMonoid`. -/
-- See note [reducible non-instances]
protected abbrev orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariantClass_add_le zero_le).. }

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance canonicallyOrderedAddCommMonoid [CanonicallyOrderedAddCommMonoid α] :
    CanonicallyOrderedAddCommMonoid (WithZero α) :=
  { WithZero.orderBot,
    WithZero.orderedAddCommMonoid _root_.zero_le,
    WithZero.existsAddOfLE with
    le_self_add := fun a b => by
      induction a
      · exact bot_le
      induction b
      · exact le_rfl
      · exact WithZero.coe_le_coe.2 le_self_add }

instance canonicallyLinearOrderedAddCommMonoid [CanonicallyLinearOrderedAddCommMonoid α] :
    CanonicallyLinearOrderedAddCommMonoid (WithZero α) :=
  { WithZero.canonicallyOrderedAddCommMonoid, WithZero.linearOrder with }

instance instLinearOrderedCommMonoidWithZero [LinearOrderedCommMonoid α] :
    LinearOrderedCommMonoidWithZero (WithZero α) :=
  { WithZero.linearOrder, WithZero.commMonoidWithZero with
    mul_le_mul_left := fun _ _ ↦ mul_le_mul_left', zero_le_one := WithZero.zero_le _ }

instance instLinearOrderedCommGroupWithZero [LinearOrderedCommGroup α] :
    LinearOrderedCommGroupWithZero (WithZero α) where
  __ := instLinearOrderedCommMonoidWithZero
  __ := commGroupWithZero

end WithZero

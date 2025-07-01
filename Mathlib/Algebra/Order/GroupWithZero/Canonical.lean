/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Monoid.TypeTags

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

variable {α β : Type*}

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type*) extends CommMonoidWithZero α, LinearOrder α,
    IsOrderedMonoid α, OrderBot α where
  /-- `0 ≤ 1` in any linearly ordered commutative monoid. -/
  zero_le_one : (0 : α) ≤ 1

/-- A linearly ordered commutative group with a zero element. -/
class LinearOrderedCommGroupWithZero (α : Type*) extends LinearOrderedCommMonoidWithZero α,
  CommGroupWithZero α

instance (priority := 100) LinearOrderedCommMonoidWithZero.toZeroLeOneClass
    [LinearOrderedCommMonoidWithZero α] : ZeroLEOneClass α :=
  { ‹LinearOrderedCommMonoidWithZero α› with }

instance (priority := 100) CanonicallyOrderedAdd.toZeroLeOneClass
    [AddZeroClass α] [LE α] [CanonicallyOrderedAdd α] [One α] : ZeroLEOneClass α :=
  ⟨zero_le 1⟩

section LinearOrderedCommMonoidWithZero
variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : ℕ}

/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/
/-- Pullback a `LinearOrderedCommMonoidWithZero` under an injective map.
See note [reducible non-instances]. -/
abbrev Function.Injective.linearOrderedCommMonoidWithZero {β : Type*} [Zero β] [Bot β] [One β]
    [Mul β] [Pow β ℕ] [Max β] [Min β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y))
    (bot : f ⊥ = ⊥) : LinearOrderedCommMonoidWithZero β where
  __ := LinearOrder.lift f hf hsup hinf
  __ := hf.isOrderedMonoid f one mul npow
  __ := hf.commMonoidWithZero f zero one mul npow
  zero_le_one :=
      show f 0 ≤ f 1 by simp only [zero, one, LinearOrderedCommMonoidWithZero.zero_le_one]
  bot_le a := show f ⊥ ≤ f a from bot ▸ bot_le

@[simp] lemma zero_le' : 0 ≤ a := by
  simpa only [mul_zero, mul_one] using mul_le_mul_left' (zero_le_one' α) a

@[simp]
theorem not_lt_zero' : ¬a < 0 :=
  not_lt_of_ge zero_le'

@[simp]
theorem le_zero_iff : a ≤ 0 ↔ a = 0 :=
  ⟨fun h ↦ le_antisymm h zero_le', fun h ↦ h ▸ le_rfl⟩

theorem zero_lt_iff : 0 < a ↔ a ≠ 0 :=
  ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne zero_le' h.symm⟩

theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 ↦ not_lt_zero' <| show b < 0 from h1 ▸ h

/-- See also `bot_eq_zero` and `bot_eq_zero'` for canonically ordered monoids. -/
lemma bot_eq_zero'' : (⊥ : α) = 0 := eq_of_forall_ge_iff fun _ ↦ by simp

instance instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual :
    LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) where
  top := .ofMul <| .toDual 0
  top_add' a := zero_mul a.toMul.ofDual
  le_top _ := zero_le'

instance instLinearOrderedAddCommMonoidWithTopOrderDualAdditive :
    LinearOrderedAddCommMonoidWithTop (Additive α)ᵒᵈ where
  top := .toDual <| .ofMul _
  top_add' := fun a ↦ zero_mul (Additive.toMul (OrderDual.ofDual a))
  le_top := fun a ↦ @zero_le' _ _ (Additive.toMul (OrderDual.ofDual a))

variable [NoZeroDivisors α]

lemma pow_pos_iff (hn : n ≠ 0) : 0 < a ^ n ↔ 0 < a := by simp_rw [zero_lt_iff, pow_ne_zero_iff hn]

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero
variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toMulPosMono : MulPosMono α where
  elim _a _b _c hbc := mul_le_mul_right' hbc _

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toPosMulMono : PosMulMono α where
  elim _a _b _c hbc := mul_le_mul_left' hbc _

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toPosMulReflectLE :
    PosMulReflectLE α where
  elim a b c hbc := by simpa [a.2.ne'] using mul_le_mul_left' hbc a⁻¹

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toMulPosReflectLE :
    MulPosReflectLE α where
  elim a b c hbc := by simpa [a.2.ne'] using mul_le_mul_right' hbc a⁻¹

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toPosMulReflectLT :
    PosMulReflectLT α where elim _a _b _c := lt_of_mul_lt_mul_left'

#adaptation_note /-- 2025-03-29 lean4#7717 Needed to add `dsimp only` -/
-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toPosMulStrictMono :
    PosMulStrictMono α where
  elim a b c hbc := by dsimp only; by_contra! h; exact hbc.not_ge <| (mul_le_mul_left a.2).1 h

#adaptation_note /-- 2025-03-29 lean4#7717 Needed to add `dsimp only` -/
-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toMulPosStrictMono :
    MulPosStrictMono α where
  elim a b c hbc := by dsimp only; by_contra! h; exact hbc.not_ge <| (mul_le_mul_right a.2).1 h

@[deprecated mul_inv_le_of_le_mul₀ (since := "2024-11-18")]
theorem mul_inv_le_of_le_mul (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
  mul_inv_le_of_le_mul₀ zero_le' zero_le' hab

@[simp]
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  zero_lt_iff.2 u.ne_zero

@[deprecated mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (since := "2024-11-18")]
theorem mul_lt_mul_of_lt_of_le₀ (hab : a ≤ b) (hb : b ≠ 0) (hcd : c < d) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hab hcd zero_le' (zero_lt_iff.2 hb)

@[deprecated mul_lt_mul'' (since := "2024-11-18")]
theorem mul_lt_mul₀ (hab : a < b) (hcd : c < d) : a * c < b * d :=
  mul_lt_mul'' hab hcd zero_le' zero_le'

theorem mul_inv_lt_of_lt_mul₀ (h : a < b * c) : a * c⁻¹ < b := by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le' zero_le' h

theorem inv_mul_lt_of_lt_mul₀ (h : a < b * c) : b⁻¹ * a < c := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  rw [← inv_le_inv₀ (zero_lt_iff.2 ha) hc] at hh
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
    using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh  h zero_le' (inv_pos.2 hc)

@[deprecated div_le_div_iff_of_pos_right (since := "2024-11-18")]
theorem div_le_div_right₀ (hc : c ≠ 0) : a / c ≤ b / c ↔ a ≤ b :=
  div_le_div_iff_of_pos_right (zero_lt_iff.2 hc)

@[deprecated div_le_div_iff_of_pos_left (since := "2024-11-18")]
theorem div_le_div_left₀ (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / b ≤ a / c ↔ c ≤ b :=
  div_le_div_iff_of_pos_left (zero_lt_iff.2 ha) (zero_lt_iff.2 hb) (zero_lt_iff.2 hc)

/-- `Equiv.mulLeft₀` as an `OrderIso` on a `LinearOrderedCommGroupWithZero.`. -/
@[simps! +simpRhs apply toEquiv,
deprecated OrderIso.mulLeft₀ (since := "2024-11-18")]
def OrderIso.mulLeft₀' {a : α} (ha : a ≠ 0) : α ≃o α := .mulLeft₀ a (zero_lt_iff.2 ha)

set_option linter.deprecated false in
@[deprecated OrderIso.mulLeft₀_symm (since := "2024-11-18")]
theorem OrderIso.mulLeft₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulLeft₀' ha).symm = OrderIso.mulLeft₀' (inv_ne_zero ha) := by
  ext
  rfl

/-- `Equiv.mulRight₀` as an `OrderIso` on a `LinearOrderedCommGroupWithZero.`. -/
@[simps! +simpRhs apply toEquiv,
deprecated OrderIso.mulRight₀ (since := "2024-11-18")]
def OrderIso.mulRight₀' {a : α} (ha : a ≠ 0) : α ≃o α := .mulRight₀ a (zero_lt_iff.2 ha)

set_option linter.deprecated false in
@[deprecated OrderIso.mulRight₀_symm (since := "2024-11-18")]
theorem OrderIso.mulRight₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulRight₀' ha).symm = OrderIso.mulRight₀' (inv_ne_zero ha) := by
  ext
  rfl

instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) where
  neg_top := inv_zero (G₀ := α)
  add_neg_cancel := fun a ha ↦ mul_inv_cancel₀ (G₀ := α) (id ha : a.toMul ≠ 0)

instance : LinearOrderedAddCommGroupWithTop (Additive α)ᵒᵈ where
  neg_top := inv_zero (G₀ := α)
  add_neg_cancel := fun a ha ↦ mul_inv_cancel₀ (G₀ := α) (id ha : a.toMul ≠ 0)

@[deprecated pow_lt_pow_right₀ (since := "2024-11-18")]
lemma pow_lt_pow_succ (ha : 1 < a) : a ^ n < a ^ n.succ := pow_lt_pow_right₀ ha n.lt_succ_self

end LinearOrderedCommGroupWithZero

instance instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
    [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) where
  zero := Multiplicative.ofAdd (OrderDual.toDual ⊤)
  zero_mul := @top_add _ (_)
  -- Porting note:  Here and elsewhere in the file, just `zero_mul` worked in Lean 3. See
  -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Type.20synonyms
  mul_zero := @add_top _ (_)
  zero_le_one := (le_top : (0 : α) ≤ ⊤)

@[simp]
theorem ofAdd_toDual_eq_zero_iff [LinearOrderedAddCommMonoidWithTop α]
    (x : α) : Multiplicative.ofAdd (OrderDual.toDual x) = 0 ↔ x = ⊤ := Iff.rfl

@[simp]
theorem ofDual_toAdd_eq_top_iff [LinearOrderedAddCommMonoidWithTop α]
    (x : Multiplicative αᵒᵈ) : OrderDual.ofDual x.toAdd = ⊤ ↔ x = 0 := Iff.rfl

@[simp]
theorem ofAdd_bot [LinearOrderedAddCommMonoidWithTop α] :
    Multiplicative.ofAdd ⊥ = (0 : Multiplicative αᵒᵈ) := rfl

@[simp]
theorem ofDual_toAdd_zero [LinearOrderedAddCommMonoidWithTop α] :
    OrderDual.ofDual (0 : Multiplicative αᵒᵈ).toAdd = ⊤ := rfl

instance [LinearOrderedAddCommGroupWithTop α] :
    LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.divInvMonoid, instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual,
    Multiplicative.instNontrivial with
    inv_zero := @LinearOrderedAddCommGroupWithTop.neg_top _ (_)
    mul_inv_cancel := @LinearOrderedAddCommGroupWithTop.add_neg_cancel _ (_) }

namespace WithZero
section Preorder
variable [Preorder α] [Preorder β] {x : WithZero α} {a b : α}

instance instPreorder : Preorder (WithZero α) := WithBot.preorder
instance instOrderBot : OrderBot (WithZero α) := WithBot.orderBot

@[simp] lemma zero_le (a : WithZero α) : 0 ≤ a := bot_le

@[simp] lemma zero_lt_coe (a : α) : (0 : WithZero α) < a := WithBot.bot_lt_coe a
@[simp] lemma not_coe_le_zero : ¬ a ≤ (0 : WithZero α) := WithBot.not_coe_le_bot a
@[simp] lemma not_lt_zero : ¬ x < (0 : WithZero α) := WithBot.not_lt_bot _

lemma zero_eq_bot : (0 : WithZero α) = ⊥ := rfl

@[simp, norm_cast] lemma coe_lt_coe : (a : WithZero α) < b ↔ a < b := WithBot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe : (a : WithZero α) ≤ b ↔ a ≤ b := WithBot.coe_le_coe

@[simp, norm_cast] lemma one_lt_coe [One α] : 1 < (a : WithZero α) ↔ 1 < a := coe_lt_coe

@[simp, norm_cast] lemma one_le_coe [One α] : 1 ≤ (a : WithZero α) ↔ 1 ≤ a := coe_le_coe

@[simp, norm_cast] lemma coe_lt_one [One α] : (a : WithZero α) < 1 ↔ a < 1 := coe_lt_coe

@[simp, norm_cast] lemma coe_le_one [One α] : (a : WithZero α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

theorem coe_le_iff {x : WithZero α} : (a : WithZero α) ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b :=
  WithBot.coe_le_iff

@[simp] lemma unzero_le_unzero {a b : WithZero α} (ha hb) :
    unzero (x := a) ha ≤ unzero (x := b) hb ↔ a ≤ b := by
  -- TODO: Fix `lift` so that it doesn't try to clear the hypotheses I give it when it is
  -- impossible to do so. See https://github.com/leanprover-community/mathlib4/issues/19160
  lift a to α using id ha
  lift b to α using id hb
  simp

instance instMulLeftMono [Mul α] [MulLeftMono α] :
    MulLeftMono (WithZero α) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a; · exact zero_le _
  induction b; · exact zero_le _
  rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul _ c, ← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' _

protected lemma addLeftMono [AddZeroClass α] [AddLeftMono α]
    (h : ∀ a : α, 0 ≤ a) : AddLeftMono (WithZero α) := by
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

instance instExistsAddOfLE [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithZero α) :=
  ⟨fun {a b} => by
    induction a
    · exact fun _ => ⟨b, (zero_add b).symm⟩
    induction b
    · exact fun h => (WithBot.not_coe_le_bot _ h).elim
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩

lemma map'_mono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : Monotone f) :
    Monotone (map' f) := by simpa [Monotone, WithZero.forall]

lemma map'_strictMono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : StrictMono f) :
    StrictMono (map' f) := by simpa [StrictMono, WithZero.forall]

end Preorder

section PartialOrder
variable [PartialOrder α]

instance instPartialOrder : PartialOrder (WithZero α) := WithBot.partialOrder

instance instMulLeftReflectLT [Mul α] [MulLeftReflectLT α] :
    MulLeftReflectLT (WithZero α) := by
  refine ⟨fun a b c h => ?_⟩
  have := ((zero_le _).trans_lt h).ne'
  induction a
  · simp at this
  induction c
  · simp at this
  induction b
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

end PartialOrder

instance instLattice [Lattice α] : Lattice (WithZero α) := WithBot.lattice

section LinearOrder
variable [LinearOrder α] {a b c : α}

instance instLinearOrder : LinearOrder (WithZero α) := WithBot.linearOrder

protected lemma le_max_iff : (a : WithZero α) ≤ max (b : WithZero α) c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]

protected lemma min_le_iff : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]

end LinearOrder

instance isOrderedMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] :
    IsOrderedMonoid (WithZero α) where
  mul_le_mul_left := fun _ _ => mul_le_mul_left'

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `WithZero α` is an ordered `AddMonoid`. -/
-- See note [reducible non-instances]
protected lemma isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (zero_le : ∀ a : α, 0 ≤ a) :
    IsOrderedAddMonoid (WithZero α) where
  add_le_add_left := @add_le_add_left _ _ _ (WithZero.addLeftMono zero_le)

/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance instCanonicallyOrderedAdd [AddZeroClass α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedAdd (WithZero α) :=
  { WithZero.instExistsAddOfLE with
    le_self_add := fun a b => by
      induction a
      · exact bot_le
      induction b
      · exact le_rfl
      · exact WithZero.coe_le_coe.2 le_self_add }

instance instLinearOrderedCommMonoidWithZero [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] :
    LinearOrderedCommMonoidWithZero (WithZero α) where
  zero_le_one := WithZero.zero_le _

instance instLinearOrderedCommGroupWithZero [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] :
    LinearOrderedCommGroupWithZero (WithZero α) where

end WithZero

section MultiplicativeNotation

/-- Notation for `WithZero (Multiplicative ℕ)` -/
scoped[Multiplicative] notation "ℕₘ₀" => WithZero (Multiplicative ℕ)

/-- Notation for `WithZero (Multiplicative ℤ)` -/
scoped[Multiplicative] notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

end MultiplicativeNotation

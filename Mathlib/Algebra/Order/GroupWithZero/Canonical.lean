/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Algebra.Group.WithOne.Map

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
  elim a b c hbc := by dsimp only; by_contra! h; exact hbc.not_ge <| (mul_le_mul_iff_right₀ a.2).1 h

#adaptation_note /-- 2025-03-29 lean4#7717 Needed to add `dsimp only` -/
-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommGroupWithZero.toMulPosStrictMono :
    MulPosStrictMono α where
  elim a b c hbc := by dsimp only; by_contra! h; exact hbc.not_ge <| (mul_le_mul_iff_left₀ a.2).1 h

@[simp]
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  zero_lt_iff.2 u.ne_zero

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

instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) where
  neg_top := inv_zero (G₀ := α)
  add_neg_cancel := fun a ha ↦ mul_inv_cancel₀ (G₀ := α) (id ha : a.toMul ≠ 0)

instance : LinearOrderedAddCommGroupWithTop (Additive α)ᵒᵈ where
  neg_top := inv_zero (G₀ := α)
  add_neg_cancel := fun a ha ↦ mul_inv_cancel₀ (G₀ := α) (id ha : a.toMul ≠ 0)

-- Counterexample with monoid for the backward direction:
-- Take `Mᵐ⁰` where `M := ℚ ×ₗ ℕ`.
lemma denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units :
    DenselyOrdered α ↔ Nontrivial αˣ ∧ DenselyOrdered αˣ := by
  refine ⟨fun H ↦ ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_between (zero_lt_one' α)
    exact ⟨Units.mk0 x hx.ne', 1, by simpa [Units.ext_iff] using hx'.ne⟩
  · refine ⟨fun x y h ↦ ?_⟩
    obtain ⟨z, hz⟩ := exists_between (Units.val_lt_val.mpr h)
    refine ⟨Units.mk0 z (ne_zero_of_lt hz.1), by simp [← Units.val_lt_val, hz]⟩
  · refine ⟨fun x y h ↦ ?_⟩
    lift y to αˣ using (ne_zero_of_lt h).isUnit
    obtain rfl | hx := (zero_le' (a := x)).eq_or_lt
    · obtain ⟨z, hz⟩ := exists_one_lt' (α := αˣ)
      exact ⟨(y * z⁻¹ : αˣ), by simp, Units.val_lt_val.mpr <| by simp [hz]⟩
    · lift x to αˣ using hx.ne'.isUnit
      obtain ⟨z, hz, hz'⟩ := H₂.dense x y (Units.val_lt_val.mpr h)
      exact ⟨z, by simp [hz, hz']⟩

-- Counterexample with monoid: `{ x : ℝ | 0 ≤ x ≤ 1 }`
instance [DenselyOrdered α] : Nontrivial αˣ :=
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  by tauto

-- Counterexample with monoid:
-- `{ x : ℝ | x = 0 ∨ ∃ (a : ℤ) (b c : ℕ), x = Real.exp (a + b * √2 - c * √3) }`
instance [DenselyOrdered α] : DenselyOrdered αˣ :=
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  by tauto

lemma denselyOrdered_units_iff [Nontrivial αˣ] : DenselyOrdered αˣ ↔ DenselyOrdered α :=
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  by tauto

end LinearOrderedCommGroupWithZero

instance instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
    [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) where
  zero := Multiplicative.ofAdd (OrderDual.toDual ⊤)
  zero_mul := @top_add _ (_)
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

section Bot

instance instBot : Bot (WithZero α) :=
  ⟨none⟩

@[simp← ]
lemma zero_eq_bot : (0 : WithZero α) = ⊥ := rfl

end Bot

section Preorder

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

instance (priority := 10) le : LE (WithZero α) :=
  ⟨fun o₁ o₂ => ∀ a : α, o₁ = ↑a → ∃ b : α, o₂ = ↑b ∧ a ≤ b⟩

lemma le_def : x ≤ y ↔ ∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b := .rfl

@[simp, norm_cast] lemma coe_le_coe : (a : WithZero α) ≤ b ↔ a ≤ b := by simp [le_def]
@[simp] lemma zero_le (a : WithZero α) : 0 ≤ a := by simp [le_def]
@[simp] lemma not_coe_le_zero : ¬ a ≤ (0 : WithZero α) := by simp [le_def]

instance (priority := 10) lt : LT (WithZero α) :=
  ⟨fun o₁ o₂ : WithZero α => ∃ b : α, o₂ = ↑b ∧ ∀ a : α, o₁ = ↑a → a < b⟩

lemma lt_def : x < y ↔ ∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b := .rfl

@[simp, norm_cast] lemma coe_lt_coe : (a : WithZero α) < b ↔ a < b := by simp [lt_def]
@[simp] lemma zero_lt_coe (a : α) : 0 < (a : WithZero α) := by simp [lt_def]
@[simp] protected lemma not_lt_zero (a : WithZero α) : ¬a < 0 := by simp [lt_def]

instance instPreorder [Preorder α] : Preorder (WithZero α) where
  lt_iff_le_not_ge x y := by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

instance instOrderBot : OrderBot (WithZero α) where
  bot_le := by simp [le_def]

@[simp, norm_cast] lemma one_lt_coe [One α] : 1 < (a : WithZero α) ↔ 1 < a := coe_lt_coe

@[simp, norm_cast] lemma one_le_coe [One α] : 1 ≤ (a : WithZero α) ↔ 1 ≤ a := coe_le_coe

@[simp, norm_cast] lemma coe_lt_one [One α] : (a : WithZero α) < 1 ↔ a < 1 := coe_lt_coe

@[simp, norm_cast] lemma coe_le_one [One α] : (a : WithZero α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

theorem coe_le_iff {x : WithZero α} : (a : WithZero α) ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b := by
  simp [le_def]

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
    · exact fun h => (not_coe_le_zero h).elim
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩

lemma map'_mono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : Monotone f) :
    Monotone (map' f) := by simpa [Monotone, WithZero.forall]

lemma map'_strictMono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : StrictMono f) :
    StrictMono (map' f) := by simpa [StrictMono, WithZero.forall]

theorem exists_ne_zero_and_lt [NoMinOrder α] (hx : x ≠ 0) :
    ∃ y, y ≠ 0 ∧ y < x := by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe, WithZero.coe_unzero hx] at hlt
  exact ⟨z, WithZero.coe_ne_zero, hlt⟩

section Multiplicative

open Multiplicative

theorem toAdd_unzero_lt_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a < ofAdd b) :
    toAdd (unzero ha) < b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h

theorem lt_ofAdd_of_toAdd_unzero_lt
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) < b) :
    a < ofAdd b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]

theorem lt_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) :
    a < ofAdd b ↔ toAdd (unzero ha) < b :=
  ⟨toAdd_unzero_lt_of_lt_ofAdd ha, lt_ofAdd_of_toAdd_unzero_lt ha⟩

theorem toAdd_unzero_le_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a ≤ ofAdd b) :
    toAdd (unzero ha) ≤ b := by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h

theorem le_ofAdd_of_toAdd_unzero_le
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) ≤ b) :
    a ≤ ofAdd b := by
  rwa [← coe_unzero ha, coe_le_coe, ← ofAdd_toAdd (unzero ha), ofAdd_le]

theorem le_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) :
    a ≤ ofAdd b ↔ toAdd (unzero ha) ≤ b :=
  ⟨toAdd_unzero_le_of_lt_ofAdd ha, le_ofAdd_of_toAdd_unzero_le ha⟩

end Multiplicative

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


section Lattice

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithZero α) where
  sup
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | 0, 0 => 0
    | (a : α), 0 => a
    | 0, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithZero α) = (a : WithZero α) ⊔ b :=
  rfl

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithZero α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithZero α) = (a : WithZero α) ⊓ b :=
  rfl

instance instLattice [Lattice α] : Lattice (WithZero α) :=
  { WithZero.semilatticeSup, WithZero.semilatticeInf with }

end Lattice

instance decidableEq [DecidableEq α] : DecidableEq (WithZero α) :=
  inferInstanceAs <| DecidableEq (Option α)

instance decidableLE [Preorder α] [DecidableLE α] : DecidableLE (WithZero α)
  | 0, _ => isTrue <| by simp
  | (a : α), 0 => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

instance decidableLT [Preorder α] [DecidableLT α] : DecidableLT (WithZero α)
  | _, 0 => isFalse <| by simp
  | 0, (a : α) => isTrue <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe

instance isTotal_le [Preorder α] [IsTotal α (· ≤ ·)] : IsTotal (WithZero α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using IsTotal.total ..

section LinearOrder
variable [LinearOrder α] {a b c : α} {x y : WithZero α}

instance instLinearOrder : LinearOrder (WithZero α) := Lattice.toLinearOrder _

protected lemma le_max_iff : (a : WithZero α) ≤ max (b : WithZero α) c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]

protected lemma min_le_iff : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]

theorem exists_ne_zero_and_le_and_le (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z ≤ x ∧ z ≤ y :=
  ⟨x ⊓ y, by simp [min_eq_iff, hx, hy], by simp, by simp⟩

theorem exists_ne_zero_and_lt_and_lt [NoMinOrder α] (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z < x ∧ z < y := by
  obtain ⟨z', hnz', hzx, hzy⟩ := exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' ≤ _›

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
    CanonicallyOrderedAdd (WithZero α) where
  le_add_self
  | 0, _ => bot_le
  | (a : α), 0 => le_rfl
  | (a : α), (b : α) => WithZero.coe_le_coe.2 le_add_self
  le_self_add
  | 0, _ => bot_le
  | (a : α), 0 => le_rfl
  | (a : α), (b : α) => WithZero.coe_le_coe.2 le_self_add

instance instLinearOrderedCommMonoidWithZero [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] :
    LinearOrderedCommMonoidWithZero (WithZero α) where
  zero_le_one := WithZero.zero_le _

instance instLinearOrderedCommGroupWithZero [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] :
    LinearOrderedCommGroupWithZero (WithZero α) where

/-! ### Exponential and logarithm -/

variable {G : Type*} [Preorder G] {a b : G}

@[simp] lemma exp_le_exp : exp a ≤ exp b ↔ a ≤ b := by simp [exp]
@[simp] lemma exp_lt_exp : exp a < exp b ↔ a < b := by simp [exp]

@[simp] lemma exp_pos : 0 < exp a := by simp [exp]

variable [AddGroup G] {x y : Gᵐ⁰}

@[simp] lemma log_le_log (hx : x ≠ 0) (hy : y ≠ 0) : log x ≤ log y ↔ x ≤ y := by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; simp [log]

@[simp] lemma log_lt_log (hx : x ≠ 0) (hy : y ≠ 0) : log x < log y ↔ x < y := by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; simp [log]

lemma log_le_iff_le_exp (hx : x ≠ 0) : log x ≤ a ↔ x ≤ exp a := by
  lift x to Multiplicative G using hx; simpa [log, exp] using .rfl

lemma log_lt_iff_lt_exp (hx : x ≠ 0) : log x < a ↔ x < exp a := by
  lift x to Multiplicative G using hx; simpa [log, exp] using .rfl

lemma le_log_iff_exp_le (hx : x ≠ 0) : a ≤ log x ↔ exp a ≤ x := by
  lift x to Multiplicative G using hx; simpa [log, exp] using .rfl

lemma lt_log_iff_exp_lt (hx : x ≠ 0) : a < log x ↔ exp a < x := by
  lift x to Multiplicative G using hx; simpa [log, exp] using .rfl

lemma le_exp_of_log_le (hxa : log x ≤ a) : x ≤ exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_le_iff_le_exp, *]

lemma lt_exp_of_log_lt (hxa : log x < a) : x < exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_lt_iff_lt_exp, *]

lemma le_log_of_exp_le (hax : exp a ≤ x) : a ≤ log x :=
  (le_log_iff_exp_le (exp_pos.trans_le hax).ne').2 hax

lemma lt_log_of_exp_lt (hax : exp a < x) : a < log x :=
  (lt_log_iff_exp_lt (exp_pos.trans hax).ne').2 hax

/-- The exponential map as an order isomorphism between `G` and `Gᵐ⁰ˣ`. -/
@[simps!] def expOrderIso : G ≃o Gᵐ⁰ˣ where
  __ := expEquiv
  map_rel_iff' := by simp [← Units.val_le_val]

/-- The logarithm as an order isomorphism between `Gᵐ⁰ˣ` and `G`. -/
@[simps!] def logOrderIso : Gᵐ⁰ˣ ≃o G where
  __ := logEquiv
  map_rel_iff' := by simp

lemma lt_mul_exp_iff_le {x y : ℤᵐ⁰} (hy : y ≠ 0) : x < y * exp 1 ↔ x ≤ y := by
  lift y to Multiplicative ℤ using hy
  obtain rfl | hx := eq_or_ne x 0
  · simp
  lift x to Multiplicative ℤ using hx
  rw [← log_le_log, ← log_lt_log] <;> simp [log_mul, Int.lt_add_one_iff]

end WithZero

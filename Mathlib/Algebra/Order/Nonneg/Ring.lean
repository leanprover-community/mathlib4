/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.LatticeIntervals

#align_import algebra.order.nonneg.ring from "leanprover-community/mathlib"@"422e70f7ce183d2900c586a8cda8381e788a0c62"

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Main declarations

* `{x : α // 0 ≤ x}` is a `CanonicallyLinearOrderedAddMonoid` if `α` is a `LinearOrderedRing`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

open Set

variable {α : Type*}

namespace Nonneg

/-- This instance uses data fields from `Subtype.partialOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a ≤ x } :=
  { Set.Ici.orderBot with }
#align nonneg.order_bot Nonneg.orderBot

theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl
#align nonneg.bot_eq Nonneg.bot_eq

instance noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a ≤ x } :=
  show NoMaxOrder (Ici a) by infer_instance
                             -- 🎉 no goals
#align nonneg.no_max_order Nonneg.noMaxOrder

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a ≤ x } :=
  Set.Ici.semilatticeSup
#align nonneg.semilattice_sup Nonneg.semilatticeSup

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  Set.Ici.semilatticeInf
#align nonneg.semilattice_inf Nonneg.semilatticeInf

instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a ≤ x } :=
  Set.Ici.distribLattice
#align nonneg.distrib_lattice Nonneg.distribLattice

instance densely_ordered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a ≤ x } :=
  show DenselyOrdered (Ici a) from Set.instDenselyOrdered
#align nonneg.densely_ordered Nonneg.densely_ordered

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`. -/
@[reducible]
protected noncomputable def conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  { @ordConnectedSubsetConditionallyCompleteLinearOrder α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ with }
#align nonneg.conditionally_complete_linear_order Nonneg.conditionallyCompleteLinearOrder

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrderBot`.

This instance uses data fields from `Subtype.linearOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
@[reducible]
protected noncomputable def conditionallyCompleteLinearOrderBot [ConditionallyCompleteLinearOrder α]
    {a : α} (h : sSup ∅ ≤ a) : ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty :=
      (Function.funext_iff.1 (@subset_sSup_def α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩) ∅).trans <|
        Subtype.eq <| by
          rw [bot_eq]
          -- ⊢ ↑(if ht : sSup (Subtype.val '' ∅) ∈ Ici a then { val := sSup (Subtype.val '' …
          cases' h.lt_or_eq with h2 h2
          -- ⊢ ↑(if ht : sSup (Subtype.val '' ∅) ∈ Ici a then { val := sSup (Subtype.val '' …
          · simp [h2.not_le]
            -- 🎉 no goals
          simp [h2] }
          -- 🎉 no goals
#align nonneg.conditionally_complete_linear_order_bot Nonneg.conditionallyCompleteLinearOrderBot

instance inhabited [Preorder α] {a : α} : Inhabited { x : α // a ≤ x } :=
  ⟨⟨a, le_rfl⟩⟩
#align nonneg.inhabited Nonneg.inhabited

instance zero [Zero α] [Preorder α] : Zero { x : α // 0 ≤ x } :=
  ⟨⟨0, le_rfl⟩⟩
#align nonneg.has_zero Nonneg.zero

@[simp, norm_cast]
protected theorem coe_zero [Zero α] [Preorder α] : ((0 : { x : α // 0 ≤ x }) : α) = 0 :=
  rfl
#align nonneg.coe_zero Nonneg.coe_zero

@[simp]
theorem mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 0 ↔ x = 0 :=
  Subtype.ext_iff
#align nonneg.mk_eq_zero Nonneg.mk_eq_zero

instance add [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    Add { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩
#align nonneg.has_add Nonneg.add

@[simp]
theorem mk_add_mk [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] {x y : α}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
  rfl
#align nonneg.mk_add_mk Nonneg.mk_add_mk

@[simp, norm_cast]
protected theorem coe_add [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (a b : { x : α // 0 ≤ x }) : ((a + b : { x : α // 0 ≤ x }) : α) = a + b :=
  rfl
#align nonneg.coe_add Nonneg.coe_add

instance nsmul [AddMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    SMul ℕ { x : α // 0 ≤ x } :=
  ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩
#align nonneg.has_nsmul Nonneg.nsmul

@[simp]
theorem nsmul_mk [AddMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] (n : ℕ) {x : α}
    (hx : 0 ≤ x) : (n • (⟨x, hx⟩ : { x : α // 0 ≤ x })) = ⟨n • x, nsmul_nonneg hx n⟩ :=
  rfl
#align nonneg.nsmul_mk Nonneg.nsmul_mk

@[simp, norm_cast]
protected theorem coe_nsmul [AddMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (n : ℕ) (a : { x : α // 0 ≤ x }) : ((n • a : { x : α // 0 ≤ x }) : α) = n • (a : α) :=
  rfl
#align nonneg.coe_nsmul Nonneg.coe_nsmul

instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedAddCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.ordered_add_comm_monoid Nonneg.orderedAddCommMonoid

instance linearOrderedAddCommMonoid [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedAddCommMonoid _ Nonneg.coe_zero
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_add_comm_monoid Nonneg.linearOrderedAddCommMonoid

instance orderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] :
    OrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedCancelAddCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.ordered_cancel_add_comm_monoid Nonneg.orderedCancelAddCommMonoid

instance linearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid α] :
    LinearOrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedCancelAddCommMonoid _ Nonneg.coe_zero
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_cancel_add_comm_monoid Nonneg.linearOrderedCancelAddCommMonoid

/-- Coercion `{x : α // 0 ≤ x} → α` as an `AddMonoidHom`. -/
def coeAddMonoidHom [OrderedAddCommMonoid α] : { x : α // 0 ≤ x } →+ α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }
#align nonneg.coe_add_monoid_hom Nonneg.coeAddMonoidHom

@[norm_cast]
theorem nsmul_coe [OrderedAddCommMonoid α] (n : ℕ) (r : { x : α // 0 ≤ x }) :
    ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _
#align nonneg.nsmul_coe Nonneg.nsmul_coe

instance one [OrderedSemiring α] : One { x : α // 0 ≤ x } where one := ⟨1, zero_le_one⟩
#align nonneg.has_one Nonneg.one

@[simp, norm_cast]
protected theorem coe_one [OrderedSemiring α] : ((1 : { x : α // 0 ≤ x }) : α) = 1 :=
  rfl
#align nonneg.coe_one Nonneg.coe_one

@[simp]
theorem mk_eq_one [OrderedSemiring α] {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff
#align nonneg.mk_eq_one Nonneg.mk_eq_one

instance mul [OrderedSemiring α] : Mul { x : α // 0 ≤ x }
    where mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩
#align nonneg.has_mul Nonneg.mul

@[simp, norm_cast]
protected theorem coe_mul [OrderedSemiring α] (a b : { x : α // 0 ≤ x }) :
    ((a * b : { x : α // 0 ≤ x }) : α) = a * b :=
  rfl
#align nonneg.coe_mul Nonneg.coe_mul

@[simp]
theorem mk_mul_mk [OrderedSemiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl
#align nonneg.mk_mul_mk Nonneg.mk_mul_mk

instance addMonoidWithOne [OrderedSemiring α] : AddMonoidWithOne { x : α // 0 ≤ x } :=
  { Nonneg.one,
    Nonneg.orderedAddCommMonoid with
    natCast := fun n => ⟨n, Nat.cast_nonneg n⟩
    natCast_zero := by simp
                       -- 🎉 no goals
    natCast_succ := fun _ => by simp; rfl }
                                -- ⊢ { val := ↑x✝ + 1, property := (_ : (fun x => 0 ≤ x) (↑x✝ + 1)) } = { val :=  …
                                      -- 🎉 no goals
#align nonneg.add_monoid_with_one Nonneg.addMonoidWithOne

@[simp, norm_cast]
protected theorem coe_nat_cast [OrderedSemiring α] (n : ℕ) : ((↑n : { x : α // 0 ≤ x }) : α) = n :=
  rfl
#align nonneg.coe_nat_cast Nonneg.coe_nat_cast

@[simp]
theorem mk_nat_cast [OrderedSemiring α] (n : ℕ) : (⟨n, n.cast_nonneg⟩ : { x : α // 0 ≤ x }) = n :=
  rfl
#align nonneg.mk_nat_cast Nonneg.mk_nat_cast

instance pow [OrderedSemiring α] : Pow { x : α // 0 ≤ x } ℕ
    where pow x n := ⟨(x : α) ^ n, pow_nonneg x.2 n⟩
#align nonneg.has_pow Nonneg.pow

@[simp, norm_cast]
protected theorem coe_pow [OrderedSemiring α] (a : { x : α // 0 ≤ x }) (n : ℕ) :
    (↑(a ^ n) : α) = (a : α) ^ n :=
  rfl
#align nonneg.coe_pow Nonneg.coe_pow

@[simp]
theorem mk_pow [OrderedSemiring α] {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl
#align nonneg.mk_pow Nonneg.mk_pow

instance orderedSemiring [OrderedSemiring α] : OrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _=> rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
#align nonneg.ordered_semiring Nonneg.orderedSemiring

instance strictOrderedSemiring [StrictOrderedSemiring α] :
    StrictOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.strictOrderedSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.strict_ordered_semiring Nonneg.strictOrderedSemiring

instance orderedCommSemiring [OrderedCommSemiring α] : OrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedCommSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.ordered_comm_semiring Nonneg.orderedCommSemiring

instance strictOrderedCommSemiring [StrictOrderedCommSemiring α] :
    StrictOrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.strictOrderedCommSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.strict_ordered_comm_semiring Nonneg.strictOrderedCommSemiring

-- These prevent noncomputable instances being found, as it does not require `LinearOrder` which
-- is frequently non-computable.
instance monoidWithZero [OrderedSemiring α] : MonoidWithZero { x : α // 0 ≤ x } := by infer_instance
                                                                                      -- 🎉 no goals
#align nonneg.monoid_with_zero Nonneg.monoidWithZero

instance commMonoidWithZero [OrderedCommSemiring α] : CommMonoidWithZero { x : α // 0 ≤ x } := by
  infer_instance
  -- 🎉 no goals
#align nonneg.comm_monoid_with_zero Nonneg.commMonoidWithZero

instance semiring [OrderedSemiring α] : Semiring { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.semiring Nonneg.semiring

instance commSemiring [OrderedCommSemiring α] : CommSemiring { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.comm_semiring Nonneg.commSemiring

instance nontrivial [LinearOrderedSemiring α] : Nontrivial { x : α // 0 ≤ x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩
#align nonneg.nontrivial Nonneg.nontrivial

instance linearOrderedSemiring [LinearOrderedSemiring α] :
    LinearOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_semiring Nonneg.linearOrderedSemiring

instance linearOrderedCommMonoidWithZero [LinearOrderedCommRing α] :
    LinearOrderedCommMonoidWithZero { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemiring, Nonneg.orderedCommSemiring with
    mul_le_mul_left := fun _ _ h c ↦ mul_le_mul_of_nonneg_left h c.prop }
#align nonneg.linear_ordered_comm_monoid_with_zero Nonneg.linearOrderedCommMonoidWithZero

/-- Coercion `{x : α // 0 ≤ x} → α` as a `RingHom`. -/
def coeRingHom [OrderedSemiring α] : { x : α // 0 ≤ x } →+* α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }
#align nonneg.coe_ring_hom Nonneg.coeRingHom

instance canonicallyOrderedAddMonoid [OrderedRing α] :
    CanonicallyOrderedAddMonoid { x : α // 0 ≤ x } :=
  { Nonneg.orderedAddCommMonoid, Nonneg.orderBot with
    le_self_add := fun _ b => le_add_of_nonneg_right b.2
    exists_add_of_le := fun {a b} h =>
      ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel'_right _ _).symm⟩ }
#align nonneg.canonically_ordered_add_monoid Nonneg.canonicallyOrderedAddMonoid

instance canonicallyOrderedCommSemiring [OrderedCommRing α] [NoZeroDivisors α] :
    CanonicallyOrderedCommSemiring { x : α // 0 ≤ x } :=
  { Nonneg.canonicallyOrderedAddMonoid, Nonneg.orderedCommSemiring with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      -- ⊢ { val := a, property := ha } * { val := b, property := hb } = 0 → { val := a …
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self]}
      -- 🎉 no goals
#align nonneg.canonically_ordered_comm_semiring Nonneg.canonicallyOrderedCommSemiring

instance canonicallyLinearOrderedAddMonoid [LinearOrderedRing α] :
    CanonicallyLinearOrderedAddMonoid { x : α // 0 ≤ x } :=
  { Subtype.linearOrder _, Nonneg.canonicallyOrderedAddMonoid with }
#align nonneg.canonically_linear_ordered_add_monoid Nonneg.canonicallyLinearOrderedAddMonoid

section LinearOrder

variable [Zero α] [LinearOrder α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
def toNonneg (a : α) : { x : α // 0 ≤ x } :=
  ⟨max a 0, le_max_right _ _⟩
#align nonneg.to_nonneg Nonneg.toNonneg

@[simp]
theorem coe_toNonneg {a : α} : (toNonneg a : α) = max a 0 :=
  rfl
#align nonneg.coe_to_nonneg Nonneg.coe_toNonneg

@[simp]
theorem toNonneg_of_nonneg {a : α} (h : 0 ≤ a) : toNonneg a = ⟨a, h⟩ := by simp [toNonneg, h]
                                                                           -- 🎉 no goals
#align nonneg.to_nonneg_of_nonneg Nonneg.toNonneg_of_nonneg

@[simp]
theorem toNonneg_coe {a : { x : α // 0 ≤ x }} : toNonneg (a : α) = a :=
  toNonneg_of_nonneg a.2
#align nonneg.to_nonneg_coe Nonneg.toNonneg_coe

@[simp]
theorem toNonneg_le {a : α} {b : { x : α // 0 ≤ x }} : toNonneg a ≤ b ↔ a ≤ b := by
  cases' b with b hb
  -- ⊢ toNonneg a ≤ { val := b, property := hb } ↔ a ≤ ↑{ val := b, property := hb }
  simp [toNonneg, hb]
  -- 🎉 no goals
#align nonneg.to_nonneg_le Nonneg.toNonneg_le

@[simp]
theorem toNonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < toNonneg b ↔ ↑a < b := by
  cases' a with a ha
  -- ⊢ { val := a, property := ha } < toNonneg b ↔ ↑{ val := a, property := ha } < b
  simp [toNonneg, ha.not_lt]
  -- 🎉 no goals
#align nonneg.to_nonneg_lt Nonneg.toNonneg_lt

instance sub [Sub α] : Sub { x : α // 0 ≤ x } :=
  ⟨fun x y => toNonneg (x - y)⟩
#align nonneg.has_sub Nonneg.sub

@[simp]
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) - ⟨y, hy⟩ = toNonneg (x - y) :=
  rfl
#align nonneg.mk_sub_mk Nonneg.mk_sub_mk

end LinearOrder

instance orderedSub [LinearOrderedRing α] : OrderedSub { x : α // 0 ≤ x } :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    -- ⊢ { val := a, property := ha } - { val := b, property := hb } ≤ { val := c, pr …
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le,
      Subtype.coe_mk]⟩
#align nonneg.has_ordered_sub Nonneg.orderedSub

end Nonneg

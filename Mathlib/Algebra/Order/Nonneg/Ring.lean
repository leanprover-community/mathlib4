/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Data.Nat.Cast.Order
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

* `{x : α // 0 ≤ x}` is a `CanonicallyLinearOrderedAddCommMonoid` if `α` is a `LinearOrderedRing`.

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

instance instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a ≤ x } :=
  show DenselyOrdered (Ici a) from Set.instDenselyOrdered
#align nonneg.densely_ordered Nonneg.instDenselyOrdered

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`. -/
protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  { @ordConnectedSubsetConditionallyCompleteLinearOrder α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ with }
#align nonneg.conditionally_complete_linear_order Nonneg.conditionallyCompleteLinearOrder

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrderBot`.

This instance uses data fields from `Subtype.linearOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
protected noncomputable abbrev conditionallyCompleteLinearOrderBot
    [ConditionallyCompleteLinearOrder α] (a : α) :
    ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a, le_rfl⟩⟩]; simp [bot_eq] }
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

-- inlining this is problematic 🧐
def dubm [AddCommMonoid α] [OrderedAddCommMonoid α] : AddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

attribute [local instance] dubm

instance orderedAddCommMonoid [AddCommMonoid α] [OrderedAddCommMonoid α] :
    OrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedAddCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => by rfl
#align nonneg.ordered_add_comm_monoid Nonneg.orderedAddCommMonoid

instance linearOrderedAddCommMonoid [AddCommMonoid α] [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedAddCommMonoid _ Nonneg.coe_zero
    (fun _ _ => rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_add_comm_monoid Nonneg.linearOrderedAddCommMonoid

instance orderedCancelAddCommMonoid [AddCommMonoid α] [OrderedCancelAddCommMonoid α] :
    OrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedCancelAddCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => by rfl
#align nonneg.ordered_cancel_add_comm_monoid Nonneg.orderedCancelAddCommMonoid

instance linearOrderedCancelAddCommMonoid [AddCommMonoid α] [LinearOrderedCancelAddCommMonoid α] :
    LinearOrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedCancelAddCommMonoid _ Nonneg.coe_zero
    (fun _ _ => rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_cancel_add_comm_monoid Nonneg.linearOrderedCancelAddCommMonoid

/-- Coercion `{x : α // 0 ≤ x} → α` as an `AddMonoidHom`. -/
def coeAddMonoidHom [AddCommMonoid α] [OrderedAddCommMonoid α] : { x : α // 0 ≤ x } →+ α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }
#align nonneg.coe_add_monoid_hom Nonneg.coeAddMonoidHom

@[norm_cast]
theorem nsmul_coe [AddCommMonoid α] [OrderedAddCommMonoid α] (n : ℕ) (r : { x : α // 0 ≤ x }) :
    ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _
#align nonneg.nsmul_coe Nonneg.nsmul_coe

instance one [Semiring α] [OrderedSemiring α] : One { x : α // 0 ≤ x } where one := ⟨1, zero_le_one⟩
#align nonneg.has_one Nonneg.one

@[simp, norm_cast]
protected theorem coe_one [Semiring α] [OrderedSemiring α] : ((1 : { x : α // 0 ≤ x }) : α) = 1 :=
  rfl
#align nonneg.coe_one Nonneg.coe_one

@[simp]
theorem mk_eq_one [Semiring α] [OrderedSemiring α] {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff
#align nonneg.mk_eq_one Nonneg.mk_eq_one

instance mul [Semiring α] [OrderedSemiring α] : Mul { x : α // 0 ≤ x } where
  mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩
#align nonneg.has_mul Nonneg.mul

@[simp, norm_cast]
protected theorem coe_mul [Semiring α] [OrderedSemiring α] (a b : { x : α // 0 ≤ x }) :
    ((a * b : { x : α // 0 ≤ x }) : α) = a * b :=
  rfl
#align nonneg.coe_mul Nonneg.coe_mul

@[simp]
theorem mk_mul_mk [Semiring α] [OrderedSemiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl
#align nonneg.mk_mul_mk Nonneg.mk_mul_mk

instance addMonoidWithOne [Semiring α] [OrderedSemiring α] : AddMonoidWithOne { x : α // 0 ≤ x } :=
  { Nonneg.one,
    Nonneg.orderedAddCommMonoid (α := α) with
    natCast := fun n => ⟨n, Nat.cast_nonneg n⟩
    natCast_zero := by simp
    natCast_succ := fun _ => by ext; simp }
#align nonneg.add_monoid_with_one Nonneg.addMonoidWithOne

@[simp, norm_cast]
protected theorem coe_natCast [Semiring α] [OrderedSemiring α] (n : ℕ) : ((↑n : { x : α // 0 ≤ x }) : α) = n :=
  rfl
#align nonneg.coe_nat_cast Nonneg.coe_natCast

@[deprecated (since := "2024-04-17")]
alias coe_nat_cast := Nonneg.coe_natCast

@[simp]
theorem mk_natCast [Semiring α] [OrderedSemiring α] (n : ℕ) :
    (⟨n, n.cast_nonneg⟩ : { x : α // 0 ≤ x }) = n :=
  rfl
#align nonneg.mk_nat_cast Nonneg.mk_natCast

@[deprecated (since := "2024-04-17")]
alias mk_nat_cast := mk_natCast

instance pow [Semiring α] [OrderedSemiring α] : Pow { x : α // 0 ≤ x } ℕ where
  pow x n := ⟨(x : α) ^ n, pow_nonneg x.2 n⟩
#align nonneg.has_pow Nonneg.pow

@[simp, norm_cast]
protected theorem coe_pow [Semiring α] [OrderedSemiring α] (a : { x : α // 0 ≤ x }) (n : ℕ) :
    (↑(a ^ n) : α) = (a : α) ^ n :=
  rfl
#align nonneg.coe_pow Nonneg.coe_pow

@[simp]
theorem mk_pow [Semiring α] [OrderedSemiring α] {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl
#align nonneg.mk_pow Nonneg.mk_pow

-- cannot inline this
local instance [Semiring α] [OrderedSemiring α] : Semiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ => rfl

instance orderedSemiring [Semiring α] [OrderedSemiring α] :
    OrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _=> rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.ordered_semiring Nonneg.orderedSemiring

instance strictOrderedSemiring [Semiring α] [StrictOrderedSemiring α] :
    StrictOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.strictOrderedSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.strict_ordered_semiring Nonneg.strictOrderedSemiring

local instance [CommSemiring α] [OrderedCommSemiring α] : CommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance orderedCommSemiring [CommSemiring α] [OrderedCommSemiring α] : OrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.orderedCommSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.ordered_comm_semiring Nonneg.orderedCommSemiring

instance strictOrderedCommSemiring [CommSemiring α] [StrictOrderedCommSemiring α] :
    StrictOrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.strictOrderedCommSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rfl) (fun _ _ => rfl) fun _ => rfl
#align nonneg.strict_ordered_comm_semiring Nonneg.strictOrderedCommSemiring

-- These prevent noncomputable instances being found, as it does not require `LinearOrder` which
-- is frequently non-computable.
instance monoidWithZero [Semiring α] [OrderedSemiring α] : MonoidWithZero { x : α // 0 ≤ x } := by infer_instance
#align nonneg.monoid_with_zero Nonneg.monoidWithZero

instance commMonoidWithZero [CommSemiring α] [OrderedCommSemiring α] :
    CommMonoidWithZero { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.comm_monoid_with_zero Nonneg.commMonoidWithZero

instance semiring [Semiring α] [OrderedSemiring α] : Semiring { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.semiring Nonneg.semiring

instance commSemiring [CommSemiring α] [OrderedCommSemiring α] : CommSemiring { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.comm_semiring Nonneg.commSemiring

instance nontrivial [Semiring α] [LinearOrderedSemiring α] : Nontrivial { x : α // 0 ≤ x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩
#align nonneg.nontrivial Nonneg.nontrivial

instance linearOrderedSemiring [Semiring α] [LinearOrderedSemiring α] :
    LinearOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => by rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_semiring Nonneg.linearOrderedSemiring

instance linearOrderedCommMonoidWithZero [CommRing α] [LinearOrderedCommRing α] :
    LinearOrderedCommMonoidWithZero { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemiring, Nonneg.orderedCommSemiring (α := α) with
    mul_le_mul_left := fun _ _ h c ↦ mul_le_mul_of_nonneg_left h c.prop }
#align nonneg.linear_ordered_comm_monoid_with_zero Nonneg.linearOrderedCommMonoidWithZero

/-- Coercion `{x : α // 0 ≤ x} → α` as a `RingHom`. -/
def coeRingHom [Semiring α] [OrderedSemiring α] : { x : α // 0 ≤ x } →+* α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }
#align nonneg.coe_ring_hom Nonneg.coeRingHom

instance canonicallyOrderedAddCommMonoid [Ring α] [OrderedRing α] :
    CanonicallyOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  { Nonneg.orderedAddCommMonoid, Nonneg.orderBot with
    le_self_add := fun _ b => le_add_of_nonneg_right b.2
    exists_add_of_le := fun {a b} h =>
      ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩ }
#align nonneg.canonically_ordered_add_monoid Nonneg.canonicallyOrderedAddCommMonoid

instance canonicallyOrderedCommSemiring [CommRing α] [OrderedCommRing α] [NoZeroDivisors α] :
    CanonicallyOrderedCommSemiring { x : α // 0 ≤ x } :=
  { Nonneg.canonicallyOrderedAddCommMonoid, Nonneg.orderedCommSemiring (α := α) with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self]}
#align nonneg.canonically_ordered_comm_semiring Nonneg.canonicallyOrderedCommSemiring

private def dumb [Ring α] [LinearOrderedRing α] : AddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

instance canonicallyLinearOrderedAddCommMonoid [Ring α] [LinearOrderedRing α] :
    CanonicallyLinearOrderedAddCommMonoid { x : α // 0 ≤ x } where
  __ := dumb (α := α)
  __ := Subtype.instLinearOrder _
  __ := Nonneg.canonicallyOrderedAddCommMonoid
#align nonneg.canonically_linear_ordered_add_monoid Nonneg.canonicallyLinearOrderedAddCommMonoid

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
#align nonneg.to_nonneg_of_nonneg Nonneg.toNonneg_of_nonneg

@[simp]
theorem toNonneg_coe {a : { x : α // 0 ≤ x }} : toNonneg (a : α) = a :=
  toNonneg_of_nonneg a.2
#align nonneg.to_nonneg_coe Nonneg.toNonneg_coe

@[simp]
theorem toNonneg_le {a : α} {b : { x : α // 0 ≤ x }} : toNonneg a ≤ b ↔ a ≤ b := by
  cases' b with b hb
  simp [toNonneg, hb]
#align nonneg.to_nonneg_le Nonneg.toNonneg_le

@[simp]
theorem toNonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < toNonneg b ↔ ↑a < b := by
  cases' a with a ha
  simp [toNonneg, ha.not_lt]
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

instance orderedSub [Ring α] [LinearOrderedRing α] : OrderedSub { x : α // 0 ≤ x } :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le,
      Subtype.coe_mk]⟩
#align nonneg.has_ordered_sub Nonneg.orderedSub

end Nonneg

/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.LatticeIntervals

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

assert_not_exists OrderedCommMonoid

open Set

variable {α : Type*}

namespace Nonneg

/-- This instance uses data fields from `Subtype.partialOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a ≤ x } :=
  { Set.Ici.orderBot with }

theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl

instance noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a ≤ x } :=
  show NoMaxOrder (Ici a) by infer_instance

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a ≤ x } :=
  Set.Ici.semilatticeSup

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  Set.Ici.semilatticeInf

instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a ≤ x } :=
  Set.Ici.distribLattice

instance instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a ≤ x } :=
  show DenselyOrdered (Ici a) from Set.instDenselyOrdered

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`. -/
protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  { @ordConnectedSubsetConditionallyCompleteLinearOrder α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ with }

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

instance inhabited [Preorder α] {a : α} : Inhabited { x : α // a ≤ x } :=
  ⟨⟨a, le_rfl⟩⟩

instance zero [Zero α] [Preorder α] : Zero { x : α // 0 ≤ x } :=
  ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
protected theorem coe_zero [Zero α] [Preorder α] : ((0 : { x : α // 0 ≤ x }) : α) = 0 :=
  rfl

@[simp]
theorem mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 0 ↔ x = 0 :=
  Subtype.ext_iff

instance add [AddZeroClass α] [Preorder α] [AddLeftMono α] : Add { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]
theorem mk_add_mk [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
  rfl

@[simp, norm_cast]
protected theorem coe_add [AddZeroClass α] [Preorder α] [AddLeftMono α]
    (a b : { x : α // 0 ≤ x }) : ((a + b : { x : α // 0 ≤ x }) : α) = a + b :=
  rfl

instance nsmul [AddMonoid α] [Preorder α] [AddLeftMono α] : SMul ℕ { x : α // 0 ≤ x } :=
  ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩

@[simp]
theorem nsmul_mk [AddMonoid α] [Preorder α] [AddLeftMono α] (n : ℕ) {x : α}
    (hx : 0 ≤ x) : (n • (⟨x, hx⟩ : { x : α // 0 ≤ x })) = ⟨n • x, nsmul_nonneg hx n⟩ :=
  rfl

@[simp, norm_cast]
protected theorem coe_nsmul [AddMonoid α] [Preorder α] [AddLeftMono α]
    (n : ℕ) (a : { x : α // 0 ≤ x }) : ((n • a : { x : α // 0 ≤ x }) : α) = n • (a : α) :=
  rfl

section One

variable [Zero α] [One α] [LE α] [ZeroLEOneClass α]

instance one : One { x : α // 0 ≤ x } where
  one := ⟨1, zero_le_one⟩

@[simp, norm_cast]
protected theorem coe_one : ((1 : { x : α // 0 ≤ x }) : α) = 1 :=
  rfl

@[simp]
theorem mk_eq_one {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff

end One

section Mul

variable [MulZeroClass α] [Preorder α] [PosMulMono α]

instance mul : Mul { x : α // 0 ≤ x } where
  mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]
protected theorem coe_mul (a b : { x : α // 0 ≤ x }) :
    ((a * b : { x : α // 0 ≤ x }) : α) = a * b :=
  rfl

@[simp]
theorem mk_mul_mk {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl

end Mul

section AddMonoid

variable [AddMonoid α] [Preorder α] [AddLeftMono α]

instance addMonoid : AddMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.addMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

/-- Coercion `{x : α // 0 ≤ x} → α` as an `AddMonoidHom`. -/
def coeAddMonoidHom : { x : α // 0 ≤ x } →+ α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }

@[norm_cast]
theorem nsmul_coe (n : ℕ) (r : { x : α // 0 ≤ x }) :
    ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [Preorder α] [AddLeftMono α]

instance addCommMonoid : AddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCommMonoid

section AddMonoidWithOne

variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

instance natCast : NatCast { x : α // 0 ≤ x } :=
  ⟨fun n => ⟨n, Nat.cast_nonneg' n⟩⟩

@[simp, norm_cast]
protected theorem coe_natCast (n : ℕ) : ((↑n : { x : α // 0 ≤ x }) : α) = n :=
  rfl

@[deprecated (since := "2024-04-17")]
alias coe_nat_cast := Nonneg.coe_natCast

@[simp]
theorem mk_natCast (n : ℕ) : (⟨n, n.cast_nonneg'⟩ : { x : α // 0 ≤ x }) = n :=
  rfl

@[deprecated (since := "2024-04-17")]
alias mk_nat_cast := mk_natCast

instance addMonoidWithOne : AddMonoidWithOne { x : α // 0 ≤ x } :=
  { Nonneg.one (α := α) with
    toNatCast := Nonneg.natCast
    natCast_zero := by ext; simp
    natCast_succ := fun _ => by ext; simp }

end AddMonoidWithOne

section Pow

variable [MonoidWithZero α] [Preorder α] [ZeroLEOneClass α] [PosMulMono α]

@[simp]
theorem pow_nonneg {a : α} (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ a ^ n
  | 0 => by
    rw [pow_zero]
    exact zero_le_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_nonneg (pow_nonneg H _) H

instance pow : Pow { x : α // 0 ≤ x } ℕ where
  pow x n := ⟨(x : α) ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]
protected theorem coe_pow (a : { x : α // 0 ≤ x }) (n : ℕ) :
    (↑(a ^ n) : α) = (a : α) ^ n :=
  rfl

@[simp]
theorem mk_pow {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl

end Pow

section Semiring

variable [Semiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

instance semiring : Semiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _=> rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance monoidWithZero : MonoidWithZero { x : α // 0 ≤ x } := by infer_instance

/-- Coercion `{x : α // 0 ≤ x} → α` as a `RingHom`. -/
def coeRingHom : { x : α // 0 ≤ x } →+* α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }

end Semiring

section CommSemiring

variable [CommSemiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

instance commSemiring : CommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance commMonoidWithZero : CommMonoidWithZero { x : α // 0 ≤ x } := inferInstance

end CommSemiring

section LinearOrder

variable [Zero α] [LinearOrder α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
def toNonneg (a : α) : { x : α // 0 ≤ x } :=
  ⟨max a 0, le_max_right _ _⟩

@[simp]
theorem coe_toNonneg {a : α} : (toNonneg a : α) = max a 0 :=
  rfl

@[simp]
theorem toNonneg_of_nonneg {a : α} (h : 0 ≤ a) : toNonneg a = ⟨a, h⟩ := by simp [toNonneg, h]

@[simp]
theorem toNonneg_coe {a : { x : α // 0 ≤ x }} : toNonneg (a : α) = a :=
  toNonneg_of_nonneg a.2

@[simp]
theorem toNonneg_le {a : α} {b : { x : α // 0 ≤ x }} : toNonneg a ≤ b ↔ a ≤ b := by
  cases' b with b hb
  simp [toNonneg, hb]

@[simp]
theorem toNonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < toNonneg b ↔ ↑a < b := by
  cases' a with a ha
  simp [toNonneg, ha.not_lt]

instance sub [Sub α] : Sub { x : α // 0 ≤ x } :=
  ⟨fun x y => toNonneg (x - y)⟩

@[simp]
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) - ⟨y, hy⟩ = toNonneg (x - y) :=
  rfl

end LinearOrder

end Nonneg

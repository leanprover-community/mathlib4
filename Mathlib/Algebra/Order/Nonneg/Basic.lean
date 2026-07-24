/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`Nonneg α` of an arbitrary type `α`.

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

@[expose] public section
assert_not_exists GeneralizedHeytingAlgebra
assert_not_exists IsOrderedMonoid
-- TODO -- assert_not_exists PosMulMono
assert_not_exists mem_upperBounds

open Set

variable {α : Type*}

/-- The subtype of nonnegative elements. -/
abbrev Nonneg (α : Type*) [Zero α] [LE α] := { x : α // 0 ≤ x }

namespace Nonneg

instance inhabited [Preorder α] {a : α} : Inhabited { x : α // a ≤ x } :=
  ⟨⟨a, le_rfl⟩⟩

instance zero [Zero α] [Preorder α] : Zero (Nonneg α) :=
  ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
protected theorem coe_zero [Zero α] [Preorder α] : ((0 : Nonneg α) : α) = 0 :=
  rfl

@[simp]
theorem mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : Nonneg α) = 0 ↔ x = 0 :=
  Subtype.ext_iff

instance add [AddZeroClass α] [Preorder α] [AddLeftMono α] : Add (Nonneg α) :=
  ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]
theorem mk_add_mk [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : Nonneg α) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
  rfl

@[simp, norm_cast]
protected theorem coe_add [AddZeroClass α] [Preorder α] [AddLeftMono α]
    (a b : Nonneg α) : ((a + b : Nonneg α) : α) = a + b :=
  rfl

instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsLeftCancelAdd α] :
    IsLeftCancelAdd (Nonneg α) where
  add_left_cancel _ _ _ eq := Subtype.ext (add_left_cancel congr($eq))

instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsRightCancelAdd α] :
    IsRightCancelAdd (Nonneg α) where
  add_right_cancel _ _ _ eq := Subtype.ext (add_right_cancel congr($eq))

instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsCancelAdd α] :
    IsCancelAdd (Nonneg α) where

instance nsmul [AddMonoid α] [Preorder α] [AddLeftMono α] : SMul ℕ (Nonneg α) :=
  ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩

@[simp]
theorem nsmul_mk [AddMonoid α] [Preorder α] [AddLeftMono α] (n : ℕ) {x : α}
    (hx : 0 ≤ x) : (n • (⟨x, hx⟩ : Nonneg α)) = ⟨n • x, nsmul_nonneg hx n⟩ :=
  rfl

@[simp, norm_cast]
protected theorem coe_nsmul [AddMonoid α] [Preorder α] [AddLeftMono α]
    (n : ℕ) (a : Nonneg α) : ((n • a : Nonneg α) : α) = n • (a : α) :=
  rfl

section One

variable [Zero α] [One α] [LE α] [ZeroLEOneClass α]

instance one : One (Nonneg α) where
  one := ⟨1, zero_le_one⟩

@[simp, norm_cast]
protected theorem coe_one : ((1 : Nonneg α) : α) = 1 :=
  rfl

@[simp]
theorem mk_eq_one {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : Nonneg α) = 1 ↔ x = 1 :=
  Subtype.ext_iff

end One

section Mul

variable [MulZeroClass α] [Preorder α] [PosMulMono α]

instance mul : Mul (Nonneg α) where
  mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]
protected theorem coe_mul (a b : Nonneg α) :
    ((a * b : Nonneg α) : α) = a * b :=
  rfl

@[simp]
theorem mk_mul_mk {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : Nonneg α) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl

end Mul

section AddMonoid

variable [AddMonoid α] [Preorder α] [AddLeftMono α]

instance addMonoid : AddMonoid (Nonneg α) :=
  fast_instance% Subtype.coe_injective.addMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

/-- Coercion `Nonneg α → α` as an `AddMonoidHom`. -/
@[simps]
def coeAddMonoidHom : Nonneg α →+ α :=
  { toFun := ((↑) : Nonneg α → α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }

@[norm_cast]
theorem nsmul_coe (n : ℕ) (r : Nonneg α) :
    ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [Preorder α] [AddLeftMono α]

instance addCommMonoid : AddCommMonoid (Nonneg α) :=
  fast_instance%
    Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCommMonoid

section AddCancelCommMonoid
variable [AddCancelCommMonoid α] [Preorder α] [AddLeftMono α]

instance addCancelCommMonoid : AddCancelCommMonoid (Nonneg α) :=
  fast_instance%
    Subtype.coe_injective.addCancelCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCancelCommMonoid

section AddMonoidWithOne

variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

instance natCast : NatCast (Nonneg α) :=
  ⟨fun n => ⟨n, Nat.cast_nonneg' n⟩⟩

@[simp, norm_cast]
protected theorem coe_natCast (n : ℕ) : ((↑n : Nonneg α) : α) = n :=
  rfl

@[simp]
theorem mk_natCast (n : ℕ) : (⟨n, n.cast_nonneg'⟩ : Nonneg α) = n :=
  rfl

instance addMonoidWithOne : AddMonoidWithOne (Nonneg α) :=
  { Nonneg.one (α := α) with
    toNatCast := Nonneg.natCast
    natCast_zero := by ext; simp
    natCast_succ := fun _ => by ext; simp }

end AddMonoidWithOne

section Pow

variable [MonoidWithZero α] [Preorder α] [ZeroLEOneClass α] [PosMulMono α]

instance pow : Pow (Nonneg α) ℕ where
  pow x n := ⟨(x : α) ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]
protected theorem coe_pow (a : Nonneg α) (n : ℕ) :
    (↑(a ^ n) : α) = (a : α) ^ n :=
  rfl

@[simp]
theorem mk_pow {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : Nonneg α) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl

end Pow

section Semiring

variable [Semiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

instance semiring : Semiring (Nonneg α) :=
  fast_instance% Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance monoidWithZero : MonoidWithZero (Nonneg α) := by infer_instance

/-- Coercion `Nonneg α → α` as a `RingHom`. -/
def coeRingHom : Nonneg α →+* α :=
  { toFun := ((↑) : Nonneg α → α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }

end Semiring

section CommSemiring

variable [CommSemiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

instance commSemiring : CommSemiring (Nonneg α) :=
  fast_instance% Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance commMonoidWithZero : CommMonoidWithZero (Nonneg α) := inferInstance

end CommSemiring

section SemilatticeSup
variable [Zero α] [SemilatticeSup α]

/-- The function `a ↦ max a 0` of type `α → Nonneg α`. -/
def toNonneg (a : α) : (Nonneg α) :=
  ⟨max a 0, le_sup_right⟩

@[simp]
theorem coe_toNonneg {a : α} : (toNonneg a : α) = max a 0 :=
  rfl

@[simp]
theorem toNonneg_of_nonneg {a : α} (h : 0 ≤ a) : toNonneg a = ⟨a, h⟩ := by simp [toNonneg, h]

@[simp]
theorem toNonneg_coe {a : Nonneg α} : toNonneg (a : α) = a :=
  toNonneg_of_nonneg a.2

@[simp]
theorem toNonneg_le {a : α} {b : Nonneg α} : toNonneg a ≤ b ↔ a ≤ b := by
  obtain ⟨b, hb⟩ := b
  simp [toNonneg, hb]

instance sub [Sub α] : Sub (Nonneg α) :=
  ⟨fun x y => toNonneg (x - y)⟩

@[simp]
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : Nonneg α) - ⟨y, hy⟩ = toNonneg (x - y) :=
  rfl

end SemilatticeSup

section LinearOrder
variable [Zero α] [LinearOrder α]

@[simp]
theorem toNonneg_lt {a : Nonneg α} {b : α} : a < toNonneg b ↔ ↑a < b := by
  obtain ⟨a, ha⟩ := a
  simp [toNonneg, ha.not_gt]

end LinearOrder

end Nonneg

/-
Copyright (c) 2026 Hang Lu Su, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Order.Group.Opposite
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Left- and right-orderable monoids

A monoid `M` is *left-orderable* if it admits a linear order invariant under left multiplication
(`a ≤ b → c * a ≤ c * b`), *right-orderable* if it admits one invariant under right multiplication,
and *bi-orderable* if a single order is invariant under both left and right multiplication. This is
stronger than being both left- and right-orderable, since those may need different orders.

This file defines the `Prop`-valued classes
`IsLeftOrderable`, `IsRightOrderable` and `IsBiOrderable`, and the instances producing them from a
compatible `LinearOrder`.

## Main results

* `isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono`: a left-cancellative monoid is
  left-orderable iff it admits a *strictly* left-invariant linear order (and similarly on the
  right and both sides).
* `isLeftOrderable_mulOpposite_iff_isRightOrderable`: `M` is right-orderable iff the opposite
  monoid `Mᵐᵒᵖ` is left-orderable.
* `isLeftOrderable_iff_isRightOrderable`: a group is left-orderable iff it is right-orderable.

## Implementation notes

The classes are stated with `MulLeftMono` (`a ≤ b → c * a ≤ c * b`) rather than the strict
`MulLeftStrictMono` (`a < b → c * a < c * b`), and likewise on the right and both sides. The two
coincide on cancellative structures (such as groups): in a left-cancellative monoid a
multiplicative left-order is automatically strict.
-/

@[expose] public section

/-- An additive monoid is left-orderable if it admits a linear order invariant under left addition,
i.e. `a ≤ b → c + a ≤ c + b`. -/
@[mk_iff]
class IsAddLeftOrderable (M : Type*) [AddMonoid M] : Prop where
  exists_linearOrder_addLeftMono (M) : ∃ _ : LinearOrder M, AddLeftMono M

/-- A monoid is left-orderable if it admits a linear order invariant under left multiplication,
i.e. `a ≤ b → c * a ≤ c * b`. -/
@[to_additive existing, mk_iff]
class IsLeftOrderable (M : Type*) [Monoid M] : Prop where
  exists_linearOrder_mulLeftMono (M) : ∃ _ : LinearOrder M, MulLeftMono M

/-- An additive monoid is right-orderable if it admits a linear order invariant under right
addition, i.e. `a ≤ b → a + c ≤ b + c`. -/
@[mk_iff]
class IsAddRightOrderable (M : Type*) [AddMonoid M] : Prop where
  exists_linearOrder_addRightMono (M) : ∃ _ : LinearOrder M, AddRightMono M

/-- A monoid is right-orderable if it admits a linear order invariant under right multiplication,
i.e. `a ≤ b → a * c ≤ b * c`. -/
@[to_additive existing, mk_iff]
class IsRightOrderable (M : Type*) [Monoid M] : Prop where
  exists_linearOrder_mulRightMono (M) : ∃ _ : LinearOrder M, MulRightMono M

/-- An additive monoid is bi-orderable if it admits a linear order invariant under both left and
right addition. -/
@[mk_iff]
class IsAddBiOrderable (M : Type*) [AddMonoid M] : Prop where
  exists_linearOrder_addLeftMono_addRightMono (M) :
    ∃ _ : LinearOrder M, AddLeftMono M ∧ AddRightMono M

/-- A monoid is bi-orderable if it admits a linear order invariant under both left and right
multiplication. -/
@[to_additive existing, mk_iff]
class IsBiOrderable (M : Type*) [Monoid M] : Prop where
  exists_linearOrder_mulLeftMono_mulRightMono (M) :
    ∃ _ : LinearOrder M, MulLeftMono M ∧ MulRightMono M

export IsAddLeftOrderable (exists_linearOrder_addLeftMono)
export IsAddRightOrderable (exists_linearOrder_addRightMono)
export IsAddBiOrderable (exists_linearOrder_addLeftMono_addRightMono)
export IsLeftOrderable (exists_linearOrder_mulLeftMono)
export IsRightOrderable (exists_linearOrder_mulRightMono)
export IsBiOrderable (exists_linearOrder_mulLeftMono_mulRightMono)

variable {M : Type*} [Monoid M]

/-- A left-ordered monoid is left-orderable. -/
@[to_additive /-- A left-ordered additive monoid is left-orderable. -/]
instance [LinearOrder M] [MulLeftMono M] :
    IsLeftOrderable M := ⟨⟨‹_›, ‹_›⟩⟩

/-- A right-ordered monoid is right-orderable. -/
@[to_additive /-- A right-ordered additive monoid is right-orderable. -/]
instance [LinearOrder M] [MulRightMono M] :
    IsRightOrderable M := ⟨⟨‹_›, ‹_›⟩⟩

/-- A bi-ordered monoid is bi-orderable. -/
@[to_additive /-- A bi-ordered additive monoid is bi-orderable. -/]
instance [LinearOrder M] [MulLeftMono M] [MulRightMono M] :
    IsBiOrderable M := ⟨⟨‹_›, ‹_›, ‹_›⟩⟩

/-- A bi-orderable monoid is left-orderable. -/
@[to_additive /-- A bi-orderable additive monoid is left-orderable. -/]
instance [IsBiOrderable M] : IsLeftOrderable M := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono M
  infer_instance

/-- A bi-orderable monoid is right-orderable. -/
@[to_additive /-- A bi-orderable additive monoid is right-orderable. -/]
instance [IsBiOrderable M] : IsRightOrderable M := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono M
  infer_instance

/-- A left-cancellative monoid is left-orderable if and only if it admits a strictly
left-invariant linear order. -/
@[to_additive /-- A left-cancellative additive monoid is left-orderable if and only if it admits a
strictly left-invariant linear order. -/]
theorem isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono [IsLeftCancelMul M] :
    IsLeftOrderable M ↔ ∃ _ : LinearOrder M, MulLeftStrictMono M := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨‹LinearOrder M›, mulLeftMono_of_mulLeftStrictMono M⟩⟩
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono M
  exact ⟨‹LinearOrder M›, inferInstance⟩

/-- A right-cancellative monoid is right-orderable if and only if it admits a strictly
right-invariant linear order. -/
@[to_additive /-- A right-cancellative additive monoid is right-orderable if and only if it admits
a strictly right-invariant linear order. -/]
theorem isRightOrderable_iff_exists_linearOrder_mulRightStrictMono [IsRightCancelMul M] :
    IsRightOrderable M ↔ ∃ _ : LinearOrder M, MulRightStrictMono M := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨‹LinearOrder M›, mulRightMono_of_mulRightStrictMono M⟩⟩
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono M
  exact ⟨‹LinearOrder M›, inferInstance⟩

/-- A cancellative monoid is bi-orderable if and only if it admits a linear order that is
strictly left- and right-invariant. -/
@[to_additive /-- A cancellative additive monoid is bi-orderable if and only if it admits a linear
order that is strictly left- and right-invariant. -/]
theorem isBiOrderable_iff_exists_linearOrder_mulLeftStrictMono_mulRightStrictMono [IsCancelMul M] :
    IsBiOrderable M ↔ ∃ _ : LinearOrder M, MulLeftStrictMono M ∧ MulRightStrictMono M := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _, _⟩ ↦
    ⟨‹LinearOrder M›, mulLeftMono_of_mulLeftStrictMono M, mulRightMono_of_mulRightStrictMono M⟩⟩
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono M
  exact ⟨‹LinearOrder M›, inferInstance, inferInstance⟩

variable (M) in
/-- A left-cancellative, left-orderable monoid admits a linear order with strictly monotone left
multiplication. -/
@[to_additive /-- A left-cancellative, left-orderable additive monoid admits a linear order with
strictly monotone left addition. -/]
theorem exists_linearOrder_mulLeftStrictMono [IsLeftCancelMul M] [IsLeftOrderable M] :
    ∃ _ : LinearOrder M, MulLeftStrictMono M :=
  isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono.mp ‹_›

variable (M) in
/-- A right-cancellative, right-orderable monoid admits a linear order with strictly monotone right
multiplication. -/
@[to_additive /-- A right-cancellative, right-orderable additive monoid admits a linear order with
strictly monotone right addition. -/]
theorem exists_linearOrder_mulRightStrictMono [IsRightCancelMul M] [IsRightOrderable M] :
    ∃ _ : LinearOrder M, MulRightStrictMono M :=
  isRightOrderable_iff_exists_linearOrder_mulRightStrictMono.mp ‹_›

variable (M) in
/-- A cancellative, bi-orderable monoid admits a linear order that is strictly monotone under both
left and right multiplication. -/
@[to_additive /-- A cancellative, bi-orderable additive monoid admits a linear order that is
strictly monotone under both left and right addition. -/]
theorem exists_linearOrder_mulLeftStrictMono_mulRightStrictMono [IsCancelMul M] [IsBiOrderable M] :
    ∃ _ : LinearOrder M, MulLeftStrictMono M ∧ MulRightStrictMono M :=
  isBiOrderable_iff_exists_linearOrder_mulLeftStrictMono_mulRightStrictMono.mp ‹_›

variable {N : Type*} [Monoid N]

/-- Left-orderability is invariant under a monoid isomorphism `e : M ≃* N`. -/
@[to_additive /-- Left-orderability is invariant under an additive monoid isomorphism
`e : M ≃+ N`. -/]
theorem IsLeftOrderable.of_mulEquiv [IsLeftOrderable M] (e : M ≃* N) : IsLeftOrderable N := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono M
  refine ⟨.lift' e.symm e.symm.injective, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (c * a) ≤ e.symm (c * b)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Right-orderability is invariant under a monoid isomorphism `e : M ≃* N`. -/
@[to_additive /-- Right-orderability is invariant under an additive monoid isomorphism
`e : M ≃+ N`. -/]
theorem IsRightOrderable.of_mulEquiv [IsRightOrderable M] (e : M ≃* N) : IsRightOrderable N := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono M
  refine ⟨.lift' e.symm e.symm.injective, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (a * c) ≤ e.symm (b * c)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Bi-orderability is invariant under a monoid isomorphism `e : M ≃* N`. -/
@[to_additive /-- Bi-orderability is invariant under an additive monoid isomorphism
`e : M ≃+ N`. -/]
theorem IsBiOrderable.of_mulEquiv [IsBiOrderable M] (e : M ≃* N) : IsBiOrderable N := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono M
  refine ⟨.lift' e.symm e.symm.injective, ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩ <;>
  · change e.symm _ ≤ e.symm _
    rw [map_mul, map_mul]
    gcongr
    exact hab

/-- Left-orderability is invariant under monoid isomorphism. -/
@[to_additive /-- Left-orderability is invariant under additive monoid isomorphism. -/]
theorem MulEquiv.isLeftOrderable_congr (e : M ≃* N) : IsLeftOrderable M ↔ IsLeftOrderable N :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability is invariant under monoid isomorphism. -/
@[to_additive /-- Right-orderability is invariant under additive monoid isomorphism. -/]
theorem MulEquiv.isRightOrderable_congr (e : M ≃* N) : IsRightOrderable M ↔ IsRightOrderable N :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Bi-orderability is invariant under monoid isomorphism. -/
@[to_additive /-- Bi-orderability is invariant under additive monoid isomorphism. -/]
theorem MulEquiv.isBiOrderable_congr (e : M ≃* N) : IsBiOrderable M ↔ IsBiOrderable N :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability of `M` passes to left-orderability of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive /-- Right-orderability of `M` passes to left-orderability of the opposite additive
monoid `Mᵃᵒᵖ`. -/]
instance [IsRightOrderable M] : IsLeftOrderable Mᵐᵒᵖ := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono M
  refine ⟨inferInstance, ⟨fun c a b hab ↦ ?_⟩⟩
  change (c * a).unop ≤ (c * b).unop
  rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
  gcongr
  exact hab

/-- Left-orderability of `M` passes to right-orderability of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive /-- Left-orderability of `M` passes to right-orderability of the opposite additive
monoid `Mᵃᵒᵖ`. -/]
instance [IsLeftOrderable M] : IsRightOrderable Mᵐᵒᵖ := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono M
  refine ⟨inferInstance, ⟨fun c a b hab ↦ ?_⟩⟩
  change (a * c).unop ≤ (b * c).unop
  rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
  gcongr
  exact hab

/-- Bi-orderability of `M` passes to bi-orderability of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive /-- Bi-orderability of `M` passes to bi-orderability of the opposite additive
monoid `Mᵃᵒᵖ`. -/]
instance [IsBiOrderable M] : IsBiOrderable Mᵐᵒᵖ := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono M
  refine ⟨inferInstance, ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩ <;>
  · change (_ : Mᵐᵒᵖ).unop ≤ (_ : Mᵐᵒᵖ).unop
    rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
    gcongr
    exact hab

/-- Right-orderability of `M` passes to left-orderability of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive /-- Right-orderability of `M` passes to left-orderability of the opposite additive
monoid `Mᵃᵒᵖ`. -/]
theorem isLeftOrderable_mulOpposite_iff_isRightOrderable :
    IsLeftOrderable Mᵐᵒᵖ ↔ IsRightOrderable M :=
  ⟨fun _ ↦ (MulEquiv.opOp M).isRightOrderable_congr.mpr inferInstance, fun _ ↦ inferInstance⟩

/-- Left-orderability of `M` passes to right-orderability of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive /-- Left-orderability of `M` passes to right-orderability of the opposite additive
monoid `Mᵃᵒᵖ`. -/]
theorem isRightOrderable_mulOpposite_iff_isLeftOrderable :
    IsRightOrderable Mᵐᵒᵖ ↔ IsLeftOrderable M :=
  ⟨fun _ ↦ (MulEquiv.opOp M).isLeftOrderable_congr.mpr inferInstance, fun _ ↦ inferInstance⟩

/-- Bi-orderability of `M` passes to bi-orderability of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive /-- Bi-orderability of `M` passes to bi-orderability of the opposite additive
monoid `Mᵃᵒᵖ`. -/]
theorem isBiOrderable_mulOpposite_iff : IsBiOrderable Mᵐᵒᵖ ↔ IsBiOrderable M :=
  ⟨fun _ ↦ (MulEquiv.opOp M).isBiOrderable_congr.mpr inferInstance, fun _ ↦ inferInstance⟩

section Group
variable {G : Type*} [Group G]

/-- A group `G` is left-orderable iff it is right-orderable. -/
@[to_additive /-- An additive group `G` is left-orderable iff it is right-orderable. -/]
theorem isLeftOrderable_iff_isRightOrderable : IsLeftOrderable G ↔ IsRightOrderable G :=
  (MulEquiv.inv' G).isLeftOrderable_congr.trans isLeftOrderable_mulOpposite_iff_isRightOrderable

end Group

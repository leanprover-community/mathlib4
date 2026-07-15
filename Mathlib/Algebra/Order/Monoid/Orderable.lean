/-
Copyright (c) 2026 Hang Lu Su, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Left- and right-orderable monoids

A monoid `M` is *left-orderable* if it admits a linear order invariant under left multiplication
(`a ≤ b → c * a ≤ c * b`), *right-orderable* if it admits one invariant under right multiplication,
and *bi-orderable* if a single order is invariant under both — stronger than being both left- and
right-orderable, since those may need different orders. This file defines the `Prop`-valued classes
`IsLeftOrderable`, `IsRightOrderable` and `IsBiOrderable`, and the instances producing them from a
compatible `LinearOrder`. Their richer theory over a *group*, where the two one-sided notions
coincide, is developed in `Mathlib/GroupTheory/Orderable.lean`.

## Implementation notes

The classes are stated with `MulLeftMono` (`a ≤ b → c * a ≤ c * b`) rather than the strict
`MulLeftStrictMono` (`a < b → c * a < c * b`), and likewise on the right and both sides. The two
coincide on cancellative structures — in a left-cancellative monoid a `MulLeftMono` order is
automatically strict (`mulLeftStrictMono_iff_isLeftCancelMul`) — so over a group nothing is lost:
`IsLeftOrderable` can be recast in the strict form
`isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono`.

Off cancellative structures the non-strict form is strictly weaker, hence a more inclusive notion of
orderability and a lower bar to establish: for instance the two-element monoid `{0, 1}` with `0`
absorbing is `MulLeftMono` under `0 < 1` but not `MulLeftStrictMono`, since `0 * 0 = 0 * 1`.
-/

@[expose] public section

/-- An additive monoid is left-orderable if it admits a linear order invariant under left addition,
i.e. `a ≤ b → c + a ≤ c + b`. -/
@[mk_iff]
class IsAddLeftOrderable (G : Type*) [AddMonoid G] : Prop where
  exists_linearOrder_addLeftMono (G) : ∃ _ : LinearOrder G, AddLeftMono G

/-- A monoid is left-orderable if it admits a linear order invariant under left multiplication,
i.e. `a ≤ b → c * a ≤ c * b`. -/
@[to_additive existing IsAddLeftOrderable, mk_iff]
class IsLeftOrderable (G : Type*) [Monoid G] : Prop where
  exists_linearOrder_mulLeftMono (G) : ∃ _ : LinearOrder G, MulLeftMono G

/-- An additive monoid is right-orderable if it admits a linear order invariant under right
addition, i.e. `a ≤ b → a + c ≤ b + c`. -/
@[mk_iff]
class IsAddRightOrderable (G : Type*) [AddMonoid G] : Prop where
  exists_linearOrder_addRightMono (G) : ∃ _ : LinearOrder G, AddRightMono G

/-- A monoid is right-orderable if it admits a linear order invariant under right multiplication,
i.e. `a ≤ b → a * c ≤ b * c`. -/
@[to_additive existing IsAddRightOrderable, mk_iff]
class IsRightOrderable (G : Type*) [Monoid G] : Prop where
  exists_linearOrder_mulRightMono (G) : ∃ _ : LinearOrder G, MulRightMono G

/-- An additive monoid is bi-orderable if it admits a linear order invariant under both left and
right addition. -/
@[mk_iff]
class IsAddBiOrderable (G : Type*) [AddMonoid G] : Prop where
  exists_linearOrder_addLeftMono_addRightMono (G) :
    ∃ _ : LinearOrder G, AddLeftMono G ∧ AddRightMono G

/-- A monoid is bi-orderable if it admits a linear order invariant under both left and right
multiplication. -/
@[to_additive existing IsAddBiOrderable, mk_iff]
class IsBiOrderable (G : Type*) [Monoid G] : Prop where
  exists_linearOrder_mulLeftMono_mulRightMono (G) :
    ∃ _ : LinearOrder G, MulLeftMono G ∧ MulRightMono G

export IsAddLeftOrderable (exists_linearOrder_addLeftMono)
export IsAddRightOrderable (exists_linearOrder_addRightMono)
export IsAddBiOrderable (exists_linearOrder_addLeftMono_addRightMono)
export IsLeftOrderable (exists_linearOrder_mulLeftMono)
export IsRightOrderable (exists_linearOrder_mulRightMono)
export IsBiOrderable (exists_linearOrder_mulLeftMono_mulRightMono)

variable {G : Type*} [Monoid G]

/-- A linear order with monotone left multiplication makes a monoid left-orderable. -/
@[to_additive /-- A linear order with monotone left addition makes an additive monoid
left-orderable. -/]
instance MulLeftMono.to_isLeftOrderable [LinearOrder G] [MulLeftMono G] :
    IsLeftOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- A linear order with monotone right multiplication makes a monoid right-orderable. -/
@[to_additive /-- A linear order with monotone right addition makes an additive monoid
right-orderable. -/]
instance MulRightMono.to_isRightOrderable [LinearOrder G] [MulRightMono G] :
    IsRightOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- A linear order monotone under both multiplications makes a monoid bi-orderable. -/
@[to_additive /-- A linear order monotone under both additions makes an additive monoid
bi-orderable. -/]
instance MulLeftMono.to_isBiOrderable [LinearOrder G] [MulLeftMono G] [MulRightMono G] :
    IsBiOrderable G := ⟨⟨‹_›, ‹_›, ‹_›⟩⟩

/-- The strict counterpart of `MulLeftMono.to_isLeftOrderable`, a separate instance since
`MulLeftStrictMono` does not synthesize `MulLeftMono`. -/
@[to_additive /-- The strict counterpart of `AddLeftMono.to_isAddLeftOrderable`, a separate instance
since `AddLeftStrictMono` does not synthesize `AddLeftMono`. -/]
instance MulLeftStrictMono.to_isLeftOrderable [LinearOrder G] [MulLeftStrictMono G] :
    IsLeftOrderable G := ⟨⟨‹_›, mulLeftMono_of_mulLeftStrictMono G⟩⟩

/-- The strict counterpart of `MulRightMono.to_isRightOrderable`. -/
@[to_additive /-- The strict counterpart of `AddRightMono.to_isAddRightOrderable`. -/]
instance MulRightStrictMono.to_isRightOrderable [LinearOrder G] [MulRightStrictMono G] :
    IsRightOrderable G := ⟨⟨‹_›, mulRightMono_of_mulRightStrictMono G⟩⟩

/-- The strict counterpart of `MulLeftMono.to_isBiOrderable`. -/
@[to_additive /-- The strict counterpart of `AddLeftMono.to_isAddBiOrderable`. -/]
instance MulLeftStrictMono.to_isBiOrderable [LinearOrder G] [MulLeftStrictMono G]
    [MulRightStrictMono G] : IsBiOrderable G :=
  ⟨⟨‹_›, mulLeftMono_of_mulLeftStrictMono G, mulRightMono_of_mulRightStrictMono G⟩⟩

/-- A bi-orderable monoid is left-orderable. -/
@[to_additive /-- A bi-orderable additive monoid is left-orderable. -/]
instance IsBiOrderable.to_isLeftOrderable [IsBiOrderable G] : IsLeftOrderable G := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  infer_instance

/-- A bi-orderable monoid is right-orderable. -/
@[to_additive /-- A bi-orderable additive monoid is right-orderable. -/]
instance IsBiOrderable.to_isRightOrderable [IsBiOrderable G] : IsRightOrderable G := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  infer_instance

/-- On a linearly ordered monoid with monotone left multiplication, strict monotonicity of left
multiplication is equivalent to left-cancellativity. This is the precise sense in which the
non-strict `MulLeftMono` used by `IsLeftOrderable` agrees with the strict `MulLeftStrictMono` on
cancellative structures such as groups. -/
@[to_additive /-- On a linearly ordered additive monoid with monotone left addition, strict
monotonicity of left addition is equivalent to left-cancellativity. -/]
theorem mulLeftStrictMono_iff_isLeftCancelMul [LinearOrder G] [MulLeftMono G] :
    MulLeftStrictMono G ↔ IsLeftCancelMul G :=
  ⟨fun _ ↦ MulLeftStrictMono.toIsLeftCancelMul, fun _ ↦ inferInstance⟩

/-- On a linearly ordered monoid with monotone right multiplication, strict monotonicity of right
multiplication is equivalent to right-cancellativity. -/
@[to_additive /-- On a linearly ordered additive monoid with monotone right addition, strict
monotonicity of right addition is equivalent to right-cancellativity. -/]
theorem mulRightStrictMono_iff_isRightCancelMul [LinearOrder G] [MulRightMono G] :
    MulRightStrictMono G ↔ IsRightCancelMul G :=
  ⟨fun _ ↦ MulRightStrictMono.toIsRightCancelMul, fun _ ↦ inferInstance⟩

/-- Over a left-cancellative monoid the defining `MulLeftMono` of `IsLeftOrderable` may be taken
strict, recovering the standard formulation `a < b → c * a < c * b`. -/
@[to_additive /-- Over a left-cancellative additive monoid the defining `AddLeftMono` of
`IsAddLeftOrderable` may be taken strict, recovering the standard formulation
`a < b → c + a < c + b`. -/]
theorem isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono [IsLeftCancelMul G] :
    IsLeftOrderable G ↔ ∃ _ : LinearOrder G, MulLeftStrictMono G := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G⟩⟩
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
  exact ⟨‹LinearOrder G›, inferInstance⟩

/-- Over a right-cancellative monoid the defining `MulRightMono` of `IsRightOrderable` may be taken
strict, recovering the standard formulation `a < b → a * c < b * c`. -/
@[to_additive /-- Over a right-cancellative additive monoid the defining `AddRightMono` of
`IsAddRightOrderable` may be taken strict, recovering the standard formulation
`a < b → a + c < b + c`. -/]
theorem isRightOrderable_iff_exists_linearOrder_mulRightStrictMono [IsRightCancelMul G] :
    IsRightOrderable G ↔ ∃ _ : LinearOrder G, MulRightStrictMono G := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulRightMono_of_mulRightStrictMono G⟩⟩
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
  exact ⟨‹LinearOrder G›, inferInstance⟩

/-- Over a cancellative monoid the defining monotonicity of `IsBiOrderable` may be taken strict on
both sides. -/
@[to_additive /-- Over a cancellative additive monoid the defining monotonicity of
`IsAddBiOrderable` may be taken strict on both sides. -/]
theorem isBiOrderable_iff_exists_linearOrder_mulLeftStrictMono_mulRightStrictMono [IsCancelMul G] :
    IsBiOrderable G ↔ ∃ _ : LinearOrder G, MulLeftStrictMono G ∧ MulRightStrictMono G := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _, _⟩ ↦
    ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G, mulRightMono_of_mulRightStrictMono G⟩⟩
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  exact ⟨‹LinearOrder G›, inferInstance, inferInstance⟩

variable (G) in
@[to_additive]
theorem exists_linearOrder_mulLeftStrictMono [IsLeftCancelMul G] [IsLeftOrderable G] :
    ∃ _ : LinearOrder G, MulLeftStrictMono G :=
  isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono.mp ‹_›

variable (G) in
@[to_additive]
theorem exists_linearOrder_mulRightStrictMono [IsRightCancelMul G] [IsRightOrderable G] :
    ∃ _ : LinearOrder G, MulRightStrictMono G :=
  isRightOrderable_iff_exists_linearOrder_mulRightStrictMono.mp ‹_›

variable (G) in
@[to_additive]
theorem exists_linearOrder_mulLeftStrictMono_mulRightStrictMono [IsCancelMul G] [IsBiOrderable G] :
    ∃ _ : LinearOrder G, MulLeftStrictMono G ∧ MulRightStrictMono G :=
  isBiOrderable_iff_exists_linearOrder_mulLeftStrictMono_mulRightStrictMono.mp ‹_›

variable {H : Type*} [Monoid H]

/-- Left-orderability transports along a monoid isomorphism `e : G ≃* H`. -/
@[to_additive]
theorem IsLeftOrderable.of_mulEquiv [IsLeftOrderable G] (e : G ≃* H) : IsLeftOrderable H := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
  let : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (c * a) ≤ e.symm (c * b)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Right-orderability transports along a monoid isomorphism `e : G ≃* H`. -/
@[to_additive]
theorem IsRightOrderable.of_mulEquiv [IsRightOrderable G] (e : G ≃* H) : IsRightOrderable H := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
  let : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (a * c) ≤ e.symm (b * c)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Bi-orderability transports along a monoid isomorphism `e : G ≃* H`. -/
@[to_additive]
theorem IsBiOrderable.of_mulEquiv [IsBiOrderable G] (e : G ≃* H) : IsBiOrderable H := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  let : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩
  · change e.symm (c * a) ≤ e.symm (c * b)
    rw [map_mul, map_mul]
    gcongr
    exact hab
  · change e.symm (a * c) ≤ e.symm (b * c)
    rw [map_mul, map_mul]
    gcongr
    exact hab

/-- Left-orderability is invariant under monoid isomorphism. -/
@[to_additive AddEquiv.isAddLeftOrderable_congr]
theorem MulEquiv.isLeftOrderable_congr (e : G ≃* H) : IsLeftOrderable G ↔ IsLeftOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability is invariant under monoid isomorphism. -/
@[to_additive AddEquiv.isAddRightOrderable_congr]
theorem MulEquiv.isRightOrderable_congr (e : G ≃* H) : IsRightOrderable G ↔ IsRightOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Bi-orderability is invariant under monoid isomorphism. -/
@[to_additive AddEquiv.isAddBiOrderable_congr]
theorem MulEquiv.isBiOrderable_congr (e : G ≃* H) : IsBiOrderable G ↔ IsBiOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability of `G` is the same as left-orderability of the opposite monoid `Gᵐᵒᵖ`, since
right multiplication on `G` is left multiplication on `Gᵐᵒᵖ`. -/
@[to_additive isAddLeftOrderable_addOpposite_iff_isAddRightOrderable]
theorem isLeftOrderable_mulOpposite_iff_isRightOrderable :
    IsLeftOrderable Gᵐᵒᵖ ↔ IsRightOrderable G := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono Gᵐᵒᵖ
    refine ⟨LinearOrder.lift' MulOpposite.op MulOpposite.op_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change MulOpposite.op (a * c) ≤ MulOpposite.op (b * c)
    rw [MulOpposite.op_mul, MulOpposite.op_mul]
    gcongr
    exact hab
  · obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
    refine ⟨LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change (c * a).unop ≤ (c * b).unop
    rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
    gcongr
    exact hab

/-- Left-orderability of `G` is the same as right-orderability of the opposite monoid `Gᵐᵒᵖ`, since
left multiplication on `G` is right multiplication on `Gᵐᵒᵖ`. -/
@[to_additive isAddRightOrderable_addOpposite_iff_isAddLeftOrderable]
theorem isRightOrderable_mulOpposite_iff_isLeftOrderable :
    IsRightOrderable Gᵐᵒᵖ ↔ IsLeftOrderable G := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono Gᵐᵒᵖ
    refine ⟨LinearOrder.lift' MulOpposite.op MulOpposite.op_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change MulOpposite.op (c * a) ≤ MulOpposite.op (c * b)
    rw [MulOpposite.op_mul, MulOpposite.op_mul]
    gcongr
    exact hab
  · obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
    refine ⟨LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change (a * c).unop ≤ (b * c).unop
    rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
    gcongr
    exact hab

/-- Bi-orderability transfers to the opposite monoid `Gᵐᵒᵖ`, since left and right multiplication on
`G` are respectively right and left multiplication on `Gᵐᵒᵖ`. -/
@[to_additive isAddBiOrderable_addOpposite_iff]
theorem isBiOrderable_mulOpposite_iff : IsBiOrderable Gᵐᵒᵖ ↔ IsBiOrderable G := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono Gᵐᵒᵖ
    refine ⟨LinearOrder.lift' MulOpposite.op MulOpposite.op_injective,
      ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩
    · change MulOpposite.op (c * a) ≤ MulOpposite.op (c * b)
      rw [MulOpposite.op_mul, MulOpposite.op_mul]
      gcongr
      exact hab
    · change MulOpposite.op (a * c) ≤ MulOpposite.op (b * c)
      rw [MulOpposite.op_mul, MulOpposite.op_mul]
      gcongr
      exact hab
  · obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
    refine ⟨LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective,
      ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩
    · change (c * a).unop ≤ (c * b).unop
      rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
      gcongr
      exact hab
    · change (a * c).unop ≤ (b * c).unop
      rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
      gcongr
      exact hab

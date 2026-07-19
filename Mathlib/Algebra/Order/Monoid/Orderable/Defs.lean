/-
Copyright (c) 2026 Hang Lu Su, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Opposite
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
compatible `LinearOrder`. Their richer theory over a *group*, where the two one-sided notions
coincide, is developed in the final section.

## Implementation notes

The classes are stated with `MulLeftMono` (`a ≤ b → c * a ≤ c * b`) rather than the strict
`MulLeftStrictMono` (`a < b → c * a < c * b`), and likewise on the right and both sides. The two
coincide on cancellative structures: in a left-cancellative monoid a `MulLeftMono` order is
automatically strict (`mulLeftStrictMono_iff_isLeftCancelMul`). Over a group nothing is lost:
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
@[to_additive existing, mk_iff]
class IsLeftOrderable (G : Type*) [Monoid G] : Prop where
  exists_linearOrder_mulLeftMono (G) : ∃ _ : LinearOrder G, MulLeftMono G

/-- An additive monoid is right-orderable if it admits a linear order invariant under right
addition, i.e. `a ≤ b → a + c ≤ b + c`. -/
@[mk_iff]
class IsAddRightOrderable (G : Type*) [AddMonoid G] : Prop where
  exists_linearOrder_addRightMono (G) : ∃ _ : LinearOrder G, AddRightMono G

/-- A monoid is right-orderable if it admits a linear order invariant under right multiplication,
i.e. `a ≤ b → a * c ≤ b * c`. -/
@[to_additive existing, mk_iff]
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
@[to_additive existing, mk_iff]
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

/-- A left-ordered monoid is left-orderable. -/
@[to_additive /-- A left-ordered additive monoid is left-orderable. -/]
instance [LinearOrder G] [MulLeftMono G] :
    IsLeftOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- A right-ordered monoid is right-orderable. -/
@[to_additive /-- A right-ordered additive monoid is right-orderable. -/]
instance [LinearOrder G] [MulRightMono G] :
    IsRightOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- A bi-ordered monoid is bi-orderable. -/
@[to_additive /-- A bi-ordered additive monoid is bi-orderable. -/]
instance [LinearOrder G] [MulLeftMono G] [MulRightMono G] :
    IsBiOrderable G := ⟨⟨‹_›, ‹_›, ‹_›⟩⟩

/-- A linear order with strict monotone left-multiplication is left-orderable. -/
@[to_additive /-- A linear order with strict monotone left-addition is left-orderable. -/]
instance [LinearOrder G] [MulLeftStrictMono G] :
    IsLeftOrderable G := ⟨⟨‹_›, mulLeftMono_of_mulLeftStrictMono G⟩⟩

/-- A linear order with strict monotone right-multiplication is right-orderable. -/
@[to_additive /-- A linear order with strict monotone right-addition is right-orderable. -/]
instance [LinearOrder G] [MulRightStrictMono G] :
    IsRightOrderable G := ⟨⟨‹_›, mulRightMono_of_mulRightStrictMono G⟩⟩

/-- A linear order with strict monotone left- and right-multiplication is bi-orderable. -/
@[to_additive /-- A linear order with strict monotone left- and right-addition is bi-orderable. -/]
instance [LinearOrder G] [MulLeftStrictMono G]
    [MulRightStrictMono G] : IsBiOrderable G :=
  ⟨⟨‹_›, mulLeftMono_of_mulLeftStrictMono G, mulRightMono_of_mulRightStrictMono G⟩⟩

/-- A bi-orderable monoid is left-orderable. -/
@[to_additive /-- A bi-orderable additive monoid is left-orderable. -/]
instance [IsBiOrderable G] : IsLeftOrderable G := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  infer_instance

/-- A bi-orderable monoid is right-orderable. -/
@[to_additive /-- A bi-orderable additive monoid is right-orderable. -/]
instance [IsBiOrderable G] : IsRightOrderable G := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  infer_instance

/-- On a left-ordered monoid, strict monotonicity of left multiplication is equivalent to
left-cancellativity. This is the precise sense in which the non-strict `MulLeftMono` used by
`IsLeftOrderable` agrees with the strict `MulLeftStrictMono` on cancellative structures such as
groups. -/
@[to_additive /-- On a left-ordered additive monoid, strict monotonicity of left addition is
equivalent to left-cancellativity. -/]
theorem mulLeftStrictMono_iff_isLeftCancelMul [LinearOrder G] [MulLeftMono G] :
    MulLeftStrictMono G ↔ IsLeftCancelMul G :=
  ⟨fun _ ↦ MulLeftStrictMono.toIsLeftCancelMul, fun _ ↦ inferInstance⟩

/-- On a right-ordered monoid, strict monotonicity of right multiplication is equivalent to
right-cancellativity. -/
@[to_additive /-- On a right-ordered additive monoid, strict monotonicity of right addition is
equivalent to right-cancellativity. -/]
theorem mulRightStrictMono_iff_isRightCancelMul [LinearOrder G] [MulRightMono G] :
    MulRightStrictMono G ↔ IsRightCancelMul G :=
  ⟨fun _ ↦ MulRightStrictMono.toIsRightCancelMul, fun _ ↦ inferInstance⟩

/-- Over a left-cancellative monoid the defining `MulLeftMono` of `IsLeftOrderable` may be taken
strict, recovering the formulation `a < b → c * a < c * b`. -/
@[to_additive /-- Over a left-cancellative additive monoid the defining `AddLeftMono` of
`IsAddLeftOrderable` may be taken strict, recovering the formulation `a < b → c + a < c + b`. -/]
theorem isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono [IsLeftCancelMul G] :
    IsLeftOrderable G ↔ ∃ _ : LinearOrder G, MulLeftStrictMono G := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G⟩⟩
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
  exact ⟨‹LinearOrder G›, inferInstance⟩

/-- Over a right-cancellative monoid the defining `MulRightMono` of `IsRightOrderable` may be taken
strict, recovering the formulation `a < b → a * c < b * c`. -/
@[to_additive /-- Over a right-cancellative additive monoid the defining `AddRightMono` of
`IsAddRightOrderable` may be taken strict, recovering the formulation `a < b → a + c < b + c`. -/]
theorem isRightOrderable_iff_exists_linearOrder_mulRightStrictMono [IsRightCancelMul G] :
    IsRightOrderable G ↔ ∃ _ : LinearOrder G, MulRightStrictMono G := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulRightMono_of_mulRightStrictMono G⟩⟩
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
  exact ⟨‹LinearOrder G›, inferInstance⟩

/-- Over a cancellative monoid the defining monotonicity of `IsBiOrderable` may be taken strict on
both sides, recovering the formulations `a < b → c * a < c * b` and `a < b → a * c < b * c`. -/
@[to_additive /-- Over a cancellative additive monoid the defining monotonicity of
`IsAddBiOrderable` may be taken strict on both sides, recovering the formulations
`a < b → c + a < c + b` and `a < b → a + c < b + c`. -/]
theorem isBiOrderable_iff_exists_linearOrder_mulLeftStrictMono_mulRightStrictMono [IsCancelMul G] :
    IsBiOrderable G ↔ ∃ _ : LinearOrder G, MulLeftStrictMono G ∧ MulRightStrictMono G := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _, _⟩ ↦
    ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G, mulRightMono_of_mulRightStrictMono G⟩⟩
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  exact ⟨‹LinearOrder G›, inferInstance, inferInstance⟩

variable (G) in
/-- A left-cancellative, left-orderable monoid admits a linear order with strictly monotone left
multiplication. -/
@[to_additive /-- A left-cancellative, left-orderable additive monoid admits a linear order with
strictly monotone left addition. -/]
theorem exists_linearOrder_mulLeftStrictMono [IsLeftCancelMul G] [IsLeftOrderable G] :
    ∃ _ : LinearOrder G, MulLeftStrictMono G :=
  isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono.mp ‹_›

variable (G) in
/-- A right-cancellative, right-orderable monoid admits a linear order with strictly monotone right
multiplication. -/
@[to_additive /-- A right-cancellative, right-orderable additive monoid admits a linear order with
strictly monotone right addition. -/]
theorem exists_linearOrder_mulRightStrictMono [IsRightCancelMul G] [IsRightOrderable G] :
    ∃ _ : LinearOrder G, MulRightStrictMono G :=
  isRightOrderable_iff_exists_linearOrder_mulRightStrictMono.mp ‹_›

variable (G) in
/-- A cancellative, bi-orderable monoid admits a linear order that is strictly monotone under both
left and right multiplication. -/
@[to_additive /-- A cancellative, bi-orderable additive monoid admits a linear order that is
strictly monotone under both left and right addition. -/]
theorem exists_linearOrder_mulLeftStrictMono_mulRightStrictMono [IsCancelMul G] [IsBiOrderable G] :
    ∃ _ : LinearOrder G, MulLeftStrictMono G ∧ MulRightStrictMono G :=
  isBiOrderable_iff_exists_linearOrder_mulLeftStrictMono_mulRightStrictMono.mp ‹_›

variable {H : Type*} [Monoid H]

/-- Left-orderability transports along a monoid isomorphism `e : G ≃* H`. -/
@[to_additive /-- Left-orderability transports along an additive monoid isomorphism
`e : G ≃+ H`. -/]
theorem IsLeftOrderable.of_mulEquiv [IsLeftOrderable G] (e : G ≃* H) : IsLeftOrderable H := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
  let : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (c * a) ≤ e.symm (c * b)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Right-orderability transports along a monoid isomorphism `e : G ≃* H`. -/
@[to_additive /-- Right-orderability transports along an additive monoid isomorphism
`e : G ≃+ H`. -/]
theorem IsRightOrderable.of_mulEquiv [IsRightOrderable G] (e : G ≃* H) : IsRightOrderable H := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
  let : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (a * c) ≤ e.symm (b * c)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Bi-orderability transports along a monoid isomorphism `e : G ≃* H`. -/
@[to_additive /-- Bi-orderability transports along an additive monoid isomorphism
`e : G ≃+ H`. -/]
theorem IsBiOrderable.of_mulEquiv [IsBiOrderable G] (e : G ≃* H) : IsBiOrderable H := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  let : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩ <;>
    · change e.symm _ ≤ e.symm _
      rw [map_mul, map_mul]
      gcongr
      exact hab

/-- Left-orderability is invariant under monoid isomorphism. -/
@[to_additive /-- Left-orderability is invariant under additive monoid isomorphism. -/]
theorem MulEquiv.isLeftOrderable_congr (e : G ≃* H) : IsLeftOrderable G ↔ IsLeftOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability is invariant under monoid isomorphism. -/
@[to_additive /-- Right-orderability is invariant under additive monoid isomorphism. -/]
theorem MulEquiv.isRightOrderable_congr (e : G ≃* H) : IsRightOrderable G ↔ IsRightOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Bi-orderability is invariant under monoid isomorphism. -/
@[to_additive /-- Bi-orderability is invariant under additive monoid isomorphism. -/]
theorem MulEquiv.isBiOrderable_congr (e : G ≃* H) : IsBiOrderable G ↔ IsBiOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability of `G` transfers to left-orderability of the opposite monoid `Gᵐᵒᵖ`, since
right multiplication on `G` is left multiplication on `Gᵐᵒᵖ`. -/
@[to_additive /-- Right-orderability of `G` transfers to left-orderability of the opposite additive
monoid `Gᵃᵒᵖ`, since right addition on `G` is left addition on `Gᵃᵒᵖ`. -/]
instance [IsRightOrderable G] : IsLeftOrderable Gᵐᵒᵖ := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
  refine ⟨LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective, ⟨fun c a b hab ↦ ?_⟩⟩
  change (c * a).unop ≤ (c * b).unop
  rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
  gcongr
  exact hab

/-- Left-orderability of `G` transfers to right-orderability of the opposite monoid `Gᵐᵒᵖ`, since
left multiplication on `G` is right multiplication on `Gᵐᵒᵖ`. -/
@[to_additive /-- Left-orderability of `G` transfers to right-orderability of the opposite additive
monoid `Gᵃᵒᵖ`, since left addition on `G` is right addition on `Gᵃᵒᵖ`. -/]
instance [IsLeftOrderable G] : IsRightOrderable Gᵐᵒᵖ := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
  refine ⟨LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective, ⟨fun c a b hab ↦ ?_⟩⟩
  change (a * c).unop ≤ (b * c).unop
  rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
  gcongr
  exact hab

/-- Bi-orderability of `G` transfers to bi-orderability of the opposite monoid `Gᵐᵒᵖ`, since left
and right multiplication on `G` are respectively right and left multiplication on `Gᵐᵒᵖ`. -/
@[to_additive /-- Bi-orderability of `G` transfers to bi-orderability of the opposite additive
monoid `Gᵃᵒᵖ`, since left and right addition on `G` are respectively right and left addition on
`Gᵃᵒᵖ`. -/]
instance [IsBiOrderable G] : IsBiOrderable Gᵐᵒᵖ := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftMono_mulRightMono G
  refine ⟨LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective,
    ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩ <;>
  · change (_ : Gᵐᵒᵖ).unop ≤ (_ : Gᵐᵒᵖ).unop
    rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
    gcongr
    exact hab

/-- Right-orderability of `G` is the same as left-orderability of the opposite monoid `Gᵐᵒᵖ`, since
right multiplication on `G` is left multiplication on `Gᵐᵒᵖ`. -/
@[to_additive /-- Right-orderability of `G` is the same as left-orderability of the opposite
additive monoid `Gᵃᵒᵖ`, since right addition on `G` is left addition on `Gᵃᵒᵖ`. -/]
theorem isLeftOrderable_mulOpposite_iff_isRightOrderable :
    IsLeftOrderable Gᵐᵒᵖ ↔ IsRightOrderable G :=
  ⟨fun _ ↦ (MulEquiv.opOp G).isRightOrderable_congr.mpr inferInstance, fun _ ↦ inferInstance⟩

/-- Left-orderability of `G` is the same as right-orderability of the opposite monoid `Gᵐᵒᵖ`, since
left multiplication on `G` is right multiplication on `Gᵐᵒᵖ`. -/
@[to_additive /-- Left-orderability of `G` is the same as right-orderability of the opposite
additive monoid `Gᵃᵒᵖ`, since left addition on `G` is right addition on `Gᵃᵒᵖ`. -/]
theorem isRightOrderable_mulOpposite_iff_isLeftOrderable :
    IsRightOrderable Gᵐᵒᵖ ↔ IsLeftOrderable G :=
  ⟨fun _ ↦ (MulEquiv.opOp G).isLeftOrderable_congr.mpr inferInstance, fun _ ↦ inferInstance⟩

/-- Bi-orderability of `G` is the same as bi-orderability of the opposite monoid `Gᵐᵒᵖ`, since left
and right multiplication on `G` are respectively right and left multiplication on `Gᵐᵒᵖ`. -/
@[to_additive /-- Bi-orderability of `G` is the same as bi-orderability of the opposite additive
monoid `Gᵃᵒᵖ`, since left and right addition on `G` are respectively right and left addition on
`Gᵃᵒᵖ`. -/]
theorem isBiOrderable_mulOpposite_iff : IsBiOrderable Gᵐᵒᵖ ↔ IsBiOrderable G :=
  ⟨fun _ ↦ (MulEquiv.opOp G).isBiOrderable_congr.mpr inferInstance, fun _ ↦ inferInstance⟩

section Group
variable {G : Type*} [Group G]

/-- A group `G` is left-orderable iff it is right-orderable, since inversion `x ↦ x⁻¹` is a
multiplicative anti-automorphism, realised as the isomorphism `MulEquiv.inv' : G ≃* Gᵐᵒᵖ`. -/
@[to_additive /-- An additive group `G` is left-orderable iff it is right-orderable, since negation
`x ↦ -x` is an additive anti-automorphism, realised as the isomorphism
`AddEquiv.inv' : G ≃+ Gᵃᵒᵖ`. -/]
theorem isLeftOrderable_iff_isRightOrderable : IsLeftOrderable G ↔ IsRightOrderable G :=
  (MulEquiv.inv' G).isLeftOrderable_congr.trans isLeftOrderable_mulOpposite_iff_isRightOrderable

end Group

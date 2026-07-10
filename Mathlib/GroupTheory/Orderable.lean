/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Left- and right-orderable groups

A group `G` is *left-orderable* if it admits a linear order invariant under left multiplication,
i.e. `a < b → c * a < c * b`, and *right-orderable* if it admits one invariant under right
multiplication, i.e. `a < b → a * c < b * c`. This file defines the `Prop`-valued classes
`IsLeftOrderable G` and `IsRightOrderable G`, asserting the existence of such an order, and shows
that the two notions coincide. It also defines `IsBiOrderable G`, asserting the existence of a
single order invariant under both left and right multiplication; this is strictly stronger than
being both left- and right-orderable, since the latter may be witnessed by different orders.

## Main declarations

* `IsLeftOrderable G`: `G` admits some strict total `LinearOrder` for which left multiplication is
strictly monotone (`MulLeftStrictMono`).
* `IsRightOrderable G`: likewise for right multiplication (`MulRightStrictMono`).
* `IsBiOrderable G`: `G` admits some strict total `LinearOrder` for which both left and right
multiplication are strictly monotone.
* `isLeftOrderable_iff_isRightOrderable`: a group is left-orderable iff it is right-orderable.
* `IsLeftOrderable.of_mulEquiv`, `MulEquiv.isLeftOrderable_congr`: left-orderability transports
  along, and is invariant under, group isomorphism.
* `Prod.instIsLeftOrderable`, `Pi.instIsLeftOrderable`: left-orderability is closed under direct and
  arbitrary indexed products.

## Implementation notes

`IsLeftOrderable` erases the witnessing order into `Prop`. Recover a (noncomputable) `LinearOrder`
instance from `IsLeftOrderable.exists_linearOrder_mulLeftStrictMono`.

The class is stated with `MulLeftStrictMono` rather than `MulLeftMono`: over a linearly ordered
group the two are equivalent, but the strict version is the standard mathematical notation.

Although `IsLeftOrderable` and `IsRightOrderable` are equivalent, neither direction of
`isLeftOrderable_iff_isRightOrderable` is an instance, since the two together would loop. The
right-handed results are therefore proved separately, by transporting along the bridge.
-/

@[expose] public section

variable {G H : Type*} [Group G] [Group H]

/-! ### Definitions -/

/-- A group is left-orderable if it admits a linear order invariant under left multiplication,
i.e. `a < b → c * a < c * b`. -/
@[mk_iff]
class IsLeftOrderable (G : Type*) [Group G] : Prop where
  exists_linearOrder_mulLeftStrictMono (G) : ∃ _ : LinearOrder G, MulLeftStrictMono G

/-- A group is right-orderable if it admits a linear order invariant under right multiplication,
i.e. `a < b → a * c < b * c`. -/
@[mk_iff]
class IsRightOrderable (G : Type*) [Group G] : Prop where
  exists_linearOrder_mulRightStrictMono (G) : ∃ _ : LinearOrder G, MulRightStrictMono G

/-- A group is bi-orderable if it admits a linear order invariant under both left and right
multiplication, i.e. `a < b → c * a < c * b` and `a < b → a * c < b * c`. -/
@[mk_iff]
class IsBiOrderable (G : Type*) [Group G] : Prop where
  exists_linearOrder_mulLeftStrictMono_mulRightStrictMono (G) :
    ∃ _ : LinearOrder G, MulLeftStrictMono G ∧ MulRightStrictMono G

export IsLeftOrderable (exists_linearOrder_mulLeftStrictMono)
export IsRightOrderable (exists_linearOrder_mulRightStrictMono)
export IsBiOrderable (exists_linearOrder_mulLeftStrictMono_mulRightStrictMono)

/-- A group with a linear order and strictly monotone left multiplication (`MulLeftStrictMono`) is
left-orderable. -/
instance MulLeftStrictMono.to_isLeftOrderable [LinearOrder G] [MulLeftStrictMono G] :
    IsLeftOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- A group with a linear order and strictly monotone right multiplication (`MulRightStrictMono`) is
right-orderable. -/
instance MulRightStrictMono.to_isRightOrderable [LinearOrder G] [MulRightStrictMono G] :
    IsRightOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- A group with a linear order that is strictly monotone under both left and right multiplication
(`MulLeftStrictMono`, `MulRightStrictMono`) is bi-orderable. -/
instance MulLeftStrictMono.to_isBiOrderable [LinearOrder G] [MulLeftStrictMono G]
    [MulRightStrictMono G] : IsBiOrderable G := ⟨⟨‹_›, ‹_›, ‹_›⟩⟩

/-- A bi-orderable group is left-orderable. -/
instance IsBiOrderable.to_isLeftOrderable [IsBiOrderable G] : IsLeftOrderable G := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftStrictMono_mulRightStrictMono G
  infer_instance

/-- A bi-orderable group is right-orderable. -/
instance IsBiOrderable.to_isRightOrderable [IsBiOrderable G] : IsRightOrderable G := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftStrictMono_mulRightStrictMono G
  infer_instance

/-- `IsLeftOrderable G` holds iff `G` admits a linear order with monotone left multiplication. -/
theorem isLeftOrderable_iff_exists_linearOrder_mulLeftMono :
    IsLeftOrderable G ↔ ∃ _ : LinearOrder G, MulLeftMono G := by
  rw [isLeftOrderable_iff]
  refine ⟨fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G⟩,
    fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, inferInstance⟩⟩

/-- `IsRightOrderable G` holds iff `G` admits a linear order with monotone right multiplication. -/
theorem isRightOrderable_iff_exists_linearOrder_mulRightMono :
    IsRightOrderable G ↔ ∃ _ : LinearOrder G, MulRightMono G := by
  rw [isRightOrderable_iff]
  refine ⟨fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulRightMono_of_mulRightStrictMono G⟩,
    fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, inferInstance⟩⟩

/-- `IsBiOrderable G` holds iff `G` admits a linear order with monotone left and right
multiplication. -/
theorem isBiOrderable_iff_exists_linearOrder_mulLeftMono_mulRightMono :
    IsBiOrderable G ↔ ∃ _ : LinearOrder G, MulLeftMono G ∧ MulRightMono G := by
  rw [isBiOrderable_iff]
  refine ⟨fun ⟨_, _, _⟩ ↦ ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G,
      mulRightMono_of_mulRightStrictMono G⟩,
    fun ⟨_, _, _⟩ ↦ ⟨‹LinearOrder G›, inferInstance, inferInstance⟩⟩

variable (G) in
theorem exists_linearOrder_mulLeftMono [IsLeftOrderable G] :
    ∃ _ : LinearOrder G, MulLeftMono G :=
  isLeftOrderable_iff_exists_linearOrder_mulLeftMono.mp ‹_›

variable (G) in
theorem exists_linearOrder_mulRightMono [IsRightOrderable G] :
    ∃ _ : LinearOrder G, MulRightMono G :=
  isRightOrderable_iff_exists_linearOrder_mulRightMono.mp ‹_›

variable (G) in
theorem exists_linearOrder_mulLeftMono_mulRightMono [IsBiOrderable G] :
    ∃ _ : LinearOrder G, MulLeftMono G ∧ MulRightMono G :=
  isBiOrderable_iff_exists_linearOrder_mulLeftMono_mulRightMono.mp ‹_›

/-- A group is left-orderable iff it is right-orderable. -/
theorem isLeftOrderable_iff_isRightOrderable : IsLeftOrderable G ↔ IsRightOrderable G := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨_, _⟩ := exists_linearOrder_mulLeftStrictMono G
    refine ⟨LinearOrder.lift' (·⁻¹) inv_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change (a * c)⁻¹ < (b * c)⁻¹
    rw [mul_inv_rev, mul_inv_rev]
    gcongr
    exact hab
  · obtain ⟨_, _⟩ := exists_linearOrder_mulRightStrictMono G
    refine ⟨LinearOrder.lift' (·⁻¹) inv_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change (c * a)⁻¹ < (c * b)⁻¹
    rw [mul_inv_rev, mul_inv_rev]
    gcongr
    exact hab

/-- Left-orderability transports along a group isomorphism `e : G ≃* H`. -/
theorem IsLeftOrderable.of_mulEquiv [IsLeftOrderable G] (e : G ≃* H) : IsLeftOrderable H := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftStrictMono G
  letI : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (c * a) < e.symm (c * b)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Right-orderability transports along a group isomorphism `e : G ≃* H`. -/
theorem IsRightOrderable.of_mulEquiv [h : IsRightOrderable G] (e : G ≃* H) :
    IsRightOrderable H := by
  rw [← isLeftOrderable_iff_isRightOrderable] at h ⊢
  exact .of_mulEquiv e

/-- Bi-orderability transports along a group isomorphism `e : G ≃* H`. -/
theorem IsBiOrderable.of_mulEquiv [IsBiOrderable G] (e : G ≃* H) : IsBiOrderable H := by
  obtain ⟨_, _, _⟩ := exists_linearOrder_mulLeftStrictMono_mulRightStrictMono G
  letI : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩, ⟨fun c a b hab ↦ ?_⟩⟩
  · change e.symm (c * a) < e.symm (c * b)
    rw [map_mul, map_mul]
    gcongr
    exact hab
  · change e.symm (a * c) < e.symm (b * c)
    rw [map_mul, map_mul]
    gcongr
    exact hab

/-- Left-orderability is invariant under group isomorphism. -/
theorem MulEquiv.isLeftOrderable_congr (e : G ≃* H) : IsLeftOrderable G ↔ IsLeftOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Right-orderability is invariant under group isomorphism. -/
theorem MulEquiv.isRightOrderable_congr (e : G ≃* H) : IsRightOrderable G ↔ IsRightOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- Bi-orderability is invariant under group isomorphism. -/
theorem MulEquiv.isBiOrderable_congr (e : G ≃* H) : IsBiOrderable G ↔ IsBiOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- The direct product of two left-orderable groups is left-orderable. -/
instance Prod.instIsLeftOrderable [IsLeftOrderable G] [IsLeftOrderable H] :
    IsLeftOrderable (G × H) := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftStrictMono G
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono H
  exact .of_mulEquiv (ofLexMulEquiv (G × H))

/-- The direct product of two right-orderable groups is right-orderable. -/
instance Prod.instIsRightOrderable [hG : IsRightOrderable G] [hH : IsRightOrderable H] :
    IsRightOrderable (G × H) := by
  rw [← isLeftOrderable_iff_isRightOrderable] at hG hH ⊢
  infer_instance

/-- An arbitrary indexed product of left-orderable groups is left-orderable. -/
instance Pi.instIsLeftOrderable {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, IsLeftOrderable (G i)] : IsLeftOrderable (∀ i, G i) := by
  choose l hl using fun i ↦ exists_linearOrder_mulLeftStrictMono (G i)
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  exact .of_mulEquiv (ofLexMulEquiv (∀ i, G i))

/-- An arbitrary indexed product of right-orderable groups is right-orderable. -/
instance Pi.instIsRightOrderable {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] [h : ∀ i, IsRightOrderable (G i)] : IsRightOrderable (∀ i, G i) := by
  simp only [← isLeftOrderable_iff_isRightOrderable] at h ⊢
  infer_instance

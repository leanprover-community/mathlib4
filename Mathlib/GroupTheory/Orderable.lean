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
# Left-orderable groups

A group `G` is *left-orderable* if it admits a linear order invariant under left multiplication,
i.e. `a ≤ b → c * a ≤ c * b`. This file defines the `Prop`-valued class `IsLeftOrderable G`,
asserting the existence of such an order.

## Main declarations

* `IsLeftOrderable G`: `G` admits some `LinearOrder` for which left multiplication is monotone
  (`MulLeftMono`).
* `isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono`: the same with *strict* monotonicity.
* `IsLeftOrderable.of_mulEquiv`, `MulEquiv.isLeftOrderable_congr`: left-orderability transports
  along, and is invariant under, group isomorphism.
* `IsLeftOrderable.prod`, `IsLeftOrderable.pi`: left-orderability is closed under direct and
  arbitrary indexed products.

## Implementation notes

`IsLeftOrderable` erases the witnessing order into `Prop`. Recover a (noncomputable) `LinearOrder`
instance from `IsLeftOrderable.exists_linearOrder_mulLeftMono`.
-/

@[expose] public section

variable {G H : Type*} [Group G] [Group H]

/-- A group is left-orderable if it admits a linear order invariant under left multiplication. -/
@[mk_iff]
class IsLeftOrderable (G : Type*) [Group G] : Prop where
  exists_linearOrder_mulLeftMono (G) : ∃ _ : LinearOrder G, MulLeftMono G

export IsLeftOrderable (exists_linearOrder_mulLeftMono)

/-- A group with a linear order and monotone left multiplication (`MulLeftMono`) is
left-orderable. -/
instance MulLeftMono.to_isLeftOrderable [LinearOrder G] [MulLeftMono G] : IsLeftOrderable G
  := ⟨⟨‹_›, ‹_›⟩⟩

/-- `IsLeftOrderable G` holds iff `G` admits a linear order with strictly monotone left
multiplication. -/
theorem isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono :
    IsLeftOrderable G ↔ ∃ _ : LinearOrder G, MulLeftStrictMono G := by
  rw [isLeftOrderable_iff]
  refine ⟨fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, inferInstance⟩,
    fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G⟩⟩

variable (G) in
theorem exists_linearOrder_mulLeftStrictMono [IsLeftOrderable G] :
    ∃ _ : LinearOrder G, MulLeftStrictMono G :=
  isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono.mp ‹_›

/-- Left-orderability transports along a group isomorphism `e : G ≃* H`. -/
theorem IsLeftOrderable.of_mulEquiv [IsLeftOrderable G] (e : G ≃* H) : IsLeftOrderable H := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
  letI : LinearOrder H := LinearOrder.lift' e.symm e.symm.injective
  refine ⟨‹LinearOrder H›, ⟨fun c a b hab ↦ ?_⟩⟩
  change e.symm (c * a) ≤ e.symm (c * b)
  rw [map_mul, map_mul]
  gcongr
  exact hab

/-- Left-orderability is invariant under group isomorphism. -/
theorem MulEquiv.isLeftOrderable_congr (e : G ≃* H) : IsLeftOrderable G ↔ IsLeftOrderable H :=
  ⟨fun _ ↦ .of_mulEquiv e, fun _ ↦ .of_mulEquiv e.symm⟩

/-- The direct product of two left-orderable groups is left-orderable. -/
instance Prod.instIsLeftOrderable [IsLeftOrderable G] [IsLeftOrderable H] :
    IsLeftOrderable (G × H) := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftStrictMono G
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono H
  exact .of_mulEquiv (ofLexMulEquiv (G × H))

/-- An arbitrary indexed product of left-orderable groups is left-orderable. -/
instance Pi.instIsLeftOrderable {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, IsLeftOrderable (G i)] : IsLeftOrderable (∀ i, G i) := by
  choose l hl using fun i ↦ exists_linearOrder_mulLeftStrictMono (G i)
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  exact .of_mulEquiv (ofLexMulEquiv (∀ i, G i))

/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
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
i.e. `a ≤ b → c * a ≤ c * b`. This file defines the `Prop`-valued class `IsLeftOrderable G`, which
records the mere *existence* of such an order.

## Main declarations

* `IsLeftOrderable G`: `G` admits some `LinearOrder` for which left multiplication is monotone
  (`MulLeftMono`), together with the instance producing it from any concrete compatible linear order
  on `G`.
* `isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono`: equivalently, some linear order for
  which left multiplication is *strictly* monotone.
* `IsLeftOrderable.of_mulEquiv`, `MulEquiv.isLeftOrderable_congr`: left-orderability transports
  along, and is invariant under, group isomorphism.
* `IsLeftOrderable.prod`: `IsLeftOrderable` is closed under direct products.
* `IsLeftOrderable.pi`: `IsLeftOrderable` is closed under arbitrary indexed products, via the
  lexicographic order for some well-order on the index type.

## Implementation notes

`IsLeftOrderable` erases the witnessing order into `Prop`, asserting only that *some* compatible
`LinearOrder` exists. Recover an actual (noncomputable) `LinearOrder` instance from
`IsLeftOrderable.exists_linearOrder_mulLeftMono`.
-/

@[expose] public section

variable {G H : Type*} [Group G] [Group H]

/-- A group is left-orderable if it admits a linear order invariant under left multiplication. -/
@[mk_iff]
class IsLeftOrderable (G : Type*) [Group G] : Prop where
  exists_linearOrder_mulLeftMono (G) : ∃ _ : LinearOrder G, MulLeftMono G

export IsLeftOrderable (exists_linearOrder_mulLeftMono)

/-- A group with a linear order for which left multiplication is monotone is left-orderable: the
given order witnesses `IsLeftOrderable`. -/
instance [LinearOrder G] [MulLeftMono G] : IsLeftOrderable G := ⟨⟨‹_›, ‹_›⟩⟩

/-- `IsLeftOrderable G` may equivalently be characterized via strictly monotone left multiplication:
the group admits some linear order for which left multiplication is strictly monotone. -/
theorem isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono :
    IsLeftOrderable G ↔ ∃ _ : LinearOrder G, MulLeftStrictMono G := by
  rw [isLeftOrderable_iff]
  refine ⟨fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, inferInstance⟩,
    fun ⟨_, _⟩ ↦ ⟨‹LinearOrder G›, mulLeftMono_of_mulLeftStrictMono G⟩⟩

variable (G) in
theorem exists_linearOrder_mulLeftStrictMono [IsLeftOrderable G] :
    ∃ _ : LinearOrder G, MulLeftStrictMono G :=
  isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono.mp ‹_›

/-- Left-orderability transports along a group isomorphism: if `G` is left-orderable and
`e : G ≃* H` is a group isomorphism, then `H` is left-orderable. The witnessing order on `H` is the
pullback along `e` of a witnessing order on `G`. -/
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

/-- The direct product of two left-orderable groups is left-orderable.
Rather than defining the lexicographic order on `G × H` by hand, we transport left-orderability
across the group isomorphism `ofLexMulEquiv (G × H) : Lex (G × H) ≃* G × H`: the lexicographic
product `G ×ₗ H` is a left-orderable group by `Prod.Lex.mulLeftMono` (left multiplication is
monotone once it is strictly monotone on the first factor and monotone on the second), and
`IsLeftOrderable.of_mulEquiv` carries this order back to the plain product. -/
instance IsLeftOrderable.prod [IsLeftOrderable G] [IsLeftOrderable H] :
    IsLeftOrderable (G × H) := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftStrictMono G
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono H
  exact .of_mulEquiv (ofLexMulEquiv (G × H))

/-- An arbitrary indexed product of left-orderable groups is left-orderable.
As with `IsLeftOrderable.prod`, rather than defining the lexicographic order on `∀ i, G i` by hand,
we transport left-orderability across the group isomorphism
`ofLexMulEquiv (∀ i, G i) : Lex (∀ i, G i) ≃* ∀ i, G i`: the lexicographic product is a
left-orderable group by `Pi.Lex.mulLeftMono` (left multiplication is monotone once it is strictly
monotone on every factor) together with `Pi.Lex.linearOrder` (the lexicographic order on a
well-ordered product of linear orders is linear), and `IsLeftOrderable.of_mulEquiv` carries this
order back to the plain product. The index need not carry any order: since `IsLeftOrderable` only
asserts the existence of a witnessing order, we may endow `ι` with an arbitrary well-order via the
well-ordering theorem (`exists_wellFoundedLT`), which is exactly what makes the lexicographic order
linear. -/
instance IsLeftOrderable.pi {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, IsLeftOrderable (G i)] : IsLeftOrderable (∀ i, G i) := by
  choose l hl using fun i ↦ exists_linearOrder_mulLeftStrictMono (G i)
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  exact .of_mulEquiv (ofLexMulEquiv (∀ i, G i))

/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Left-orderable groups

A group `G` is *left-orderable* if it admits a linear order that is invariant under left
multiplication, i.e. `a ≤ b → c * a ≤ c * b` for all `a b c : G`.

This file introduces the `Prop`-valued class `IsLeftOrderable G`, which records the mere
*existence* of such an order, together with the instance producing it from any concrete
compatible linear order on `G`.

## Main declarations

* `IsLeftOrderable G`: the group `G` admits some `LinearOrder` for which left multiplication is
  monotone (`MulLeftMono`).
* `mulLeftStrictMono_iff_mulLeftMono`: on a linearly ordered group, monotone and strictly monotone
  left multiplication are equivalent, so `IsLeftOrderable` may equally be phrased with either.
* `IsLeftOrderable` is closed under direct products (with the lexicographic order).

## Implementation notes

`IsLeftOrderable` erases the witnessing order into `Prop`: it asserts that *some* compatible
`LinearOrder` exists without exposing a canonical one. To recover an actual `LinearOrder`
instance from `[IsLeftOrderable G]`, extract it noncomputably from
`IsLeftOrderable.exists_linearOrder_mulLeftMono`.

-/

@[expose] public section

variable (G : Type*) [Group G]

/-- A group is left-orderable if it admits a linear order invariant under left multiplication. -/
@[mk_iff]
class IsLeftOrderable : Prop where
  exists_linearOrder_mulLeftMono : ∃ _ : LinearOrder G, MulLeftMono G

variable [LinearOrder G]

instance [MulLeftMono G] : IsLeftOrderable G :=
  ⟨⟨‹_›, ‹_›⟩⟩

/-- For a group with a linear order, left multiplication is strictly monotone if and only if it is
monotone. Hence `IsLeftOrderable` could equivalently be defined with `MulLeftStrictMono` in place of
`MulLeftMono`. -/
@[to_additive /-- For an additive group with a linear order, left addition is strictly monotone if
and only if it is monotone. -/]
theorem mulLeftStrictMono_iff_mulLeftMono :
    MulLeftStrictMono G ↔ MulLeftMono G :=
  ⟨fun _ ↦ mulLeftMono_of_mulLeftStrictMono G, fun _ ↦ inferInstance⟩

variable {M N : Type*} [Group M] [Group N]

/-- The direct product of two left-orderable groups is left-orderable: the lexicographic order on
the product of witnessing orders is left-invariant. -/
instance [IsLeftOrderable M] [IsLeftOrderable N] : IsLeftOrderable (M × N) := by
  obtain ⟨_, _⟩ := ‹IsLeftOrderable M›.exists_linearOrder_mulLeftMono
  obtain ⟨_, _⟩ := ‹IsLeftOrderable N›.exists_linearOrder_mulLeftMono
  exact ⟨inferInstanceAs (LinearOrder (M ×ₗ N)), inferInstanceAs (MulLeftMono (M ×ₗ N))⟩

/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

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

## Implementation notes

`IsLeftOrderable` erases the witnessing order into `Prop`: it asserts that *some* compatible
`LinearOrder` exists without exposing a canonical one. To recover an actual `LinearOrder`
instance from `[IsLeftOrderable G]`, extract it noncomputably from
`IsLeftOrderable.exists_linearOrder_mulLeftMono`.

## TODO

* Right-orderable and bi-orderable groups.
* Equivalence with the existence of a suitable positive cone.
-/

@[expose] public section

/-- A group is left-orderable if it admits a linear order invariant under left multiplication. -/
@[mk_iff]
class IsLeftOrderable (G : Type*) [Group G] : Prop where
  exists_linearOrder_mulLeftMono : ∃ _ : LinearOrder G, MulLeftMono G

instance (G : Type*) [Group G] [LinearOrder G] [MulLeftMono G] : IsLeftOrderable G :=
  ⟨⟨‹_›, ‹_›⟩⟩

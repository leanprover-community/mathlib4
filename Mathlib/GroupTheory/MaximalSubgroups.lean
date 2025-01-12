/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Order.Atoms

/-! # Maximal subgroups

A subgroup `K` of a group `G` is maximal if it is maximal in the collection of proper subgroups
of `G`: this is defined as `IsCoatom K`.

We prove a few basic results which are essentially copied from those about maximal ideals.

Besides them, we have :
* `Subgroup.isMaximal_iff` proves that a subgroup `K` of `G` is maximal if and only if
  it is not `⊤` and if for all `g ∈ G` such that `g ∉ K`, every subgroup containing `K` and `g` is `⊤`.

## Remark on implementation

While the API is inspired from that for maximal ideals (`Ideal.IsMaximal`),
it has not been felt necessary to encapsulate the notion of maxiamal subgroup as a class,
and it is just defined as an `abbrev` to `IsCoatom`.

Will we need to write this for all `sub`-structures ?
In fact, the essentially only justification of this file is `Subgroup.isMaximal_iff`.
-/

variable {G : Type*} [Group G]

namespace Subgroup

/-- A subgroup is maximal if it is maximal in the collection of proper subgroups -/
@[to_additive
  "An additive subgroup is maximal if it is maximal in the collection of proper additive subgroups"]
abbrev IsMaximal (K : Subgroup G) : Prop :=
  IsCoatom K

@[to_additive]
theorem isMaximal_def {K : Subgroup G} : K.IsMaximal ↔ IsCoatom K := Iff.rfl

@[to_additive]
theorem IsMaximal.ne_top {K : Subgroup G} (h : K.IsMaximal) : K ≠ ⊤ := h.1

@[to_additive]
theorem IsMaximal.eq_top_of_lt {K H : Subgroup G} (h : K.IsMaximal) (hH : K < H) : H = ⊤ :=
    h.2 H hH

@[to_additive]
theorem isMaximal_iff {K : Subgroup G} :
    K.IsMaximal ↔ K ≠ ⊤ ∧ ∀ H g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ :=
  SetLike.isCoatom_iff

@[to_additive]
theorem IsMaximal.eq_of_le {K H : Subgroup G} (hK : K.IsMaximal) (hH : H ≠ ⊤) (KH : K ≤ H) :
    K = H :=
  eq_iff_le_not_lt.2 ⟨KH, fun h => hH (hK.2 H h)⟩

end Subgroup

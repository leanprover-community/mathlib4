/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module maximal_subgroups
-/
import Mathlib.GroupTheory.Subgroup.Basic

/-! # Maximal subgroups

A subgroup `is_maximal` if it is maximal in the collection of
proper subgroups.

We prove a few basic results which are essentially copied from
those about maximal ideals.

Besides them, we have :
* `is_maximal_iff` proves that a subgroup K of G is maximal
if and only  if it is not ⊤ and if for all g ∈ G such that g ∉ K,
every subgroup containing K and g is ⊤.

## TODO

Is it useful to write it in a greater generality?
Will we need to write this for all `sub`-structures ?

-/


-- import algebra.group.defs
variable {G : Type _} [Group G]

namespace Subgroup

/-- A subgroup is maximal if it is maximal in the collection of proper subgroups. -/
class IsMaximal (K : Subgroup G) : Prop where
/-- A subgroup is maximal if it is maximal in the collection of proper subgroups. -/
  out : IsCoatom K
#align subgroup.is_maximal Subgroup.IsMaximal

theorem isMaximal_def {K : Subgroup G} : K.IsMaximal ↔ IsCoatom K :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align subgroup.is_maximal_def Subgroup.isMaximal_def

theorem IsMaximal.ne_top {K : Subgroup G} (h : K.IsMaximal) : K ≠ ⊤ :=
  (isMaximal_def.1 h).1
#align subgroup.is_maximal.ne_top Subgroup.IsMaximal.ne_top

theorem isMaximal_iff {K : Subgroup G} :
    K.IsMaximal ↔ K ≠ ⊤ ∧ ∀ (H : Subgroup G) (g), K ≤ H → g ∉ K → g ∈ H → H = ⊤ := by
  constructor
  · intro hK
    constructor
    · exact hK.ne_top
    · intro H g hKH hgK hgH
      apply (isMaximal_def.1 hK).2
      rw [← Ne.le_iff_lt]
      exact hKH
      · rw [Ne.def]
        intro z
        rw [z] at hgK
        exact hgK hgH
  · rintro ⟨hG, hmax⟩
    constructor; constructor;
    · assumption
    · intro H hKH
      obtain ⟨g, hgH, hgK⟩ := Set.exists_of_ssubset hKH
      exact hmax H g (le_of_lt hKH) hgK hgH
#align subgroup.is_maximal_iff Subgroup.isMaximal_iff

theorem IsMaximal.eq_of_le {K H : Subgroup G} (hK : K.IsMaximal) (hH : H ≠ ⊤) (KH : K ≤ H) :
    K = H :=
  eq_iff_le_not_lt.2 ⟨KH, fun h => hH (hK.1.2 _ h)⟩
#align subgroup.is_maximal.eq_of_le Subgroup.IsMaximal.eq_of_le

end Subgroup

#lint

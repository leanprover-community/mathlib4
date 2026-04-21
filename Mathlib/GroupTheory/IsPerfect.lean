/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/
module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Perfect groups

A group `G` is perfect if it equals its commutator subgroup, that is `⁅G, G⁆ = G`.

Among the basic results, we show that
* a nontrivial perfect group is not solvable (`IsPerfect.not_isSolvable`);
* an abelian perfect group is trivial (`IsPerfect.subsingleton_of_isMulCommutative`).

## Main Definition

* `Group.IsPerfect`: a group `G` is *perfect* if it equals its own commutator,
  that is `⁅⊤, ⊤⁆ = ⊤`, where `⊤` is the full subgroup `G`.

## Main Theorems

* `IsPerfect.map`: The image of a perfect group under a monoid homomorphism is perfect.
* `IsPerfect.instQuotientSubgroup`: The quotient of a perfect group by a normal subgroup is perfect.
* `IsPerfect.ofSurjective`: The image of a perfect group under a surjective monoid
  homomorphism is perfect.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Group
open Subgroup

variable {G G' : Type*} [Group G] [Group G'] {H K : Subgroup G} (f : G →* G')

variable (G) in
/-- A group `G` is perfect if `G` equals its commutator subgroup `⁅G, G⁆`. -/
class IsPerfect where
  /-- The commutator of the group `G` with itself is the whole group `G`. -/
  commutator_eq_top : commutator G = (⊤ : Subgroup G)

attribute [simp] IsPerfect.commutator_eq_top

lemma isPerfect_def : IsPerfect G ↔ commutator G = ⊤ :=
  ⟨fun h ↦ h.commutator_eq_top, fun h ↦ ⟨h⟩⟩

lemma _root_.Subgroup.isPerfect_iff : IsPerfect H ↔ ⁅H, H⁆ = H := by
  rw [Group.isPerfect_def, ← map_subtype_inj,
    map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype]

lemma _root_.Subgroup.commutator_eq_self [hH : IsPerfect H] : ⁅H, H⁆ = H :=
  isPerfect_iff.mp hH

namespace IsPerfect

lemma mem_commutator [hP : IsPerfect G] {g : G} : g ∈ commutator G := by
  simp

/-- The trivial group is perfect. -/
instance [Subsingleton G] : IsPerfect G where
  commutator_eq_top := Subsingleton.elim _ _

theorem top_iff : IsPerfect (⊤ : Subgroup G) ↔ IsPerfect G := by
  rw [isPerfect_def, isPerfect_def, ← map_subtype_inj,
    map_subtype_commutator, ← MonoidHom.range_eq_map, subtype_range, commutator_def]

instance [IsPerfect G] : IsPerfect (⊤ : Subgroup G) :=
  top_iff.mpr inferInstance

variable (G) in
lemma not_isSolvable [Nontrivial G] [IsPerfect G] : ¬ IsSolvable G := by
  intro h
  exact (h.commutator_lt_top_of_nontrivial G).ne commutator_eq_top

variable (G) in
lemma not_isNilpotent [Nontrivial G] [IsPerfect G] : ¬ IsNilpotent G :=
  fun _ ↦ (not_isSolvable G) IsNilpotent.to_isSolvable

open scoped IsMulCommutative in
variable (G) in
lemma not_isMulCommutative [Nontrivial G] [IsPerfect G] : ¬ IsMulCommutative G :=
  fun _ ↦ (not_isSolvable G) CommGroup.isSolvable

instance subsingleton_of_isMulCommutative
    [hG : IsPerfect G] [h_comm : IsMulCommutative G] : Subsingleton G := by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm

protected lemma map [IsPerfect H] : IsPerfect (H.map f) := by
  rw [isPerfect_iff, ← map_commutator, commutator_eq_self]

protected lemma range [IsPerfect G] : IsPerfect f.range := by
  rw [MonoidHom.range_eq_map]
  exact IsPerfect.map _

variable {f} in
lemma ofSurjective [IsPerfect G] (hf : Function.Surjective f) : IsPerfect G' := by
  rw [← top_iff, ← MonoidHom.range_eq_top_of_surjective f hf]
  exact IsPerfect.range f

instance instQuotientSubgroup [H.Normal] [IsPerfect G] : IsPerfect (G ⧸ H) :=
  ofSurjective (QuotientGroup.mk'_surjective H)

end Group.IsPerfect

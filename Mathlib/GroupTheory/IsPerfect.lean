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
* an abelian solvable group is trivial (`IsPerfect.subsingleton_of_isMulCommutative`).

## Main Definition

* `IsPerfect`: a group `G` is *perfect* if it equals its own commutator,
  that is `⁅⊤, ⊤⁆ = ⊤`, where `⊤` is the full subgroup `G`.

## Main Theorems

* `IsPerfect.map`: The image of a perfect group under a monoid homomorphism is perfect.
* `IsPerfect.instQuotient`: The quotient of a perfect group by a normal subgroup is perfect.
* `IsPerfect.map_surjective`: The image of a perfect group under a surjective monoid homomorphism
  is perfect.
-/

@[expose] public section

namespace Group
open Subgroup

variable {G} [Group G] {H K : Subgroup G}

variable (G) in
/-- A group `G` is perfect if `G` equals its commutator subgroup `⁅G, G⁆`. -/
class IsPerfect where
  /-- The commutator of the group `G` with itself is the whole group `G`. -/
  commutator_eq_top : ⁅(⊤ : Subgroup G), ⊤⁆ = (⊤ : Subgroup G)

attribute [simp] IsPerfect.commutator_eq_top

lemma isPerfect_def : IsPerfect G ↔ commutator G = ⊤ :=
  ⟨fun h ↦ h.commutator_eq_top, fun h ↦ ⟨h⟩⟩

lemma _root_.Subgroup.isPerfect_iff : IsPerfect H ↔ ⁅H, H⁆ = H := by
  rw [Group.isPerfect_def, ← (map_injective H.subtype_injective).eq_iff,
    map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype]

namespace IsPerfect

lemma mem_comm [hP : IsPerfect G] {g : G} : g ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
  simp

/-- The trivial subgroup `⊥` is always perfect. -/
instance instIsPerfectBot : IsPerfect (⊥ : Subgroup G) where
  commutator_eq_top := of_decide_eq_true rfl

/--
If a group `G` is perfect, then also viewing `G` as the top subgroup of itself
it is a perfect group.
-/
instance instIsPerfectTop [hC : IsPerfect G] : IsPerfect (⊤ : Subgroup G) where
  commutator_eq_top := by
    ext ⟨h, hh⟩
    rw [← hC.commutator_eq_top, ← map_subtype_commutator] at hh
    aesop

/--
If a group `G` is perfect, when viewed as the top subgroup of `G`, then also `G` itself is perfect.
-/
-- Should *not* be an instance!
lemma instIsPerfectTop' [hC : IsPerfect (⊤ : Subgroup G)] : IsPerfect G where
  commutator_eq_top := by
    apply le_antisymm (commutator_le_self (⊤ : Subgroup G))
    intro h hh
    rw [← map_subtype_commutator, _root_.commutator_def]
    simp [*]

lemma not_isSolvable (G) [Group G] [Nontrivial G] [IsPerfect G] :
    ¬ IsSolvable G := by
  intro h
  have comm_lt := IsSolvable.commutator_lt_of_ne_bot (bot_ne_top (α := Subgroup G)).symm
  grind only [commutator_eq_top]

lemma not_isNilpotent (G) [Group G] [Nontrivial G] [IsPerfect G] :
    ¬ IsNilpotent G :=
  fun _ ↦ (not_isSolvable G) IsNilpotent.to_isSolvable

lemma not_isMulCommutative (G) [Group G] [Nontrivial G] [IsPerfect G] :
    ¬ IsMulCommutative G :=
  fun _ ↦ (not_isSolvable G) CommGroup.isSolvable

instance subsingleton_of_isMulCommutative
    [hG : IsPerfect G] [h_comm : IsMulCommutative G] : Subsingleton G := by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm

/-- The image of a perfect subgroup under a homomorphism is perfect. -/
protected
lemma map {G'} [Group G'] [hP : IsPerfect G] (f : G →* G') :
    IsPerfect (map f ⊤) := by
  rw [Subgroup.isPerfect_iff, ← map_commutator, hP.commutator_eq_top]

/--
The subgroup `⊤` of `G ⧸ H` is perfect if the group `G` is.

See `Group.IsPerfect.instQuotient'` for the analogous statement about the type `G ⧸ H` itself.
-/
instance instQuotient [H.Normal] [hP : IsPerfect G] :
    IsPerfect (⊤ : Subgroup (G ⧸ H)) := by
  rw [← map_top_of_surjective _ (QuotientGroup.mk'_surjective H)]
  exact hP.map _

/--
The group `G ⧸ H` is perfect if the group `G` is.

The difference with `Group.IsPerfect.instQuotient` is that the conclusion here is the type
`G ⧸ H`, rather than the subgroup `(⊤ : Subgroup (G ⧸ H))`.
-/
instance instQuotient' [hH : H.Normal] [hP : IsPerfect G] : IsPerfect (G ⧸ H) :=
  instIsPerfectTop'

/--
This lemma is a version of `map`, except that the image is the simpler `⊤ : Subgroup G'`, but
there is a surjectivity assumption on `f` instead.
-/
lemma map_surjective {G'} [Group G'] [IsPerfect G] {f : G →* G'} (hf : Function.Surjective f) :
    IsPerfect G' :=
  have : IsPerfect (map f ⊤) := IsPerfect.map f
  instIsPerfectTop' (hC := by rwa [map_top_of_surjective f hf] at this)

end Group.IsPerfect

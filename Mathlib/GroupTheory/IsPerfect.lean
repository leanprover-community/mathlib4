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
* an abelian solvable group is trivial.

## Main Definition

* `IsPerfect`: a subgroup `H` of a group `G` is *perfect* if it equals its own commutator,
  that is `⁅H, H⁆ = H`.

## Main Theorems

* `IsPerfect.map`: The image of a perfect subgroup under a monoid homomorphism is perfect.
* `IsPerfect.instQuotient`: The quotient of a perfect group by a normal subgroup is perfect.
* `IsPerfect.map_surjective`: The image of a perfect group under a monoid homomorphism is perfect.

## Implementation Notes

The definition of `IsPerfect` takes a *sub*group `H` of `G`, instead of the whole group.
Hence, the expected spelling for the whole group being perfect is `(⊤ : Subgroup G).IsPerfect`.

This definition makes it easier to work with perfect subgroups, which are often encountered
in the informal setting.

For instance, a *quasi-simple* subgroup of a group is a perfect subgroup whose quotient by the
centre is simple.

Such groups play a fundamental role in the classification of finite simple groups.
-/

@[expose] public section

namespace Subgroup
open Group

variable {G} [Group G] {H K : Subgroup G}

/-- A subgroup `H` of a group `G` is perfect if `H` equals its commutator subgroup `⁅H, H⁆`. -/
class IsPerfect (H : Subgroup G) where
  /-- The commutator of the subgroup `H` with itself is the whole subgroup `H`. -/
  commutator_eq_top : ⁅H, H⁆ = H

attribute [simp] IsPerfect.commutator_eq_top

namespace IsPerfect

lemma mem_comm_iff [hP : H.IsPerfect] {g : G} : g ∈ ⁅H, H⁆ ↔ g ∈ H := by
  simp

/-- The trivial subgroup `⊥` is always perfect. -/
instance instIsPerfectBot : (⊥ : Subgroup G).IsPerfect where
  commutator_eq_top := commutator_bot_right _

/--
If a subgroup `H` of `G` is perfect, then also viewing `H` as the top subgroup of itself
it is a perfect group.
-/
instance instIsPerfectTop [hC : H.IsPerfect] : (⊤ : Subgroup H).IsPerfect where
  commutator_eq_top := by
    ext ⟨h, hh⟩
    rw [← hC.commutator_eq_top, ← map_subtype_commutator] at hh
    rw [← _root_.commutator_def]
    simp_all

/--
If a subgroup `H` of `G` is perfect, when viewed as the top subgroup of `H`, then also viewing
`H` as a subgroup of `G` it is perfect.
-/
-- Should *not* be an instance!
lemma instIsPerfectTop' [hC : (⊤ : Subgroup H).IsPerfect] : H.IsPerfect where
  commutator_eq_top := by
    apply le_antisymm (commutator_le_self H)
    intro h hh
    rw [← map_subtype_commutator, _root_.commutator_def]
    simp [*]

lemma not_isSolvable (G) [Group G] [Nontrivial G] [IsPerfect (⊤ : Subgroup G)] :
    ¬ IsSolvable G := by
  intro h
  have comm_lt := IsSolvable.commutator_lt_of_ne_bot (bot_ne_top (α := Subgroup G)).symm
  grind only [commutator_eq_top]

lemma not_isNilpotent (G) [Group G] [Nontrivial G] [IsPerfect (⊤ : Subgroup G)] :
    ¬ IsNilpotent G :=
  fun _ ↦ (not_isSolvable G) IsNilpotent.to_isSolvable

lemma not_isMulCommutative (G) [Group G] [Nontrivial G] [IsPerfect (⊤ : Subgroup G)] :
    ¬ IsMulCommutative G :=
  fun _ ↦ (not_isSolvable G) CommGroup.isSolvable

instance instSubsingletonOfIsPerfectTopOfIsMulCommutative
    [hG : IsPerfect (⊤ : Subgroup G)] [h_comm : IsMulCommutative G] : Subsingleton G := by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm

/-- The image of a perfect subgroup under a homomorphism is perfect. -/
protected
lemma map {G'} [Group G'] [hP : IsPerfect H] (f : G →* G') :
    IsPerfect (map f H) where
  commutator_eq_top := by
    cases hP with
    | mk commutator_eq_top => grind only [map_commutator]

instance instQuotient [H.Normal] [hP : IsPerfect (⊤ : Subgroup G)] :
    IsPerfect (⊤ : Subgroup (G ⧸ H)) := by
  rw [← map_top_of_surjective _ (QuotientGroup.mk'_surjective H)]
  exact hP.map _

/--
This lemma is a version of `map`, except that the image is the simpler `⊤ : Subgroup G'`, but
there is a surjectivity assumption on `f` instead.
-/
lemma map_surjective {G'} [Group G'] [IsPerfect (⊤ : Subgroup G)] {f : G →* G'}
    (hf : Function.Surjective f) :
    IsPerfect (⊤ : Subgroup G') where
  commutator_eq_top := by
    ext g'
    simp only [mem_top, iff_true]
    obtain ⟨g, rfl⟩ := hf g'
    simp [← map_top_of_surjective f hf, ← map_commutator]

end Subgroup.IsPerfect

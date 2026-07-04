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

variable (G) in
@[simp]
theorem derivedSeries_eq_top [IsPerfect G] (n : ℕ) : derivedSeries G n = ⊤ := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [derivedSeries_succ, derivedSeries_eq_top, commutator_eq_self]

@[simp]
theorem lowerCentralSeries_eq_top (H : Subgroup G) [IsPerfect H] (n : ℕ) :
    H.lowerCentralSeries n = H := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [Subgroup.lowerCentralSeries_succ, lowerCentralSeries_eq_top, commutator_eq_self]

variable (G) in
@[simp]
theorem upperCentralSeries_eq_center [IsPerfect G] {n : ℕ} (hn : n ≠ 0) :
    Subgroup.upperCentralSeries G n = center G := by
  rw [← Subgroup.upperCentralSeries_one, eq_comm]
  apply Subgroup.upperCentralSeries.eq_ge_of_eq_succ <| by lia
  apply le_antisymm <| Subgroup.upperCentralSeries_mono G one_le_two
  rw [Subgroup.upperCentralSeries_one, ← commutator_top_right_eq_bot_iff_le_center,
    ← commutator_eq_top, commutator_comm, commutator_def]
  suffices ⁅⁅Subgroup.upperCentralSeries G 2, ⊤⁆, ⊤⁆ = ⊥ from
    commutator_commutator_eq_bot_of_rotate (by simpa [commutator_comm]) this
  rw [commutator_top_right_eq_bot_iff_le_center, ← Subgroup.upperCentralSeries_one]
  apply commutator_upperCentralSeries_top_le

variable (G) in
/-- **Grün's lemma** -/
theorem center_quotient_center_eq_bot [IsPerfect G] : center (G ⧸ center G) = ⊥ := by
  rw [← Subgroup.upperCentralSeries_one (G ⧸ center G),
    ← comap_eq_ker_of_surjective <| QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk',
    Subgroup.comap_upperCentralSeries_quotient_center, upperCentralSeries_eq_center G <| by lia]

end Group.IsPerfect

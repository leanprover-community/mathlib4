/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rank of a group

This file defines the rank of a group, namely the minimum size of a generating set.

## TODO

Should we define `erank G : ℕ∞` the rank of a not necessarily finitely generated group `G`,
then redefine `rank G` as `(erank G).toNat`? Maybe a `Cardinal`-valued version too?
-/

open Function Group

variable {G H : Type*} [Group G] [Group H]

namespace Group

variable (G) in
/-- The minimum number of generators of a group. -/
@[to_additive /-- The minimum number of generators of an additive group. -/]
noncomputable def rank [h : FG G] : ℕ := @Nat.find _ (Classical.decPred _) (fg_iff'.mp h)

variable (G) in
@[to_additive]
lemma rank_spec [h : FG G] : ∃ S : Finset G, S.card = rank G ∧ .closure S = (⊤ : Subgroup G) :=
  @Nat.find_spec _ (Classical.decPred _) (fg_iff'.mp h)

@[to_additive]
lemma rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ : Subgroup G)) : rank G ≤ S.card :=
  @Nat.find_le _ _ (Classical.decPred _) (fg_iff'.mp h) ⟨S, rfl, hS⟩

@[to_additive]
lemma rank_le_of_surjective [FG G] [FG H] (f : G →* H) (hf : Surjective f) : rank H ≤ rank G := by
  classical
  obtain ⟨S, hS1, hS2⟩ := rank_spec G
  trans (S.image f).card
  · apply rank_le
    rw [Finset.coe_image, ← MonoidHom.map_closure, hS2, Subgroup.map_top_of_surjective f hf]
  · exact Finset.card_image_le.trans_eq hS1

@[to_additive]
lemma rank_range_le [FG G] {f : G →* H} : rank f.range ≤ rank G :=
  rank_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
lemma rank_congr [FG G] [FG H] (e : G ≃* H) : rank G = rank H :=
  le_antisymm (rank_le_of_surjective e.symm e.symm.surjective)
    (rank_le_of_surjective e e.surjective)

end Group

namespace Subgroup

@[to_additive]
lemma rank_congr {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K) : rank H = rank K := by
  subst h; rfl

@[to_additive]
lemma rank_closure_finset_le_card (s : Finset G) : rank (closure (s : Set G)) ≤ s.card := by
  classical
  let t : Finset (closure (s : Set G)) := s.preimage Subtype.val Subtype.coe_injective.injOn
  have ht : closure (t : Set (closure (s : Set G))) = ⊤ := by
    rw [Finset.coe_preimage]
    exact closure_preimage_eq_top (s : Set G)
  apply (rank_le ht).trans
  suffices H : Set.InjOn Subtype.val (t : Set (closure (s : Set G))) by
    rw [← Finset.card_image_of_injOn H, Finset.image_preimage]
    apply Finset.card_filter_le
  apply Subtype.coe_injective.injOn

@[to_additive]
lemma rank_closure_finite_le_nat_card (s : Set G) [Finite s] : rank (closure s) ≤ Nat.card s := by
  haveI := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card, ← s.toFinset_card, ← rank_congr (congr_arg _ s.coe_toFinset)]
  exact rank_closure_finset_le_card s.toFinset

lemma nat_card_centralizer_nat_card_stabilizer (g : G) :
    Nat.card (centralizer {g}) = Nat.card (MulAction.stabilizer (ConjAct G) g) := by
  rw [centralizer_eq_comap_stabilizer];   rfl

end Subgroup

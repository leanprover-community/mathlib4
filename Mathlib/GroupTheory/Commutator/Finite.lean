/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.Index

/-!
The commutator of a finite direct product is contained in the direct product of the commutators.
-/

public section

variable {G : Type*} [Group G] {H₁ H₂ : Subgroup G}

namespace Subgroup

theorem commutator_eq_bot_of_coprime_natCard [H₁.Normal] [H₂.Normal]
    (h : Nat.card H₁ |>.Coprime <| Nat.card H₂) : ⁅H₁, H₂⁆ = ⊥ := by
  grw [eq_bot_iff, commutator_le_inf]
  exact disjoint_of_coprime_natCard h |>.eq_bot.le

theorem commute_of_coprime_natCard [H₁.Normal] [H₂.Normal]
    (h : Nat.card H₁ |>.Coprime <| Nat.card H₂) {g₁ g₂} (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂) :
    Commute g₁ g₂ := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [commutator_eq_bot_of_coprime_natCard h] using commutator_mem_commutator h₁ h₂

/-- The commutator of a finite direct product is contained in the direct product of the commutators.
-/
@[to_additive /-- The commutator of a finite direct product is contained in the direct product of
the commutators. -/]
theorem commutator_pi_pi_of_finite {η : Type*} [Finite η] {Gs : η → Type*} [∀ i, Group (Gs i)]
    (H K : ∀ i, Subgroup (Gs i)) : ⁅Subgroup.pi Set.univ H, Subgroup.pi Set.univ K⁆ =
    Subgroup.pi Set.univ fun i => ⁅H i, K i⁆ := by
  classical
    apply le_antisymm (commutator_pi_pi_le H K)
    rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j _hj
        rintro _ ⟨x, hx, rfl⟩
        by_cases h : j = i
        · subst h
          simpa using hx
        · simp [h, one_mem]

variable [Finite (commutatorSet G)]

instance : Group.FG (_root_.commutator G) := by
  rw [commutator_eq_closure]; apply Group.closure_finite_fg

variable (G) in
lemma rank_commutator_le_card : Group.rank (_root_.commutator G) ≤ Nat.card (commutatorSet G) := by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

variable [Group.FG G]

instance finiteIndex_center : FiniteIndex (center G) := by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩

variable (G) in
lemma index_center_le_pow : (center G).index ≤ Nat.card (commutatorSet G) ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Finset.coe_sort_coe, ← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

end Subgroup

section commutatorRepresentatives

open Subgroup

lemma card_commutatorSet_closureCommutatorRepresentatives :
    Nat.card (commutatorSet (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G) := by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

lemma card_commutator_closureCommutatorRepresentatives :
    Nat.card (commutator (closureCommutatorRepresentatives G)) = Nat.card (commutator G) := by
  rw [commutator_eq_closure G, ← image_commutatorSet_closureCommutatorRepresentatives, ←
    MonoidHom.map_closure, ← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

variable [Finite (commutatorSet G)]

instance : Finite (commutatorRepresentatives G) := Set.finite_coe_iff.mpr (Set.finite_range _)

instance closureCommutatorRepresentatives_fg : Group.FG (closureCommutatorRepresentatives G) :=
  Group.closure_finite_fg _

variable (G) in
lemma rank_closureCommutatorRepresentatives_le :
    Group.rank (closureCommutatorRepresentatives G) ≤ 2 * Nat.card (commutatorSet G) := by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))

instance : Finite (commutatorSet (closureCommutatorRepresentatives G)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

end commutatorRepresentatives

/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk
import Mathlib.Combinatorics.SimpleGraph.Regularity.Energy

#align_import combinatorics.simple_graph.regularity.increment from "leanprover-community/mathlib"@"bf7ef0e83e5b7e6c1169e97f055e58a2e4e9d52d"

/-!
# Increment partition for Szemerédi Regularity Lemma

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines the partition obtained by gluing the parts partitions
together (the *increment partition*) and shows that the energy globally increases.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.increment`: The increment partition.
* `SzemerediRegularity.card_increment`: The increment partition is much bigger than the original,
  but by a controlled amount.
* `SzemerediRegularity.energy_increment`: The increment partition has energy greater than the
  original by a known (small) fixed amount.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`gcongr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset Fintype SimpleGraph SzemerediRegularity

open scoped SzemerediRegularity.Positivity

variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ)

local notation3 "m" => (card α / stepBound P.parts.card : ℕ)

namespace SzemerediRegularity

/-- The **increment partition** in Szemerédi's Regularity Lemma.

If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition
with a slightly higher energy. This is helpful since the energy is bounded by a constant (see
`Finpartition.energy_le_one`), so this process eventually terminates and yields a
not-too-big uniform equipartition. -/
noncomputable def increment : Finpartition (univ : Finset α) :=
  P.bind fun _ => chunk hP G ε
#align szemeredi_regularity.increment SzemerediRegularity.increment

open Finpartition Finpartition.IsEquipartition

variable {hP G ε}

/-- The increment partition has a prescribed (very big) size in terms of the original partition. -/
theorem card_increment (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPG : ¬P.IsUniform G ε) :
    (increment hP G ε).parts.card = stepBound P.parts.card := by
  have hPα' : stepBound P.parts.card ≤ card α :=
    (mul_le_mul_left' (pow_le_pow_left' (by norm_num) _) _).trans hPα
  have hPpos : 0 < stepBound P.parts.card := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  rw [increment, card_bind]
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  rw [sum_const_nat, sum_const_nat, card_attach, card_attach]; rotate_left
  any_goals exact fun x hx => card_parts_equitabilise _ _ (Nat.div_pos hPα' hPpos).ne'
  rw [Nat.sub_add_cancel a_add_one_le_four_pow_parts_card,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), ← add_mul]
  congr
  rw [filter_card_add_filter_neg_card_eq_card, card_attach]
#align szemeredi_regularity.card_increment SzemerediRegularity.card_increment

variable (hP G ε)

theorem increment_isEquipartition : (increment hP G ε).IsEquipartition := by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨m, fun A hA => ?_⟩
  rw [mem_coe, increment, mem_bind] at hA
  obtain ⟨U, hU, hA⟩ := hA
  exact card_eq_of_mem_parts_chunk hA
#align szemeredi_regularity.increment_is_equipartition SzemerediRegularity.increment_isEquipartition

/-- The contribution to `Finpartition.energy` of a pair of distinct parts of a `Finpartition`. -/
private noncomputable def distinctPairs (x : {x // x ∈ P.parts.offDiag}) :
    Finset (Finset α × Finset α) :=
  (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts

variable {hP G ε}

private theorem distinctPairs_increment :
    P.parts.offDiag.attach.biUnion (distinctPairs hP G ε) ⊆ (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  simp only [distinctPairs, increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    exists_and_left, exists_prop, mem_product, mem_attach, true_and_iff, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, exists₂_imp, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro rfl
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)

private lemma pairwiseDisjoint_distinctPairs :
    (P.parts.offDiag.attach : Set {x // x ∈ P.parts.offDiag}).PairwiseDisjoint
      (distinctPairs hP G ε) := by
  simp (config := { unfoldPartialApp := true }) only [distinctPairs, Set.PairwiseDisjoint,
    Function.onFun, disjoint_left, inf_eq_inter, mem_inter, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
  exact hst <| Subtype.ext_val <| Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
        P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb) <|
          Finpartition.le _ huv₂.2 hb

variable [Nonempty α]

lemma le_sum_distinctPairs_edgeDensity_sq (x : {i // i ∈ P.parts.offDiag}) (hε₁ : ε ≤ 1)
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : ↑100 ≤ ↑4 ^ P.parts.card * ε ^ 5) :
    (G.edgeDensity x.1.1 x.1.2 : ℝ) ^ 2 +
      ((if G.IsUniform ε x.1.1 x.1.2 then 0 else ε ^ 4 / 3) - ε ^ 5 / 25) ≤
    (∑ i ∈ distinctPairs hP G ε x, G.edgeDensity i.1 i.2 ^ 2 : ℝ) / 16 ^ P.parts.card := by
  rw [distinctPairs, ← add_sub_assoc, add_sub_right_comm]
  split_ifs with h
  · rw [add_zero]
    exact edgeDensity_chunk_uniform hPα hPε _ _
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h
#align szemeredi_regularity.pair_contrib_lower_bound SzemerediRegularity.le_sum_distinctPairs_edgeDensity_sq

#noalign szemeredi_regularity.off_diag_pairs_le_increment_energy
#noalign szemeredi_regularity.uniform_add_nonuniform_eq_off_diag_pairs

/-- The increment partition has energy greater than the original one by a known fixed amount. -/
theorem energy_increment (hP : P.IsEquipartition) (hP₇ : 7 ≤ P.parts.card)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPG : ¬P.IsUniform G ε) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ↑(P.energy G) + ε ^ 5 / 4 ≤ (increment hP G ε).energy G := by
  calc
    _ = (∑ x ∈ P.parts.offDiag, (G.edgeDensity x.1 x.2 : ℝ) ^ 2 +
          P.parts.card ^ 2 * (ε ^ 5 / 4) : ℝ) / P.parts.card ^ 2 := by
        rw [coe_energy, add_div, mul_div_cancel_left₀]; positivity
    _ ≤ (∑ x ∈ P.parts.offDiag.attach, (∑ i ∈ distinctPairs hP G ε x,
          G.edgeDensity i.1 i.2 ^ 2 : ℝ) / 16 ^ P.parts.card) / P.parts.card ^ 2 := ?_
    _ = (∑ x ∈ P.parts.offDiag.attach, ∑ i ∈ distinctPairs hP G ε x,
          G.edgeDensity i.1 i.2 ^ 2 : ℝ) / (increment hP G ε).parts.card ^ 2 := by
        rw [card_increment hPα hPG, coe_stepBound, mul_pow, pow_right_comm,
          div_mul_eq_div_div_swap, ← sum_div]; norm_num
    _ ≤ _ := by
        rw [coe_energy]
        gcongr
        rw [← sum_biUnion pairwiseDisjoint_distinctPairs]
        exact sum_le_sum_of_subset_of_nonneg distinctPairs_increment fun i _ _ ↦ sq_nonneg _
  gcongr
  rw [Finpartition.IsUniform, not_le, mul_tsub, mul_one, ← offDiag_card] at hPG
  calc
    _ ≤ ∑ x ∈ P.parts.offDiag, (edgeDensity G x.1 x.2 : ℝ) ^ 2 +
        ((nonUniforms P G ε).card * (ε ^ 4 / 3) - P.parts.offDiag.card * (ε ^ 5 / 25)) :=
        add_le_add_left ?_ _
    _ = ∑ x ∈ P.parts.offDiag, ((G.edgeDensity x.1 x.2 : ℝ) ^ 2 +
        ((if G.IsUniform ε x.1 x.2 then (0 : ℝ) else ε ^ 4 / 3) - ε ^ 5 / 25) : ℝ) := by
        rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_ite, sum_const_zero,
          zero_add, sum_const, nsmul_eq_mul, ← Finpartition.nonUniforms, ← add_sub_assoc,
          add_sub_right_comm]
    _ = _ := (sum_attach ..).symm
    _ ≤ _ := sum_le_sum fun i _ ↦ le_sum_distinctPairs_edgeDensity_sq i hε₁ hPα hPε
  calc
    _ = (6/7 * P.parts.card ^ 2) * ε ^ 5 * (7 / 24) := by ring
    _ ≤ P.parts.offDiag.card * ε ^ 5 * (22 / 75) := by
        gcongr ?_ * _ * ?_
        · rw [← mul_div_right_comm, div_le_iff (by norm_num), offDiag_card]
          norm_cast
          rw [tsub_mul]
          refine le_tsub_of_add_le_left ?_
          nlinarith
        · norm_num
    _ = (P.parts.offDiag.card * ε * (ε ^ 4 / 3) - P.parts.offDiag.card * (ε ^ 5 / 25)) := by ring
    _ ≤ ((nonUniforms P G ε).card * (ε ^ 4 / 3) - P.parts.offDiag.card * (ε ^ 5 / 25)) := by gcongr
#align szemeredi_regularity.energy_increment SzemerediRegularity.energy_increment

end SzemerediRegularity

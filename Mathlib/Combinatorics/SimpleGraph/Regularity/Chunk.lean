/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.regularity.chunk
! leanprover-community/mathlib commit bf7ef0e83e5b7e6c1169e97f055e58a2e4e9d52d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Bound
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform

/-!
# Chunk of the increment partition for Szemerédi Regularity Lemma

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines those partitions of parts and shows that they locally
increase the energy.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `szemeredi_regularity.chunk`: The partition of a part of the starting partition.
* `szemeredi_regularity.edge_density_chunk_uniform`: `chunk` does not locally decrease the edge
  density between uniform parts too much.
* `szemeredi_regularity.edge_density_chunk_not_uniform`: `chunk` locally increases the edge density
  between non-uniform parts.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`rel_congr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finpartition Finset Fintype Rel Nat

open scoped BigOperators Classical

attribute [local positivity] tactic.positivity_szemeredi_regularity

namespace SzemerediRegularity

variable {α : Type _} [Fintype α] {P : Finpartition (univ : Finset α)} (hP : P.IsEquipartition)
  (G : SimpleGraph α) (ε : ℝ) {U : Finset α} (hU : U ∈ P.parts) (V : Finset α)

local notation "m" => (card α / stepBound P.parts.card : ℕ)

/-!
### Definitions

We define `chunk`, the partition of a part, and `star`, the sets of parts of `chunk` that are
contained in the corresponding witness of non-uniformity.
-/


/-- The portion of `szemeredi_regularity.increment` which partitions `U`. -/
noncomputable def chunk : Finpartition U :=
  if hUcard : U.card = m * 4 ^ P.parts.card + (card α / P.parts.card - m * 4 ^ P.parts.card) then
    (atomise U <| P.nonuniformWitnesses G ε U).equitabilise <| card_aux₁ hUcard
  else (atomise U <| P.nonuniformWitnesses G ε U).equitabilise <| card_aux₂ hP hU hUcard
#align szemeredi_regularity.chunk SzemerediRegularity.chunk

-- `hP` and `hU` are used to get that `U` has size
-- `m * 4 ^ P.parts.card + a or m * 4 ^ P.parts.card + a + 1`
/-- The portion of `szemeredi_regularity.chunk` which is contained in the witness of non uniformity
of `U` and `V`. -/
noncomputable def star (V : Finset α) : Finset (Finset α) :=
  (chunk hP G ε hU).parts.filterₓ (· ⊆ G.nonuniformWitness ε U V)
#align szemeredi_regularity.star SzemerediRegularity.star

/-!
### Density estimates

We estimate the density between parts of `chunk`.
-/


theorem biUnion_star_subset_nonuniformWitness :
    (star hP G ε hU V).biUnion id ⊆ G.nonuniformWitness ε U V :=
  biUnion_subset_iff_forall_subset.2 fun A hA => (mem_filter.1 hA).2
#align szemeredi_regularity.bUnion_star_subset_nonuniform_witness SzemerediRegularity.biUnion_star_subset_nonuniformWitness

variable {hP G ε hU V} {𝒜 : Finset (Finset α)} {s : Finset α}

theorem star_subset_chunk : star hP G ε hU V ⊆ (chunk hP G ε hU).parts :=
  filter_subset _ _
#align szemeredi_regularity.star_subset_chunk SzemerediRegularity.star_subset_chunk

private theorem card_nonuniform_witness_sdiff_bUnion_star (hV : V ∈ P.parts) (hUV : U ≠ V)
    (h₂ : ¬G.IsUniform ε U V) :
    (G.nonuniformWitness ε U V \ (star hP G ε hU V).biUnion id).card ≤ 2 ^ (P.parts.card - 1) * m :=
  by
  have hX : G.nonuniform_witness ε U V ∈ P.nonuniform_witnesses G ε U :=
    nonuniform_witness_mem_nonuniform_witnesses h₂ hV hUV
  have q :
    G.nonuniform_witness ε U V \ (star hP G ε hU V).biUnion id ⊆
      ((atomise U <| P.nonuniform_witnesses G ε U).parts.filterₓ fun B =>
            B ⊆ G.nonuniform_witness ε U V ∧ B.Nonempty).biUnion
        fun B => B \ ((chunk hP G ε hU).parts.filterₓ (· ⊆ B)).biUnion id := by
    intro x hx
    rw [← bUnion_filter_atomise hX (G.nonuniform_witness_subset h₂), star, mem_sdiff, mem_bUnion] at
      hx 
    simp only [not_exists, mem_bUnion, and_imp, filter_congr_decidable, exists_prop, mem_filter,
      not_and, mem_sdiff, id.def, mem_sdiff] at hx ⊢
    obtain ⟨⟨B, hB₁, hB₂⟩, hx⟩ := hx
    exact ⟨B, hB₁, hB₂, fun A hA AB => hx A hA <| AB.trans hB₁.2.1⟩
  apply (card_le_of_subset q).trans (card_bUnion_le.trans _)
  trans
    ∑ i in
      (atomise U <| P.nonuniform_witnesses G ε U).parts.filterₓ fun B =>
        B ⊆ G.nonuniform_witness ε U V ∧ B.Nonempty,
      m
  · suffices
      ∀ B ∈ (atomise U <| P.nonuniform_witnesses G ε U).parts,
        (B \ ((chunk hP G ε hU).parts.filterₓ (· ⊆ B)).biUnion id).card ≤ m
      by exact sum_le_sum fun B hB => this B <| filter_subset _ _ hB
    intro B hB
    unfold chunk
    split_ifs with h₁
    · convert card_parts_equitabilise_subset_le _ (card_aux₁ h₁) hB
    · convert card_parts_equitabilise_subset_le _ (card_aux₂ hP hU h₁) hB
  rw [sum_const]
  refine' mul_le_mul_right' _ _
  have t := card_filter_atomise_le_two_pow hX
  rw [filter_congr_decidable] at t 
  refine' t.trans (pow_le_pow (by norm_num) <| tsub_le_tsub_right _ _)
  exact card_image_le.trans (card_le_of_subset <| filter_subset _ _)

private theorem one_sub_eps_mul_card_nonuniform_witness_le_card_star (hV : V ∈ P.parts)
    (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hε₁ : ε ≤ 1) :
    (1 - ε / 10) * (G.nonuniformWitness ε U V).card ≤ ((star hP G ε hU V).biUnion id).card := by
  have hP₁ : 0 < P.parts.card := Finset.card_pos.2 ⟨_, hU⟩
  have : (2 ^ P.parts.card : ℝ) * m / (U.card * ε) ≤ ε / 10 := by
    rw [← div_div, div_le_iff']
    swap
    positivity
    refine' le_of_mul_le_mul_left _ (pow_pos zero_lt_two P.parts.card)
    calc
      2 ^ P.parts.card * ((2 ^ P.parts.card * m : ℝ) / U.card) =
          (2 * 2) ^ P.parts.card * m / U.card :=
        by rw [mul_pow, ← mul_div_assoc, mul_assoc]
      _ = 4 ^ P.parts.card * m / U.card := by norm_num
      _ ≤ 1 := (div_le_one_of_le (pow_mul_m_le_card_part hP hU) (cast_nonneg _))
      _ ≤ 2 ^ P.parts.card * ε ^ 2 / 10 := by
        refine' (one_le_sq_iff <| by positivity).1 _
        rw [div_pow, mul_pow, pow_right_comm, ← pow_mul ε,
          one_le_div (sq_pos_of_ne_zero (10 : ℝ) <| by norm_num)]
        calc
          (10 ^ 2 : ℝ) = 100 := by norm_num
          _ ≤ 4 ^ P.parts.card * ε ^ 5 := hPε
          _ ≤ 4 ^ P.parts.card * ε ^ 4 :=
            (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hε₁ <| le_succ _)
              (by positivity))
          _ = (2 ^ 2) ^ P.parts.card * ε ^ (2 * 2) := by norm_num
      _ = 2 ^ P.parts.card * (ε * (ε / 10)) := by rw [mul_div_assoc, sq, mul_div_assoc]
  calc
    (1 - ε / 10) * (G.nonuniform_witness ε U V).card ≤
        (1 - 2 ^ P.parts.card * m / (U.card * ε)) * (G.nonuniform_witness ε U V).card :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left this _) (cast_nonneg _)
    _ =
        (G.nonuniform_witness ε U V).card -
          2 ^ P.parts.card * m / (U.card * ε) * (G.nonuniform_witness ε U V).card :=
      by rw [sub_mul, one_mul]
    _ ≤ (G.nonuniform_witness ε U V).card - 2 ^ (P.parts.card - 1) * m := by
      refine' sub_le_sub_left _ _
      have : (2 : ℝ) ^ P.parts.card = 2 ^ (P.parts.card - 1) * 2 := by
        rw [← pow_succ', tsub_add_cancel_of_le (succ_le_iff.2 hP₁)]
      rw [← mul_div_right_comm, this, mul_right_comm _ (2 : ℝ), mul_assoc, le_div_iff]
      refine' mul_le_mul_of_nonneg_left _ (by positivity)
      exact
        (G.le_card_nonuniform_witness hunif).trans
          (le_mul_of_one_le_left (cast_nonneg _) one_le_two)
      have := P.nonempty_of_mem_parts hU
      positivity
    _ ≤ ((star hP G ε hU V).biUnion id).card := by
      norm_cast
      rw [sub_le_comm, ←
        cast_sub (card_le_of_subset <| bUnion_star_subset_nonuniform_witness hP G ε hU V), ←
        card_sdiff (bUnion_star_subset_nonuniform_witness hP G ε hU V), cast_le]
      exact card_nonuniform_witness_sdiff_bUnion_star hV hUV hunif

variable {hP G ε U hU V}

/-! ### `chunk` -/


theorem card_chunk (hm : m ≠ 0) : (chunk hP G ε hU).parts.card = 4 ^ P.parts.card := by
  unfold chunk
  split_ifs
  · rw [card_parts_equitabilise _ _ hm, tsub_add_cancel_of_le]
    exact le_of_lt a_add_one_le_four_pow_parts_card
  · rw [card_parts_equitabilise _ _ hm, tsub_add_cancel_of_le a_add_one_le_four_pow_parts_card]
#align szemeredi_regularity.card_chunk SzemerediRegularity.card_chunk

theorem card_eq_of_mem_parts_chunk (hs : s ∈ (chunk hP G ε hU).parts) :
    s.card = m ∨ s.card = m + 1 := by unfold chunk at hs ;
  split_ifs at hs  <;> exact card_eq_of_mem_parts_equitabilise hs
#align szemeredi_regularity.card_eq_of_mem_parts_chunk SzemerediRegularity.card_eq_of_mem_parts_chunk

theorem m_le_card_of_mem_chunk_parts (hs : s ∈ (chunk hP G ε hU).parts) : m ≤ s.card :=
  (card_eq_of_mem_parts_chunk hs).elim ge_of_eq fun i => by simp [i]
#align szemeredi_regularity.m_le_card_of_mem_chunk_parts SzemerediRegularity.m_le_card_of_mem_chunk_parts

theorem card_le_m_add_one_of_mem_chunk_parts (hs : s ∈ (chunk hP G ε hU).parts) : s.card ≤ m + 1 :=
  (card_eq_of_mem_parts_chunk hs).elim (fun i => by simp [i]) fun i => i.le
#align szemeredi_regularity.card_le_m_add_one_of_mem_chunk_parts SzemerediRegularity.card_le_m_add_one_of_mem_chunk_parts

theorem card_biUnion_star_le_m_add_one_card_star_mul :
    (((star hP G ε hU V).biUnion id).card : ℝ) ≤ (star hP G ε hU V).card * (m + 1) := by
  exact_mod_cast
    card_bUnion_le_card_mul _ _ _ fun s hs =>
      card_le_m_add_one_of_mem_chunk_parts <| star_subset_chunk hs
#align szemeredi_regularity.card_bUnion_star_le_m_add_one_card_star_mul SzemerediRegularity.card_biUnion_star_le_m_add_one_card_star_mul

private theorem le_sum_card_subset_chunk_parts (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (𝒜.card : ℝ) * s.card * (m / (m + 1)) ≤ (𝒜.sup id).card := by
  rw [mul_div_assoc', div_le_iff coe_m_add_one_pos, mul_right_comm]
  refine' mul_le_mul _ _ (cast_nonneg _) (cast_nonneg _)
  · rw [← (of_subset _ h𝒜 rfl).sum_card_parts, of_subset_parts, ← cast_mul, cast_le]
    exact card_nsmul_le_sum _ _ _ fun x hx => m_le_card_of_mem_chunk_parts <| h𝒜 hx
  · exact_mod_cast card_le_m_add_one_of_mem_chunk_parts (h𝒜 hs)

private theorem sum_card_subset_chunk_parts_le (m_pos : (0 : ℝ) < m)
    (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    ((𝒜.sup id).card : ℝ) ≤ 𝒜.card * s.card * ((m + 1) / m) := by
  rw [sup_eq_bUnion, mul_div_assoc', le_div_iff m_pos, mul_right_comm]
  refine' mul_le_mul _ _ (cast_nonneg _) (by positivity)
  · norm_cast
    refine' card_bUnion_le_card_mul _ _ _ fun x hx => _
    apply card_le_m_add_one_of_mem_chunk_parts (h𝒜 hx)
  · exact_mod_cast m_le_card_of_mem_chunk_parts (h𝒜 hs)

private theorem one_sub_le_m_div_m_add_one_sq [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) :
    1 - ε ^ 5 / 50 ≤ (m / (m + 1)) ^ 2 := by
  have : (m : ℝ) / (m + 1) = 1 - 1 / (m + 1) := by
    rw [one_sub_div coe_m_add_one_pos.ne', add_sub_cancel]
  rw [this, sub_sq, one_pow, mul_one]
  refine' le_trans _ (le_add_of_nonneg_right <| sq_nonneg _)
  rw [sub_le_sub_iff_left, ← le_div_iff' (show (0 : ℝ) < 2 by norm_num), div_div,
    one_div_le coe_m_add_one_pos, one_div_div]
  refine' le_trans _ (le_add_of_nonneg_right zero_le_one)
  norm_num
  apply hundred_div_ε_pow_five_le_m hPα hPε
  positivity

private theorem m_add_one_div_m_le_one_add [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hε₁ : ε ≤ 1) : ((m + 1 : ℝ) / m) ^ 2 ≤ 1 + ε ^ 5 / 49 := by
  rw [same_add_div]
  swap
  · positivity
  have : 1 + 1 / (m : ℝ) ≤ 1 + ε ^ 5 / 100 := by
    rw [add_le_add_iff_left, ← one_div_div (100 : ℝ)]
    exact one_div_le_one_div_of_le (by positivity) (hundred_div_ε_pow_five_le_m hPα hPε)
  refine' (pow_le_pow_of_le_left _ this 2).trans _
  · positivity
  rw [add_sq, one_pow, add_assoc, add_le_add_iff_left, mul_one, ← le_sub_iff_add_le',
    div_eq_mul_one_div _ (49 : ℝ), mul_div_left_comm (2 : ℝ), ← mul_sub_left_distrib, div_pow,
    div_le_iff (show (0 : ℝ) < 100 ^ 2 by norm_num), mul_assoc, sq]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  exact (pow_le_one 5 (by positivity) hε₁).trans (by norm_num)

private theorem density_sub_eps_le_sum_density_div_card [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    ↑(G.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / 50 ≤
      (∑ ab in A.product B, G.edgeDensity ab.1 ab.2) / (A.card * B.card) := by
  have :
    ↑(G.edge_density (A.bUnion id) (B.bUnion id)) - ε ^ 5 / 50 ≤
      (1 - ε ^ 5 / 50) * G.edge_density (A.bUnion id) (B.bUnion id) := by
    rw [sub_mul, one_mul, sub_le_sub_iff_left]
    refine' mul_le_of_le_one_right (by positivity) _
    exact_mod_cast G.edge_density_le_one _ _
  refine' this.trans _
  simp only [SimpleGraph.edgeDensity_def, SimpleGraph.interedges, ← sup_eq_bUnion, cast_sum,
    Rel.card_interedges_finpartition _ (of_subset _ hA rfl) (of_subset _ hB rfl), of_subset_parts,
    sum_div, mul_sum, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, div_div,
    mul_div_left_comm ((1 : ℝ) - _)]
  push_cast
  apply sum_le_sum
  simp only [and_imp, Prod.forall, mem_product]
  rintro x y hx hy
  rw [mul_mul_mul_comm, mul_comm (x.card : ℝ), mul_comm (y.card : ℝ), le_div_iff, mul_assoc]
  · refine' mul_le_of_le_one_right (cast_nonneg _) _
    rw [div_mul_eq_mul_div, ← mul_assoc, mul_assoc]
    refine' div_le_one_of_le _ (by positivity)
    refine' (mul_le_mul_of_nonneg_right (one_sub_le_m_div_m_add_one_sq hPα hPε) _).trans _
    · exact_mod_cast zero_le _
    rw [sq, mul_mul_mul_comm, mul_comm ((m : ℝ) / _), mul_comm ((m : ℝ) / _)]
    refine' mul_le_mul _ _ _ (cast_nonneg _)
    apply le_sum_card_subset_chunk_parts hA hx
    apply le_sum_card_subset_chunk_parts hB hy
    positivity
  refine' mul_pos (mul_pos _ _) (mul_pos _ _) <;> rw [cast_pos, Finset.card_pos]
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]

private theorem sum_density_div_card_le_density_add_eps [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    (∑ ab in A.product B, G.edgeDensity ab.1 ab.2 : ℝ) / (A.card * B.card) ≤
      G.edgeDensity (A.biUnion id) (B.biUnion id) + ε ^ 5 / 49 := by
  have :
    (1 + ε ^ 5 / 49) * G.edge_density (A.bUnion id) (B.bUnion id) ≤
      G.edge_density (A.bUnion id) (B.bUnion id) + ε ^ 5 / 49 := by
    rw [add_mul, one_mul, add_le_add_iff_left]
    refine' mul_le_of_le_one_right (by positivity) _
    exact_mod_cast G.edge_density_le_one _ _
  refine' le_trans _ this
  simp only [SimpleGraph.edgeDensity, edge_density, ← sup_eq_bUnion, cast_sum, mul_sum, sum_div,
    Rel.card_interedges_finpartition _ (of_subset _ hA rfl) (of_subset _ hB rfl), Rat.cast_sum,
    Rat.cast_div, Rat.cast_mul, of_subset_parts, mul_div_left_comm ((1 : ℝ) + _), div_div]
  push_cast
  apply sum_le_sum
  simp only [and_imp, Prod.forall, mem_product]
  intro x y hx hy
  rw [mul_mul_mul_comm, mul_comm (x.card : ℝ), mul_comm (y.card : ℝ), div_le_iff, mul_assoc]
  · refine' le_mul_of_one_le_right (cast_nonneg _) _
    rw [div_mul_eq_mul_div, one_le_div]
    refine' le_trans _ (mul_le_mul_of_nonneg_right (m_add_one_div_m_le_one_add hPα hPε hε₁) _)
    · rw [sq, mul_mul_mul_comm, mul_comm (_ / (m : ℝ)), mul_comm (_ / (m : ℝ))]
      exact
        mul_le_mul (sum_card_subset_chunk_parts_le (by positivity) hA hx)
          (sum_card_subset_chunk_parts_le (by positivity) hB hy) (by positivity) (by positivity)
    · exact_mod_cast zero_le _
    rw [← cast_mul, cast_pos]
    apply mul_pos <;> rw [Finset.card_pos, sup_eq_bUnion, bUnion_nonempty]
    · exact ⟨_, hx, nonempty_of_mem_parts _ (hA hx)⟩
    · exact ⟨_, hy, nonempty_of_mem_parts _ (hB hy)⟩
  refine' mul_pos (mul_pos _ _) (mul_pos _ _) <;> rw [cast_pos, Finset.card_pos]
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]

private theorem average_density_near_total_density [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    |(∑ ab in A.product B, G.edgeDensity ab.1 ab.2 : ℝ) / (A.card * B.card) -
          G.edgeDensity (A.biUnion id) (B.biUnion id)| ≤
      ε ^ 5 / 49 := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add']
    exact sum_density_div_card_le_density_add_eps hPα hPε hε₁ hA hB
  suffices
    (G.edge_density (A.bUnion id) (B.bUnion id) : ℝ) -
        (∑ ab in A.product B, G.edge_density ab.1 ab.2) / (A.card * B.card) ≤
      ε ^ 5 / 50 by
    apply this.trans
    exact div_le_div_of_le_left (by positivity) (by norm_num) (by norm_num)
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  apply density_sub_eps_le_sum_density_div_card hPα hPε hA hB

private theorem edge_density_chunk_aux [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    ↑(G.edgeDensity U V) ^ 2 - ε ^ 5 / 25 ≤
      ((∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts, G.edgeDensity ab.1 ab.2) /
          16 ^ P.parts.card) ^
        2 := by
  obtain hGε | hGε := le_total (↑(G.edge_density U V)) (ε ^ 5 / 50)
  · refine' (sub_nonpos_of_le <| (sq_le _ _).trans <| hGε.trans _).trans (sq_nonneg _)
    · exact_mod_cast G.edge_density_nonneg _ _
    · exact_mod_cast G.edge_density_le_one _ _
    · exact div_le_div_of_le_left (by positivity) (by norm_num) (by norm_num)
  rw [← sub_nonneg] at hGε 
  have :
    ↑(G.edge_density U V) - ε ^ 5 / 50 ≤
      (∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts, G.edge_density ab.1 ab.2) /
        16 ^ P.parts.card := by
    refine'
      (le_trans _ <|
            density_sub_eps_le_sum_density_div_card hPα hPε
              (Set.Subset.refl (chunk hP G ε hU).parts)
              (Set.Subset.refl (chunk hP G ε hV).parts)).trans
        _
    · rw [bUnion_parts, bUnion_parts]
    · rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ← cast_mul, ← mul_pow, cast_pow]
      norm_cast
  refine' le_trans _ (pow_le_pow_of_le_left hGε this 2)
  rw [sub_sq, sub_add, sub_le_sub_iff_left]
  refine' (sub_le_self _ <| sq_nonneg <| ε ^ 5 / 50).trans _
  rw [mul_right_comm, mul_div_left_comm, div_eq_mul_inv (ε ^ 5),
    show (2 : ℝ) / 50 = 25⁻¹ by norm_num]
  exact mul_le_of_le_one_right (by positivity) (by exact_mod_cast G.edge_density_le_one _ _)

private theorem abs_density_star_sub_density_le_eps (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUV' : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    |(G.edgeDensity ((star hP G ε hU V).biUnion id) ((star hP G ε hV U).biUnion id) : ℝ) -
          G.edgeDensity (G.nonuniformWitness ε U V) (G.nonuniformWitness ε V U)| ≤
      ε / 5 := by
  convert
    abs_edge_density_sub_edge_density_le_two_mul G.adj
      (bUnion_star_subset_nonuniform_witness hP G ε hU V)
      (bUnion_star_subset_nonuniform_witness hP G ε hV U) (by positivity)
      (one_sub_eps_mul_card_nonuniform_witness_le_card_star hV hUV' hUV hPε hε₁)
      (one_sub_eps_mul_card_nonuniform_witness_le_card_star hU hUV'.symm (fun hVU => hUV hVU.symm)
        hPε hε₁)
  linarith

private theorem eps_le_card_star_div [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) (hε₁ : ε ≤ 1) (hU : U ∈ P.parts) (hV : V ∈ P.parts)
    (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V) :
    4 / 5 * ε ≤ (star hP G ε hU V).card / 4 ^ P.parts.card := by
  have hm : (0 : ℝ) ≤ 1 - m⁻¹ := sub_nonneg_of_le (inv_le_one <| one_le_m_coe hPα)
  have hε : 0 ≤ 1 - ε / 10 :=
    sub_nonneg_of_le (div_le_one_of_le (hε₁.trans <| by norm_num) <| by norm_num)
  calc
    4 / 5 * ε = (1 - 1 / 10) * (1 - 9⁻¹) * ε := by norm_num
    _ ≤ (1 - ε / 10) * (1 - m⁻¹) * ((G.nonuniform_witness ε U V).card / U.card) :=
      (mul_le_mul
        (mul_le_mul (sub_le_sub_left (div_le_div_of_le_of_nonneg hε₁ <| by norm_num) _)
          (sub_le_sub_left
            (inv_le_inv_of_le (by norm_num) <| by
              exact_mod_cast show 9 ≤ 100 by norm_num.trans (hundred_le_m hPα hPε hε₁))
            _)
          (by norm_num) hε)
        ((le_div_iff' <| (@cast_pos ℝ _ _ _).2 (P.nonempty_of_mem_parts hU).card_pos).2 <|
          G.le_card_nonuniform_witness hunif)
        (by positivity) (by positivity))
    _ = (1 - ε / 10) * (G.nonuniform_witness ε U V).card * ((1 - m⁻¹) / U.card) := by
      rw [mul_assoc, mul_assoc, mul_div_left_comm]
    _ ≤ ((star hP G ε hU V).biUnion id).card * ((1 - m⁻¹) / U.card) :=
      (mul_le_mul_of_nonneg_right
        (one_sub_eps_mul_card_nonuniform_witness_le_card_star hV hUV hunif hPε hε₁) (by positivity))
    _ ≤ (star hP G ε hU V).card * (m + 1) * ((1 - m⁻¹) / U.card) :=
      (mul_le_mul_of_nonneg_right card_bUnion_star_le_m_add_one_card_star_mul (by positivity))
    _ ≤ (star hP G ε hU V).card * (m + 1) * ((1 - m⁻¹) / (4 ^ P.parts.card * m)) :=
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_le_left hm (by positivity) <| pow_mul_m_le_card_part hP hU) (by positivity))
    _ ≤ (star hP G ε hU V).card / 4 ^ P.parts.card := by
      rw [mul_assoc, mul_comm ((4 : ℝ) ^ P.parts.card), ← div_div, ← mul_div_assoc, ← mul_comm_div]
      refine' mul_le_of_le_one_right (by positivity) _
      have hm : (0 : ℝ) < m := by positivity
      rw [mul_div_assoc', div_le_one hm, ← one_div, one_sub_div hm.ne', mul_div_assoc',
        div_le_iff hm]
      linarith

/-!
### Final bounds

Those inequalities are the end result of all this hard work.
-/


/-- Lower bound on the edge densities between non-uniform parts of `szemeredi_regularity.star`. -/
private theorem edge_density_star_not_uniform [Nonempty α]
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUVne : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    3 / 4 * ε ≤
      |(∑ ab in (star hP G ε hU V).product (star hP G ε hV U), G.edgeDensity ab.1 ab.2) /
            ((star hP G ε hU V).card * (star hP G ε hV U).card) -
          (∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
              G.edgeDensity ab.1 ab.2) /
            16 ^ P.parts.card| := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, pow_right_comm, sq ((4 : ℝ) ^ _)]
  set p : ℝ :=
    (∑ ab in (star hP G ε hU V).product (star hP G ε hV U), G.edge_density ab.1 ab.2) /
      ((star hP G ε hU V).card * (star hP G ε hV U).card)
  set q : ℝ :=
    (∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts, G.edge_density ab.1 ab.2) /
      (4 ^ P.parts.card * 4 ^ P.parts.card)
  change _ ≤ |p - q|
  set r : ℝ := G.edge_density ((star hP G ε hU V).biUnion id) ((star hP G ε hV U).biUnion id)
  set s : ℝ := G.edge_density (G.nonuniform_witness ε U V) (G.nonuniform_witness ε V U)
  set t : ℝ := G.edge_density U V
  have hrs : |r - s| ≤ ε / 5 := abs_density_star_sub_density_le_eps hPε hε₁ hUVne hUV
  have hst : ε ≤ |s - t| := G.nonuniform_witness_spec hUVne hUV
  have hpr : |p - r| ≤ ε ^ 5 / 49 :=
    average_density_near_total_density hPα hPε hε₁ star_subset_chunk star_subset_chunk
  have hqt : |q - t| ≤ ε ^ 5 / 49 := by
    have :=
      average_density_near_total_density hPα hPε hε₁ (subset.refl (chunk hP G ε hU).parts)
        (subset.refl (chunk hP G ε hV).parts)
    simp_rw [← sup_eq_bUnion, sup_parts, card_chunk (m_pos hPα).ne', cast_pow] at this 
    norm_num at this 
    exact this
  have hε' : ε ^ 5 ≤ ε := by
    simpa using pow_le_pow_of_le_one (by positivity) hε₁ (show 1 ≤ 5 by norm_num)
  have hpr' : |p - r| ≤ ε / 49 := hpr.trans (div_le_div_of_le_of_nonneg hε' <| by norm_num)
  have hqt' : |q - t| ≤ ε / 49 := hqt.trans (div_le_div_of_le_of_nonneg hε' <| by norm_num)
  rw [abs_sub_le_iff] at hrs hpr' hqt' 
  rw [le_abs] at hst ⊢
  cases hst
  left; linarith
  right; linarith

/-- Lower bound on the edge densities between non-uniform parts of `szemeredi_regularity.increment`.
-/
theorem edgeDensity_chunk_not_uniform [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts}
    (hUVne : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / 25 + ε ^ 4 / 3 ≤
      (∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
          G.edgeDensity ab.1 ab.2 ^ 2) /
        16 ^ P.parts.card :=
  calc
    ↑(G.edgeDensity U V) ^ 2 - ε ^ 5 / 25 + ε ^ 4 / 3 ≤
        G.edgeDensity U V ^ 2 - ε ^ 5 / 25 +
          (star hP G ε hU V).card * (star hP G ε hV U).card / 16 ^ P.parts.card * (9 / 16) *
            ε ^ 2 := by
      apply add_le_add_left
      have Ul : 4 / 5 * ε ≤ (star hP G ε hU V).card / _ :=
        eps_le_card_star_div hPα hPε hε₁ hU hV hUVne hUV
      have Vl : 4 / 5 * ε ≤ (star hP G ε hV U).card / _ :=
        eps_le_card_star_div hPα hPε hε₁ hV hU hUVne.symm fun h => hUV h.symm
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, pow_right_comm, sq ((4 : ℝ) ^ _), ←
        _root_.div_mul_div_comm, mul_assoc]
      have : 0 < ε := by positivity
      have UVl := mul_le_mul Ul Vl (by positivity) (by positivity)
      refine' le_trans _ (mul_le_mul_of_nonneg_right UVl _)
      · field_simp
        ring_nf
        apply mul_le_mul_of_nonneg_right
        norm_num
        positivity
      · norm_num
        positivity
    _ ≤
        (∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
            G.edgeDensity ab.1 ab.2 ^ 2) /
          16 ^ P.parts.card := by
      have t :
        (star hP G ε hU V).product (star hP G ε hV U) ⊆
          (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts :=
        product_subset_product star_subset_chunk star_subset_chunk
      have hε : 0 ≤ ε := by positivity
      have :=
        add_div_le_sum_sq_div_card t (fun x => (G.edge_density x.1 x.2 : ℝ))
          (G.edge_density U V ^ 2 - ε ^ 5 / 25) (show 0 ≤ 3 / 4 * ε by linarith) _ _
      · simp_rw [card_product, card_chunk (m_pos hPα).ne', ← mul_pow, cast_pow, mul_pow, div_pow, ←
          mul_assoc] at this 
        norm_num at this 
        exact this
      · simp_rw [card_product, card_chunk (m_pos hPα).ne', ← mul_pow]
        norm_num
        exact edge_density_star_not_uniform hPα hPε hε₁ hUVne hUV
      · rw [card_product]
        apply (edge_density_chunk_aux hPα hPε hU hV).trans
        rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ← mul_pow]
        norm_num
        exact hP
#align szemeredi_regularity.edge_density_chunk_not_uniform SzemerediRegularity.edgeDensity_chunk_not_uniform

/-- Lower bound on the edge densities between parts of `szemeredi_regularity.increment`. This is the
blanket lower bound used the uniform parts. -/
theorem edgeDensity_chunk_uniform [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / 25 ≤
      (∑ ab in (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
          G.edgeDensity ab.1 ab.2 ^ 2) /
        16 ^ P.parts.card := by
  apply (edge_density_chunk_aux hPα hPε hU hV).trans
  convert sum_div_card_sq_le_sum_sq_div_card <;>
      rw [card_product, cast_mul, card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ←
        cast_mul, ← mul_pow] <;>
    norm_cast
#align szemeredi_regularity.edge_density_chunk_uniform SzemerediRegularity.edgeDensity_chunk_uniform

end SzemerediRegularity


/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
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

* `SzemerediRegularity.chunk`: The partition of a part of the starting partition.
* `SzemerediRegularity.edgeDensity_chunk_uniform`: `chunk` does not locally decrease the edge
  density between uniform parts too much.
* `SzemerediRegularity.edgeDensity_chunk_not_uniform`: `chunk` locally increases the edge density
  between non-uniform parts.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`gcongr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finpartition Finset Fintype Rel Nat
open scoped SzemerediRegularity.Positivity

namespace SzemerediRegularity

variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) {U : Finset α}
  (hU : U ∈ P.parts) (V : Finset α)

local notation3 "m" => (card α / stepBound #P.parts : ℕ)

/-!
### Definitions

We define `chunk`, the partition of a part, and `star`, the sets of parts of `chunk` that are
contained in the corresponding witness of non-uniformity.
-/


/-- The portion of `SzemerediRegularity.increment` which partitions `U`. -/
noncomputable def chunk : Finpartition U :=
  if hUcard : #U = m * 4 ^ #P.parts + (card α / #P.parts - m * 4 ^ #P.parts) then
    (atomise U <| P.nonuniformWitnesses G ε U).equitabilise <| card_aux₁ hUcard
  else (atomise U <| P.nonuniformWitnesses G ε U).equitabilise <| card_aux₂ hP hU hUcard

-- `hP` and `hU` are used to get that `U` has size
-- `m * 4 ^ #P.parts + a or m * 4 ^ #P.parts + a + 1`
/-- The portion of `SzemerediRegularity.chunk` which is contained in the witness of non-uniformity
of `U` and `V`. -/
noncomputable def star (V : Finset α) : Finset (Finset α) :=
  {A ∈ (chunk hP G ε hU).parts | A ⊆ G.nonuniformWitness ε U V}

/-!
### Density estimates

We estimate the density between parts of `chunk`.
-/


theorem biUnion_star_subset_nonuniformWitness :
    (star hP G ε hU V).biUnion id ⊆ G.nonuniformWitness ε U V :=
  biUnion_subset_iff_forall_subset.2 fun _ hA => (mem_filter.1 hA).2

variable {hP G ε hU V} {𝒜 : Finset (Finset α)} {s : Finset α}

theorem star_subset_chunk : star hP G ε hU V ⊆ (chunk hP G ε hU).parts :=
  filter_subset _ _

private theorem card_nonuniformWitness_sdiff_biUnion_star (hV : V ∈ P.parts) (hUV : U ≠ V)
    (h₂ : ¬G.IsUniform ε U V) :
    #(G.nonuniformWitness ε U V \ (star hP G ε hU V).biUnion id) ≤ 2 ^ (#P.parts - 1) * m := by
  have hX : G.nonuniformWitness ε U V ∈ P.nonuniformWitnesses G ε U :=
    nonuniformWitness_mem_nonuniformWitnesses h₂ hV hUV
  have q : G.nonuniformWitness ε U V \ (star hP G ε hU V).biUnion id ⊆
      {B ∈ (atomise U <| P.nonuniformWitnesses G ε U).parts |
        B ⊆ G.nonuniformWitness ε U V ∧ B.Nonempty}.biUnion
        fun B => B \ {A ∈ (chunk hP G ε hU).parts | A ⊆ B}.biUnion id := by
    intro x hx
    rw [← biUnion_filter_atomise hX (G.nonuniformWitness_subset h₂), star, mem_sdiff,
      mem_biUnion] at hx
    simp only [not_exists, mem_biUnion, and_imp, mem_filter,
      not_and, mem_sdiff, id, mem_sdiff] at hx ⊢
    obtain ⟨⟨B, hB₁, hB₂⟩, hx⟩ := hx
    exact ⟨B, hB₁, hB₂, fun A hA AB => hx A hA <| AB.trans hB₁.2.1⟩
  apply (card_le_card q).trans (card_biUnion_le.trans _)
  trans ∑ B ∈ (atomise U <| P.nonuniformWitnesses G ε U).parts with
    B ⊆ G.nonuniformWitness ε U V ∧ B.Nonempty, m
  · suffices ∀ B ∈ (atomise U <| P.nonuniformWitnesses G ε U).parts,
        #(B \ {A ∈ (chunk hP G ε hU).parts | A ⊆ B}.biUnion id) ≤ m by
      exact sum_le_sum fun B hB => this B <| filter_subset _ _ hB
    intro B hB
    unfold chunk
    split_ifs with h₁
    · convert card_parts_equitabilise_subset_le _ (card_aux₁ h₁) hB
    · convert card_parts_equitabilise_subset_le _ (card_aux₂ hP hU h₁) hB
  grw [sum_const, smul_eq_mul, card_filter_atomise_le_two_pow (s := U) hX,
    Finpartition.card_nonuniformWitnesses_le, filter_subset] <;> simp

private theorem one_sub_eps_mul_card_nonuniformWitness_le_card_star (hV : V ∈ P.parts)
    (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) :
    (1 - ε / 10) * #(G.nonuniformWitness ε U V) ≤ #((star hP G ε hU V).biUnion id) := by
  have hP₁ : 0 < #P.parts := Finset.card_pos.2 ⟨_, hU⟩
  have : (↑2 ^ #P.parts : ℝ) * m / (#U * ε) ≤ ε / 10 := by
    rw [← div_div, div_le_iff₀']
    swap
    · sz_positivity
    refine le_of_mul_le_mul_left ?_ (pow_pos zero_lt_two #P.parts)
    calc
      ↑2 ^ #P.parts * ((↑2 ^ #P.parts * m : ℝ) / #U) =
          ((2 : ℝ) * 2) ^ #P.parts * m / #U := by
        rw [mul_pow, ← mul_div_assoc, mul_assoc]
      _ = ↑4 ^ #P.parts * m / #U := by norm_num
      _ ≤ 1 := div_le_one_of_le₀ (pow_mul_m_le_card_part hP hU) (cast_nonneg _)
      _ ≤ ↑2 ^ #P.parts * ε ^ 2 / 10 := by
        refine (one_le_sq_iff₀ <| by positivity).1 ?_
        rw [div_pow, mul_pow, pow_right_comm, ← pow_mul ε, one_le_div (by positivity)]
        calc
          (↑10 ^ 2) = 100 := by norm_num
          _ ≤ ↑4 ^ #P.parts * ε ^ 5 := hPε
          _ ≤ ↑4 ^ #P.parts * ε ^ 4 := by
            gcongr _ * ?_
            exact pow_le_pow_of_le_one (by sz_positivity) hε₁ (by decide)
          _ = (↑2 ^ 2) ^ #P.parts * ε ^ (2 * 2) := by norm_num
      _ = ↑2 ^ #P.parts * (ε * (ε / 10)) := by rw [mul_div_assoc, sq, mul_div_assoc]
  calc
    (↑1 - ε / 10) * #(G.nonuniformWitness ε U V) ≤
        (↑1 - ↑2 ^ #P.parts * m / (#U * ε)) * #(G.nonuniformWitness ε U V) := by gcongr
    _ = #(G.nonuniformWitness ε U V) -
        ↑2 ^ #P.parts * m / (#U * ε) * #(G.nonuniformWitness ε U V) := by
      rw [sub_mul, one_mul]
    _ ≤ #(G.nonuniformWitness ε U V) - ↑2 ^ (#P.parts - 1) * m := by
      refine sub_le_sub_left ?_ _
      have : (2 : ℝ) ^ #P.parts = ↑2 ^ (#P.parts - 1) * 2 := by
        rw [← _root_.pow_succ, tsub_add_cancel_of_le (succ_le_iff.2 hP₁)]
      rw [← mul_div_right_comm, this, mul_right_comm _ (2 : ℝ), mul_assoc, le_div_iff₀]
      · gcongr _ * ?_
        exact (G.le_card_nonuniformWitness hunif).trans
          (le_mul_of_one_le_left (cast_nonneg _) one_le_two)
      have := Finset.card_pos.mpr (P.nonempty_of_mem_parts hU)
      sz_positivity
    _ ≤ #((star hP G ε hU V).biUnion id) := by
      rw [sub_le_comm, ←
        cast_sub (card_le_card <| biUnion_star_subset_nonuniformWitness hP G ε hU V), ←
        card_sdiff_of_subset (biUnion_star_subset_nonuniformWitness hP G ε hU V)]
      exact mod_cast card_nonuniformWitness_sdiff_biUnion_star hV hUV hunif

/-! ### `chunk` -/


theorem card_chunk (hm : m ≠ 0) : #(chunk hP G ε hU).parts = 4 ^ #P.parts := by
  unfold chunk
  split_ifs
  · rw [card_parts_equitabilise _ _ hm, tsub_add_cancel_of_le]
    exact le_of_lt a_add_one_le_four_pow_parts_card
  · rw [card_parts_equitabilise _ _ hm, tsub_add_cancel_of_le a_add_one_le_four_pow_parts_card]

theorem card_eq_of_mem_parts_chunk (hs : s ∈ (chunk hP G ε hU).parts) :
    #s = m ∨ #s = m + 1 := by
  unfold chunk at hs
  split_ifs at hs <;> exact card_eq_of_mem_parts_equitabilise hs

theorem m_le_card_of_mem_chunk_parts (hs : s ∈ (chunk hP G ε hU).parts) : m ≤ #s :=
  (card_eq_of_mem_parts_chunk hs).elim ge_of_eq fun i => by simp [i]

theorem card_le_m_add_one_of_mem_chunk_parts (hs : s ∈ (chunk hP G ε hU).parts) : #s ≤ m + 1 :=
  (card_eq_of_mem_parts_chunk hs).elim (fun i => by simp [i]) fun i => i.le

theorem card_biUnion_star_le_m_add_one_card_star_mul :
    (#((star hP G ε hU V).biUnion id) : ℝ) ≤ #(star hP G ε hU V) * (m + 1) :=
  mod_cast card_biUnion_le_card_mul _ _ _ fun _ hs =>
    card_le_m_add_one_of_mem_chunk_parts <| star_subset_chunk hs

private theorem le_sum_card_subset_chunk_parts (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (#𝒜 : ℝ) * #s * (m / (m + 1)) ≤ #(𝒜.sup id) := by
  rw [mul_div_assoc', div_le_iff₀ coe_m_add_one_pos, mul_right_comm]
  gcongr
  · rw [← (ofSubset _ h𝒜 rfl).sum_card_parts, ofSubset_parts, ← cast_mul, cast_le]
    exact card_nsmul_le_sum _ _ _ fun x hx => m_le_card_of_mem_chunk_parts <| h𝒜 hx
  · exact mod_cast card_le_m_add_one_of_mem_chunk_parts (h𝒜 hs)

private theorem sum_card_subset_chunk_parts_le (m_pos : (0 : ℝ) < m)
    (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (#(𝒜.sup id) : ℝ) ≤ #𝒜 * #s * ((m + 1) / m) := by
  rw [sup_eq_biUnion, mul_div_assoc', le_div_iff₀ m_pos, mul_right_comm]
  gcongr
  · norm_cast
    refine card_biUnion_le_card_mul _ _ _ fun x hx => ?_
    apply card_le_m_add_one_of_mem_chunk_parts (h𝒜 hx)
  · exact mod_cast m_le_card_of_mem_chunk_parts (h𝒜 hs)

private theorem one_sub_le_m_div_m_add_one_sq [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) :
    ↑1 - ε ^ 5 / ↑50 ≤ (m / (m + 1 : ℝ)) ^ 2 := by
  have : (m : ℝ) / (m + 1) = 1 - 1 / (m + 1) := by
    rw [one_sub_div coe_m_add_one_pos.ne', add_sub_cancel_right]
  rw [this, sub_sq, one_pow, mul_one]
  refine le_trans ?_ (le_add_of_nonneg_right <| sq_nonneg _)
  rw [sub_le_sub_iff_left, ← le_div_iff₀' (show (0 : ℝ) < 2 by simp), div_div,
    one_div_le coe_m_add_one_pos, one_div_div]
  · refine le_trans ?_ (le_add_of_nonneg_right zero_le_one)
    norm_num
    apply hundred_div_ε_pow_five_le_m hPα hPε
  sz_positivity

private theorem m_add_one_div_m_le_one_add [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) :
    ((m + 1 : ℝ) / m) ^ 2 ≤ ↑1 + ε ^ 5 / 49 := by
  have : 0 ≤ ε := by sz_positivity
  rw [same_add_div (by sz_positivity)]
  calc
    _ ≤ (1 + ε ^ 5 / 100) ^ 2 := by
      gcongr (1 + ?_) ^ 2
      rw [← one_div_div (100 : ℝ)]
      exact one_div_le_one_div_of_le (by sz_positivity) (hundred_div_ε_pow_five_le_m hPα hPε)
    _ = 1 + ε ^ 5 * (50⁻¹ + ε ^ 5 / 10000) := by ring
    _ ≤ 1 + ε ^ 5 * (50⁻¹ + 1 ^ 5 / 10000) := by gcongr
    _ ≤ 1 + ε ^ 5 * 49⁻¹ := by gcongr; norm_num
    _ = 1 + ε ^ 5 / 49 := by rw [div_eq_mul_inv]

private theorem density_sub_eps_le_sum_density_div_card [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    (G.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / 50 ≤
    (∑ ab ∈ A.product B, (G.edgeDensity ab.1 ab.2 : ℝ)) / (#A * #B) := by
  have : ↑(G.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / ↑50 ≤
      (↑1 - ε ^ 5 / 50) * G.edgeDensity (A.biUnion id) (B.biUnion id) := by
    rw [sub_mul, one_mul, sub_le_sub_iff_left]
    refine mul_le_of_le_one_right (by sz_positivity) ?_
    exact mod_cast G.edgeDensity_le_one _ _
  refine this.trans ?_
  conv_rhs => -- Porting note: LHS and RHS need separate treatment to get the desired form
    simp only [SimpleGraph.edgeDensity_def, sum_div, Rat.cast_div, div_div]
  conv_lhs =>
    rw [SimpleGraph.edgeDensity_def, SimpleGraph.interedges, ← sup_eq_biUnion, ← sup_eq_biUnion,
      Rel.card_interedges_finpartition _ (ofSubset _ hA rfl) (ofSubset _ hB rfl), ofSubset_parts,
      ofSubset_parts]
    simp only [cast_sum, sum_div, mul_sum, Rat.cast_sum, Rat.cast_div,
      mul_div_left_comm ((1 : ℝ) - _)]
  push_cast
  apply sum_le_sum
  simp only [and_imp, Prod.forall, mem_product]
  rintro x y hx hy
  rw [mul_mul_mul_comm, mul_comm (#x : ℝ), mul_comm (#y : ℝ), le_div_iff₀, mul_assoc]
  · refine mul_le_of_le_one_right (cast_nonneg _) ?_
    rw [div_mul_eq_mul_div, ← mul_assoc, mul_assoc]
    refine div_le_one_of_le₀ ?_ (by positivity)
    refine (mul_le_mul_of_nonneg_right (one_sub_le_m_div_m_add_one_sq hPα hPε) ?_).trans ?_
    · exact mod_cast _root_.zero_le _
    rw [sq, mul_mul_mul_comm, mul_comm ((m : ℝ) / _), mul_comm ((m : ℝ) / _)]
    gcongr
    · apply le_sum_card_subset_chunk_parts hA hx
    · apply le_sum_card_subset_chunk_parts hB hy
  refine mul_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_) <;> rw [cast_pos, Finset.card_pos]
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]

private theorem sum_density_div_card_le_density_add_eps [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    (∑ ab ∈ A.product B, G.edgeDensity ab.1 ab.2 : ℝ) / (#A * #B) ≤
    G.edgeDensity (A.biUnion id) (B.biUnion id) + ε ^ 5 / 49 := by
  have : (↑1 + ε ^ 5 / ↑49) * G.edgeDensity (A.biUnion id) (B.biUnion id) ≤
      G.edgeDensity (A.biUnion id) (B.biUnion id) + ε ^ 5 / 49 := by
    rw [add_mul, one_mul, add_le_add_iff_left]
    refine mul_le_of_le_one_right (by sz_positivity) ?_
    exact mod_cast G.edgeDensity_le_one _ _
  refine le_trans ?_ this
  conv_lhs => -- Porting note: LHS and RHS need separate treatment to get the desired form
    simp only [SimpleGraph.edgeDensity, edgeDensity, sum_div, Rat.cast_div, div_div]
  conv_rhs =>
    rw [SimpleGraph.edgeDensity, edgeDensity, ← sup_eq_biUnion, ← sup_eq_biUnion,
      Rel.card_interedges_finpartition _ (ofSubset _ hA rfl) (ofSubset _ hB rfl)]
    simp only [cast_sum, mul_sum, sum_div, Rat.cast_sum, Rat.cast_div,
      mul_div_left_comm ((1 : ℝ) + _)]
  push_cast
  apply sum_le_sum
  simp only [and_imp, Prod.forall, mem_product, show A.product B = A ×ˢ B by rfl]
  intro x y hx hy
  rw [mul_mul_mul_comm, mul_comm (#x : ℝ), mul_comm (#y : ℝ), div_le_iff₀, mul_assoc]
  · refine le_mul_of_one_le_right (cast_nonneg _) ?_
    rw [div_mul_eq_mul_div, one_le_div]
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (m_add_one_div_m_le_one_add hPα hPε hε₁) ?_)
      · rw [sq, mul_mul_mul_comm, mul_comm (_ / (m : ℝ)), mul_comm (_ / (m : ℝ))]
        gcongr
        exacts [sum_card_subset_chunk_parts_le (by sz_positivity) hA hx,
          sum_card_subset_chunk_parts_le (by sz_positivity) hB hy]
      · exact mod_cast _root_.zero_le _
    rw [← cast_mul, cast_pos]
    apply mul_pos <;> rw [Finset.card_pos, sup_eq_biUnion, biUnion_nonempty]
    · exact ⟨_, hx, nonempty_of_mem_parts _ (hA hx)⟩
    · exact ⟨_, hy, nonempty_of_mem_parts _ (hB hy)⟩
  refine mul_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_) <;> rw [cast_pos, Finset.card_pos]
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]

private theorem average_density_near_total_density [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    |(∑ ab ∈ A.product B, G.edgeDensity ab.1 ab.2 : ℝ) / (#A * #B) -
      G.edgeDensity (A.biUnion id) (B.biUnion id)| ≤ ε ^ 5 / 49 := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add']
    exact sum_density_div_card_le_density_add_eps hPα hPε hε₁ hA hB
  suffices (G.edgeDensity (A.biUnion id) (B.biUnion id) : ℝ) -
      (∑ ab ∈ A.product B, (G.edgeDensity ab.1 ab.2 : ℝ)) / (#A * #B) ≤ ε ^ 5 / 50 by
    apply this.trans
    gcongr <;> [sz_positivity; norm_num]
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  apply density_sub_eps_le_sum_density_div_card hPα hPε hA hB

private theorem edgeDensity_chunk_aux [Nonempty α] (hP)
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    ((∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (G.edgeDensity ab.1 ab.2 : ℝ)) / ↑16 ^ #P.parts) ^ 2 := by
  obtain hGε | hGε := le_total (G.edgeDensity U V : ℝ) (ε ^ 5 / 50)
  · refine (sub_nonpos_of_le <| (sq_le ?_ ?_).trans <| hGε.trans ?_).trans (sq_nonneg _)
    · exact mod_cast G.edgeDensity_nonneg _ _
    · exact mod_cast G.edgeDensity_le_one _ _
    · exact div_le_div_of_nonneg_left (by sz_positivity) (by simp) (by norm_num)
  rw [← sub_nonneg] at hGε
  have : 0 ≤ ε := by sz_positivity
  calc
    _ = G.edgeDensity U V ^ 2 - 1 * ε ^ 5 / 25 + 0 ^ 10 / 2500 := by ring
    _ ≤ G.edgeDensity U V ^ 2 - G.edgeDensity U V * ε ^ 5 / 25 + ε ^ 10 / 2500 := by
      gcongr; exact mod_cast G.edgeDensity_le_one ..
    _ = (G.edgeDensity U V - ε ^ 5 / 50) ^ 2 := by ring
    _ ≤ _ := by
      gcongr
      have rflU := Subset.refl (chunk hP G ε hU).parts
      have rflV := Subset.refl (chunk hP G ε hV).parts
      refine (le_trans ?_ <| density_sub_eps_le_sum_density_div_card hPα hPε rflU rflV).trans ?_
      · rw [biUnion_parts, biUnion_parts]
      · rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ← cast_mul, ← mul_pow, cast_pow]
        norm_cast

private theorem abs_density_star_sub_density_le_eps (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUV' : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    |(G.edgeDensity ((star hP G ε hU V).biUnion id) ((star hP G ε hV U).biUnion id) : ℝ) -
      G.edgeDensity (G.nonuniformWitness ε U V) (G.nonuniformWitness ε V U)| ≤ ε / 5 := by
  convert abs_edgeDensity_sub_edgeDensity_le_two_mul G.Adj
    (biUnion_star_subset_nonuniformWitness hP G ε hU V)
    (biUnion_star_subset_nonuniformWitness hP G ε hV U) (by sz_positivity)
    (one_sub_eps_mul_card_nonuniformWitness_le_card_star hV hUV' hUV hPε hε₁)
    (one_sub_eps_mul_card_nonuniformWitness_le_card_star hU hUV'.symm (fun hVU => hUV hVU.symm)
      hPε hε₁) using 1
  linarith

private theorem eps_le_card_star_div [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) (hU : U ∈ P.parts) (hV : V ∈ P.parts)
    (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V) :
    ↑4 / ↑5 * ε ≤ #(star hP G ε hU V) / ↑4 ^ #P.parts := by
  have hm : (0 : ℝ) ≤ 1 - (↑m)⁻¹ := sub_nonneg_of_le (inv_le_one_of_one_le₀ <| one_le_m_coe hPα)
  have hε : 0 ≤ 1 - ε / 10 :=
    sub_nonneg_of_le (div_le_one_of_le₀ (hε₁.trans <| by simp) <| by norm_num)
  have hε₀ : 0 < ε := by sz_positivity
  calc
    4 / 5 * ε = (1 - 1 / 10) * (1 - 9⁻¹) * ε := by norm_num
    _ ≤ (1 - ε / 10) * (1 - (↑m)⁻¹) * (#(G.nonuniformWitness ε U V) / #U) := by
        gcongr
        exacts [mod_cast (show 9 ≤ 100 by simp).trans (hundred_le_m hPα hPε hε₁),
          (le_div_iff₀' <| cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos).2 <|
           G.le_card_nonuniformWitness hunif]
    _ = (1 - ε / 10) * #(G.nonuniformWitness ε U V) * ((1 - (↑m)⁻¹) / #U) := by
      rw [mul_assoc, mul_assoc, mul_div_left_comm]
    _ ≤ #((star hP G ε hU V).biUnion id) * ((1 - (↑m)⁻¹) / #U) := by
      gcongr
      exact one_sub_eps_mul_card_nonuniformWitness_le_card_star hV hUV hunif hPε hε₁
    _ ≤ #(star hP G ε hU V) * (m + 1) * ((1 - (↑m)⁻¹) / #U) := by
      gcongr
      exact card_biUnion_star_le_m_add_one_card_star_mul
    _ ≤ #(star hP G ε hU V) * (m + ↑1) * ((↑1 - (↑m)⁻¹) / (↑4 ^ #P.parts * m)) := by
      gcongr
      · sz_positivity
      · exact pow_mul_m_le_card_part hP hU
    _ ≤ #(star hP G ε hU V) / ↑4 ^ #P.parts := by
      rw [mul_assoc, mul_comm ((4 : ℝ) ^ #P.parts), ← div_div, ← mul_div_assoc, ← mul_comm_div]
      refine mul_le_of_le_one_right (by positivity) ?_
      have hm : (0 : ℝ) < m := by sz_positivity
      rw [mul_div_assoc', div_le_one hm, ← one_div, one_sub_div hm.ne', mul_div_assoc',
        div_le_iff₀ hm]
      linarith

/-!
### Final bounds

Those inequalities are the end result of all this hard work.
-/


/-- Lower bound on the edge densities between non-uniform parts of `SzemerediRegularity.star`. -/
private theorem edgeDensity_star_not_uniform [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUVne : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    ↑3 / ↑4 * ε ≤
    |(∑ ab ∈ (star hP G ε hU V).product (star hP G ε hV U), (G.edgeDensity ab.1 ab.2 : ℝ)) /
      (#(star hP G ε hU V) * #(star hP G ε hV U)) -
        (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
          (G.edgeDensity ab.1 ab.2 : ℝ)) / (16 : ℝ) ^ #P.parts| := by
  rw [show (16 : ℝ) = ↑4 ^ 2 by norm_num, pow_right_comm, sq ((4 : ℝ) ^ _)]
  set p : ℝ :=
    (∑ ab ∈ (star hP G ε hU V).product (star hP G ε hV U), (G.edgeDensity ab.1 ab.2 : ℝ)) /
      (#(star hP G ε hU V) * #(star hP G ε hV U))
  set q : ℝ :=
    (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (G.edgeDensity ab.1 ab.2 : ℝ)) / (↑4 ^ #P.parts * ↑4 ^ #P.parts)
  set r : ℝ := ↑(G.edgeDensity ((star hP G ε hU V).biUnion id) ((star hP G ε hV U).biUnion id))
  set s : ℝ := ↑(G.edgeDensity (G.nonuniformWitness ε U V) (G.nonuniformWitness ε V U))
  set t : ℝ := ↑(G.edgeDensity U V)
  have hrs : |r - s| ≤ ε / 5 := abs_density_star_sub_density_le_eps hPε hε₁ hUVne hUV
  have hst : ε ≤ |s - t| := by
    -- After https://github.com/leanprover/lean4/pull/2734, we need to do the zeta reduction before `mod_cast`.
    unfold s t
    exact mod_cast G.nonuniformWitness_spec hUVne hUV
  have hpr : |p - r| ≤ ε ^ 5 / 49 :=
    average_density_near_total_density hPα hPε hε₁ star_subset_chunk star_subset_chunk
  have hqt : |q - t| ≤ ε ^ 5 / 49 := by
    have := average_density_near_total_density hPα hPε hε₁
      (Subset.refl (chunk hP G ε hU).parts) (Subset.refl (chunk hP G ε hV).parts)
    simp_rw [← sup_eq_biUnion, sup_parts, card_chunk (m_pos hPα).ne', cast_pow] at this
    norm_num at this
    exact this
  have hε' : ε ^ 5 ≤ ε := by
    simpa using pow_le_pow_of_le_one (by sz_positivity) hε₁ (show 1 ≤ 5 by simp)
  rw [abs_sub_le_iff] at hrs hpr hqt
  rw [le_abs] at hst ⊢
  cases hst
  · left; linarith
  · right; linarith

/-- Lower bound on the edge densities between non-uniform parts of `SzemerediRegularity.increment`.
-/
theorem edgeDensity_chunk_not_uniform [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts}
    (hUVne : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 + ε ^ 4 / ↑3 ≤
    (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / ↑16 ^ #P.parts :=
  calc
    ↑(G.edgeDensity U V) ^ 2 - ε ^ 5 / 25 + ε ^ 4 / ↑3 ≤ ↑(G.edgeDensity U V) ^ 2 - ε ^ 5 / ↑25 +
        #(star hP G ε hU V) * #(star hP G ε hV U) / ↑16 ^ #P.parts *
          (↑9 / ↑16) * ε ^ 2 := by
      gcongr
      have Ul : 4 / 5 * ε ≤ #(star hP G ε hU V) / _ :=
        eps_le_card_star_div hPα hPε hε₁ hU hV hUVne hUV
      have Vl : 4 / 5 * ε ≤ #(star hP G ε hV U) / _ :=
        eps_le_card_star_div hPα hPε hε₁ hV hU hUVne.symm fun h => hUV h.symm
      rw [show (16 : ℝ) = ↑4 ^ 2 by norm_num, pow_right_comm, sq ((4 : ℝ) ^ _), ←
        _root_.div_mul_div_comm, mul_assoc]
      have : 0 < ε := by sz_positivity
      have UVl := mul_le_mul Ul Vl (by positivity) ?_
      swap
      · -- This seems faster than `exact div_nonneg (by positivity) (by positivity)` and *much*
        -- (tens of seconds) faster than `positivity` on its own.
        apply div_nonneg <;> positivity
      refine le_trans ?_ (mul_le_mul_of_nonneg_right UVl ?_)
      · norm_num
        nlinarith
      · norm_num
        positivity
    _ ≤ (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
        (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / ↑16 ^ #P.parts := by
      have t : (star hP G ε hU V).product (star hP G ε hV U) ⊆
          (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts :=
        product_subset_product star_subset_chunk star_subset_chunk
      have hε : 0 ≤ ε := by sz_positivity
      have sp : ∀ (a b : Finset (Finset α)), a.product b = a ×ˢ b := fun a b => rfl
      have := add_div_le_sum_sq_div_card t (fun x => (G.edgeDensity x.1 x.2 : ℝ))
        ((G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25) (show 0 ≤ 3 / 4 * ε by linarith) ?_ ?_
      · simp_rw [sp, card_product, card_chunk (m_pos hPα).ne', ← mul_pow, cast_pow, mul_pow,
          div_pow, ← mul_assoc] at this
        norm_num at this
        exact this
      · simp_rw [sp, card_product, card_chunk (m_pos hPα).ne', ← mul_pow]
        norm_num
        exact edgeDensity_star_not_uniform hPα hPε hε₁ hUVne hUV
      · rw [sp, card_product]
        apply (edgeDensity_chunk_aux hP hPα hPε hU hV).trans
        · rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ← mul_pow]
          simp

/-- Lower bound on the edge densities between parts of `SzemerediRegularity.increment`. This is the
blanket lower bound used the uniform parts. -/
theorem edgeDensity_chunk_uniform [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / ↑16 ^ #P.parts := by
  apply (edgeDensity_chunk_aux (hP := hP) hPα hPε hU hV).trans
  have key : (16 : ℝ) ^ #P.parts = #((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts) := by
    rw [card_product, cast_mul, card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ←
      cast_mul, ← mul_pow]; norm_cast
  simp_rw [key]
  convert sum_div_card_sq_le_sum_sq_div_card (α := ℝ)

end SzemerediRegularity

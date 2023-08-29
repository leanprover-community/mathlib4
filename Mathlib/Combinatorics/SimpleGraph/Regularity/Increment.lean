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

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open scoped BigOperators Classical SzemerediRegularity.Positivity

variable {α : Type*} [Fintype α] {P : Finpartition (univ : Finset α)} (hP : P.IsEquipartition)
  (G : SimpleGraph α) (ε : ℝ)

local notation3 (prettyPrint := false)
  "m" => (card α / stepBound P.parts.card : ℕ)

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
    (mul_le_mul_left' (pow_le_pow_of_le_left' (by norm_num) _) _).trans hPα
  have hPpos : 0 < stepBound P.parts.card := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  -- ⊢ Finset.card (increment hP G ε).parts = stepBound (Finset.card P.parts)
  rw [increment, card_bind]
  -- ⊢ ∑ A in attach P.parts, Finset.card (chunk hP G ε (_ : ↑A ∈ P.parts)).parts = …
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  -- ⊢ ∑ x in attach (filter (fun x => Finset.card ↑x = Fintype.card α / stepBound  …
  rw [sum_const_nat, sum_const_nat, card_attach, card_attach]; rotate_left
  any_goals exact fun x hx => card_parts_equitabilise _ _ (Nat.div_pos hPα' hPpos).ne'
  -- ⊢ Finset.card (filter (fun x => Finset.card ↑x = Fintype.card α / stepBound (F …
  rw [Nat.sub_add_cancel a_add_one_le_four_pow_parts_card,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), ← add_mul]
  congr
  -- ⊢ Finset.card (filter (fun x => Finset.card ↑x = Fintype.card α / stepBound (F …
  rw [filter_card_add_filter_neg_card_eq_card, card_attach]
  -- 🎉 no goals
#align szemeredi_regularity.card_increment SzemerediRegularity.card_increment

theorem increment_isEquipartition (hP : P.IsEquipartition) (G : SimpleGraph α) (ε : ℝ) :
    (increment hP G ε).IsEquipartition := by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  -- ⊢ ∃ b, ∀ (a : Finset α), a ∈ ↑(increment hP G ε).parts → Finset.card a = b ∨ F …
  refine' ⟨m, fun A hA => _⟩
  -- ⊢ Finset.card A = Fintype.card α / stepBound (Finset.card P.parts) ∨ Finset.ca …
  rw [mem_coe, increment, mem_bind] at hA
  -- ⊢ Finset.card A = Fintype.card α / stepBound (Finset.card P.parts) ∨ Finset.ca …
  obtain ⟨U, hU, hA⟩ := hA
  -- ⊢ Finset.card A = Fintype.card α / stepBound (Finset.card P.parts) ∨ Finset.ca …
  exact card_eq_of_mem_parts_chunk hA
  -- 🎉 no goals
#align szemeredi_regularity.increment_is_equipartition SzemerediRegularity.increment_isEquipartition

private theorem distinct_pairs_increment :
    (P.parts.offDiag.attach.biUnion fun UV =>
      (chunk hP G ε (mem_offDiag.1 UV.2).1).parts ×ˢ
      (chunk hP G ε (mem_offDiag.1 UV.2).2.1).parts) ⊆
    (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  -- ⊢ ((Ui, Vj) ∈ Finset.biUnion (attach (offDiag P.parts)) fun UV => (chunk hP G  …
  simp only [increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists, exists_and_left,
    exists_prop, mem_product, mem_attach, true_and_iff, Subtype.exists, and_imp, mem_offDiag,
    forall_exists_index, bex_imp, Ne.def]
  refine' fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, _⟩
  -- ⊢ ¬Ui = Vj
  rintro rfl
  -- ⊢ False
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  -- ⊢ False
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)

/-- The contribution to `Finpartition.energy` of a pair of distinct parts of a `Finpartition`. -/
private noncomputable def pairContrib (G : SimpleGraph α) (ε : ℝ) (hP : P.IsEquipartition)
    (x : { x // x ∈ P.parts.offDiag }) : ℚ :=
  ∑ i in (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts,
    (G.edgeDensity i.fst i.snd : ℚ) ^ 2

theorem offDiag_pairs_le_increment_energy :
    ∑ x in P.parts.offDiag.attach, pairContrib G ε hP x / ((increment hP G ε).parts.card : ℚ) ^ 2 ≤
    (increment hP G ε).energy G := by
  simp_rw [pairContrib, ← sum_div]
  -- ⊢ (∑ x in attach (offDiag P.parts), ∑ i in (chunk hP G ε (_ : (↑x).fst ∈ P.par …
  refine' div_le_div_of_le_of_nonneg (α := ℚ) _ (sq_nonneg _)
  -- ⊢ ∑ x in attach (offDiag P.parts), ∑ i in (chunk hP G ε (_ : (↑x).fst ∈ P.part …
  rw [← sum_biUnion]
  -- ⊢ ∑ x in Finset.biUnion (attach (offDiag P.parts)) fun x => (chunk hP G ε (_ : …
  · exact sum_le_sum_of_subset_of_nonneg distinct_pairs_increment fun i _ _ => sq_nonneg _
    -- 🎉 no goals
  simp only [Set.PairwiseDisjoint, Function.onFun, disjoint_left, inf_eq_inter, mem_inter,
    mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  -- ⊢ False
  rw [mem_offDiag] at hs ht
  -- ⊢ False
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  -- ⊢ False
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
  -- ⊢ False
  exact hst (Subtype.ext_val <| Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
        P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb) <|
          Finpartition.le _ huv₂.2 hb)
#align szemeredi_regularity.off_diag_pairs_le_increment_energy SzemerediRegularity.offDiag_pairs_le_increment_energy

theorem pairContrib_lower_bound [Nonempty α] (x : { i // i ∈ P.parts.offDiag }) (hε₁ : ε ≤ 1)
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : ↑100 ≤ ↑4 ^ P.parts.card * ε ^ 5) :
    ((G.edgeDensity x.1.1 x.1.2 : ℝ) ^ 2 - ε ^ 5 / ↑25 +
      if G.IsUniform ε x.1.1 x.1.2 then (0 : ℝ) else ε ^ 4 / 3) ≤
    pairContrib G ε hP x / ↑16 ^ P.parts.card := by
  rw [pairContrib]
  -- ⊢ (↑(edgeDensity G (↑x).fst (↑x).snd) ^ 2 - ε ^ 5 / 25 + if SimpleGraph.IsUnif …
  push_cast
  -- ⊢ (↑(edgeDensity G (↑x).fst (↑x).snd) ^ 2 - ε ^ 5 / 25 + if SimpleGraph.IsUnif …
  split_ifs with h
  -- ⊢ ↑(edgeDensity G (↑x).fst (↑x).snd) ^ 2 - ε ^ 5 / 25 + 0 ≤ (∑ x in (chunk hP  …
  · rw [add_zero]
    -- ⊢ ↑(edgeDensity G (↑x).fst (↑x).snd) ^ 2 - ε ^ 5 / 25 ≤ (∑ x in (chunk hP G ε  …
    exact edgeDensity_chunk_uniform hPα hPε _ _
    -- 🎉 no goals
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h
    -- 🎉 no goals
#align szemeredi_regularity.pair_contrib_lower_bound SzemerediRegularity.pairContrib_lower_bound

theorem uniform_add_nonuniform_eq_offDiag_pairs [Nonempty α] (hε₁ : ε ≤ 1) (hP₇ : 7 ≤ P.parts.card)
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) (hPε : ↑100 ≤ ↑4 ^ P.parts.card * ε ^ 5)
    (hPG : ¬P.IsUniform G ε) :
    (∑ x in P.parts.offDiag, (G.edgeDensity x.1 x.2 : ℝ) ^ 2 +
      ↑P.parts.card ^ 2 * (ε ^ 5 / 4) : ℝ) / (P.parts.card : ℝ) ^ 2 ≤
    ∑ x in P.parts.offDiag.attach,
      (pairContrib G ε hP x : ℝ) / ((increment hP G ε).parts.card : ℝ) ^ 2 := by
  conv_rhs =>
    rw [← sum_div, card_increment hPα hPG, stepBound, ← Nat.cast_pow, mul_pow, pow_right_comm,
      Nat.cast_mul, mul_comm, ← div_div, show 4 ^ 2 = 16 by norm_num, sum_div]
  rw [← Nat.cast_pow, Nat.cast_pow 16]
  -- ⊢ (∑ x in offDiag P.parts, ↑(edgeDensity G x.fst x.snd) ^ 2 + ↑(Finset.card P. …
  refine' div_le_div_of_le_of_nonneg _ (Nat.cast_nonneg _)
  -- ⊢ ∑ x in offDiag P.parts, ↑(edgeDensity G x.fst x.snd) ^ 2 + ↑(Finset.card P.p …
  norm_num
  -- ⊢ ∑ x in offDiag P.parts, ↑(edgeDensity G x.fst x.snd) ^ 2 + ↑(Finset.card P.p …
  trans ∑ x in P.parts.offDiag.attach, ((G.edgeDensity x.1.1 x.1.2 : ℝ) ^ 2 - ε ^ 5 / ↑25 +
    if G.IsUniform ε x.1.1 x.1.2 then (0 : ℝ) else ε ^ 4 / 3 : ℝ)
  swap
  -- ⊢ ∑ x in attach (offDiag P.parts), (↑(edgeDensity G (↑x).fst (↑x).snd) ^ 2 - ε …
  · exact sum_le_sum fun i _ => pairContrib_lower_bound i hε₁ hPα hPε
    -- 🎉 no goals
  have :
      ∑ x in P.parts.offDiag.attach, ((G.edgeDensity x.1.1 x.1.2 : ℝ) ^ 2 - ε ^ 5 / ↑25 +
        if G.IsUniform ε x.1.1 x.1.2 then (0 : ℝ) else ε ^ 4 / 3 : ℝ) =
      ∑ x in P.parts.offDiag, ((G.edgeDensity x.1 x.2 : ℝ) ^ 2 - ε ^ 5 / ↑25 +
        if G.IsUniform ε x.1 x.2 then (0 : ℝ) else ε ^ 4 / 3) := by
    convert sum_attach (β := ℝ); rfl
  rw [this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_ite, sum_const_zero,
    zero_add, sum_const, nsmul_eq_mul, ← Finpartition.nonUniforms]
  rw [Finpartition.IsUniform, not_le] at hPG
  -- ⊢ ∑ x in offDiag P.parts, ↑(edgeDensity G x.fst x.snd) ^ 2 + ↑(Finset.card P.p …
  refine' le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right hPG.le <| by positivity) _)
  -- ⊢ ∑ x in offDiag P.parts, ↑(edgeDensity G x.fst x.snd) ^ 2 + ↑(Finset.card P.p …
  conv_rhs =>
    enter [1, 2]
    rw [offDiag_card]
    conv => enter [1, 1, 2]; rw [← mul_one P.parts.card]
    rw [← Nat.mul_sub_left_distrib]
  simp_rw [mul_assoc, sub_add_eq_add_sub, add_sub_assoc, ← mul_sub_left_distrib, mul_div_assoc' ε,
    ← pow_succ, show 4 + 1 = 5 by rfl, div_eq_mul_one_div (ε ^ 5), ← mul_sub_left_distrib,
    mul_left_comm _ (ε ^ 5), sq, Nat.cast_mul, mul_assoc, ← mul_assoc (ε ^ 5)]
  refine' add_le_add_left (mul_le_mul_of_nonneg_left _ <| by sz_positivity) _
  -- ⊢ ↑(Finset.card P.parts) * (1 / 4) ≤ ↑(Finset.card P.parts - 1) * (1 / 3 - 1 / …
  rw [Nat.cast_sub (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos, mul_sub_right_distrib,
    Nat.cast_one, one_mul, le_sub_comm, ← mul_sub_left_distrib, ←
    div_le_iff (show (0 : ℝ) < 1 / 3 - 1 / 25 - 1 / 4 by norm_num)]
  exact le_trans (show _ ≤ (7 : ℝ) by norm_num) (by exact_mod_cast hP₇)
  -- 🎉 no goals
#align szemeredi_regularity.uniform_add_nonuniform_eq_off_diag_pairs SzemerediRegularity.uniform_add_nonuniform_eq_offDiag_pairs

/-- The increment partition has energy greater than the original one by a known fixed amount. -/
theorem energy_increment [Nonempty α] (hP : P.IsEquipartition) (hP₇ : 7 ≤ P.parts.card)
    (hε : ↑100 < ↑4 ^ P.parts.card * ε ^ 5) (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPG : ¬P.IsUniform G ε) (hε₁ : ε ≤ 1) :
    ↑(P.energy G) + ε ^ 5 / 4 ≤ (increment hP G ε).energy G := by
  rw [coe_energy]
  -- ⊢ (∑ uv in offDiag P.parts, ↑(edgeDensity G uv.fst uv.snd) ^ 2) / ↑(Finset.car …
  have h := uniform_add_nonuniform_eq_offDiag_pairs (hP := hP) hε₁ hP₇ hPα hε.le hPG
  -- ⊢ (∑ uv in offDiag P.parts, ↑(edgeDensity G uv.fst uv.snd) ^ 2) / ↑(Finset.car …
  rw [add_div, mul_div_cancel_left] at h
  -- ⊢ (∑ uv in offDiag P.parts, ↑(edgeDensity G uv.fst uv.snd) ^ 2) / ↑(Finset.car …
  exact h.trans (by exact_mod_cast offDiag_pairs_le_increment_energy)
  -- ⊢ ↑(Finset.card P.parts) ^ 2 ≠ 0
  positivity
  -- 🎉 no goals
#align szemeredi_regularity.energy_increment SzemerediRegularity.energy_increment

end SzemerediRegularity

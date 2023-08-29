/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Increment

#align_import combinatorics.simple_graph.regularity.lemma from "leanprover-community/mathlib"@"1d4d3ca5ec44693640c4f5e407a6b611f77accc8"

/-!
# Szemerédi's Regularity Lemma

In this file, we prove Szemerédi's Regularity Lemma (aka SRL). This is a landmark result in
combinatorics roughly stating that any sufficiently big graph behaves like a random graph. This is
useful because random graphs are well-behaved in many aspects.

More precisely, SRL states that for any `ε > 0` and integer `l` there exists a bound `M` such that
any graph on at least `l` vertices can be partitioned into at least `l` parts and at most `M` parts
such that the resulting partitioned graph is `ε`-uniform.

This statement is very robust to tweaking and many different versions exist. Here, we prove the
version where the resulting partition is equitable (aka an *equipartition*), namely all parts have
the same size up to a difference of `1`.

The proof we formalise goes as follows:
1. Define an auxiliary measure of edge density, the *energy* of a partition.
2. Start with an arbitrary equipartition of size `l`.
3. Repeatedly break up the parts of the current equipartition in a big but controlled number of
  parts. The key point is to break along the witnesses of non-uniformity, so that a lesser portion
  of the pairs of parts are non-`ε`-uniform.
4. Check that this results in an equipartition with an energy greater than the energy of the current
  partition, plus some constant.
5. Since the energy is between zero and one, we can't run this process forever. Check that when the
  process stops we have an `ε`-uniform equipartition.

This file only contains the final result. The supporting material is spread across the
`Combinatorics/SimpleGraph/Regularity` folder:
* `Combinatorics/SimpleGraph/Regularity/Bound`: Definition of the bound on the number of parts.
  Numerical inequalities involving the lemma constants.
* `Combinatorics/SimpleGraph/Regularity/Energy`: Definition of the energy of a simple graph along a
  partition.
* `Combinatorics/SimpleGraph/Regularity/Uniform`: Definition of uniformity of a simple graph along
  a pair of parts and along a partition.
* `Combinatorics/SimpleGraph/Regularity/Equitabilise`: Construction of an equipartition with
  a prescribed number of parts of each size and almost refining a given partition.
* `Combinatorics/SimpleGraph/Regularity/Chunk`: Break up one part of the current equipartition.
  Check that density between non-uniform parts increases, and that density between uniform parts
  doesn't decrease too much.
* `Combinatorics/SimpleGraph/Regularity/Increment`: Gather all those broken up parts into the new
  equipartition (aka *increment partition*). Check that energy increases by at least a fixed amount.
* `Combinatorics/SimpleGraph/Regularity/Lemma`: Wrap everything up into an induction on the energy.

## TODO

We currently only prove the equipartition version of SRL.

* Prove the diagonal version.
* Prove the degree version.
* Define the regularity of a partition and prove the corresponding version.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finpartition Finset Fintype Function SzemerediRegularity

open scoped Classical

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {α : Type*} [Fintype α] (G : SimpleGraph α) {ε : ℝ} {l : ℕ}

/-- Effective **Szemerédi Regularity Lemma**: For any sufficiently large graph, there is an
`ε`-uniform equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity (hε : 0 < ε) (hl : l ≤ card α) :
    ∃ P : Finpartition univ,
      P.IsEquipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ bound ε l ∧ P.IsUniform G ε := by
  obtain hα | hα := le_total (card α) (bound ε l)
  -- ⊢ ∃ P, IsEquipartition P ∧ l ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ bou …
  -- If `card α ≤ bound ε l`, then the partition into singletons is acceptable.
  · refine' ⟨⊥, bot_isEquipartition _, _⟩
    -- ⊢ l ≤ Finset.card ⊥.parts ∧ Finset.card ⊥.parts ≤ bound ε l ∧ IsUniform ⊥ G ε
    rw [card_bot, card_univ]
    -- ⊢ l ≤ Fintype.card α ∧ Fintype.card α ≤ bound ε l ∧ IsUniform ⊥ G ε
    exact ⟨hl, hα, botIsUniform _ hε⟩
    -- 🎉 no goals
  -- Else, let's start from a dummy equipartition of size `initialBound ε l`.
  let t := initialBound ε l
  -- ⊢ ∃ P, IsEquipartition P ∧ l ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ bou …
  have htα : t ≤ (univ : Finset α).card :=
    (initialBound_le_bound _ _).trans (by rwa [Finset.card_univ])
  obtain ⟨dum, hdum₁, hdum₂⟩ :=
    exists_equipartition_card_eq (univ : Finset α) (initialBound_pos _ _).ne' htα
  obtain hε₁ | hε₁ := le_total 1 ε
  -- ⊢ ∃ P, IsEquipartition P ∧ l ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ bou …
  -- If `ε ≥ 1`, then this dummy equipartition is `ε`-uniform, so we're done.
  · exact ⟨dum, hdum₁, (le_initialBound ε l).trans hdum₂.ge,
      hdum₂.le.trans (initialBound_le_bound ε l), (dum.isUniformOne G).mono hε₁⟩
  -- Else, set up the induction on energy. We phrase it through the existence for each `i` of an
  -- equipartition of size bounded by `stepBound^[i] (initialBound ε l)` and which is either
  -- `ε`-uniform or has energy at least `ε ^ 5 / 4 * i`.
  have : Nonempty α := by
    rw [← Fintype.card_pos_iff]
    exact (bound_pos _ _).trans_le hα
  suffices h : ∀ i, ∃ P : Finpartition (univ : Finset α), P.IsEquipartition ∧ t ≤ P.parts.card ∧
    P.parts.card ≤ stepBound^[i] t ∧ (P.IsUniform G ε ∨ ε ^ 5 / 4 * i ≤ P.energy G)
  -- For `i > 4 / ε ^ 5` we know that the partition we get can't have energy `≥ ε ^ 5 / 4 * i > 1`,
  -- so it must instead be `ε`-uniform and we won.
  · obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (⌊4 / ε ^ 5⌋₊ + 1)
    -- ⊢ ∃ P, IsEquipartition P ∧ l ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ bou …
    refine' ⟨P, hP₁, (le_initialBound _ _).trans hP₂, hP₃.trans _,
      hP₄.resolve_right fun hPenergy => lt_irrefl (1 : ℝ) _⟩
    · rw [iterate_succ_apply']
      -- ⊢ stepBound (stepBound^[⌊↑4 / ε ^ 5⌋₊] t) ≤ bound ε l
      exact mul_le_mul_left' (pow_le_pow_of_le_left (by norm_num) (by norm_num) _) _
      -- 🎉 no goals
    calc
      (1 : ℝ) = ε ^ 5 / ↑4 * (↑4 / ε ^ 5) := by
        rw [mul_comm, div_mul_div_cancel 4 (pow_pos hε 5).ne']; norm_num
      _ < ε ^ 5 / 4 * (⌊4 / ε ^ 5⌋₊ + 1) :=
        ((mul_lt_mul_left <| by positivity).2 (Nat.lt_floor_add_one _))
      _ ≤ (P.energy G : ℝ) := by rwa [← Nat.cast_add_one]
      _ ≤ 1 := by exact_mod_cast P.energy_le_one G
  -- Let's do the actual induction.
  intro i
  -- ⊢ ∃ P, IsEquipartition P ∧ t ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ ste …
  induction' i with i ih
  -- ⊢ ∃ P, IsEquipartition P ∧ t ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ ste …
  -- For `i = 0`, the dummy equipartition is enough.
  · refine' ⟨dum, hdum₁, hdum₂.ge, hdum₂.le, Or.inr _⟩
    -- ⊢ ε ^ 5 / 4 * ↑Nat.zero ≤ ↑(energy dum G)
    rw [Nat.cast_zero, mul_zero]
    -- ⊢ 0 ≤ ↑(energy dum G)
    exact_mod_cast dum.energy_nonneg G
    -- 🎉 no goals
  -- For the induction step at `i + 1`, find `P` the equipartition at `i`.
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := ih
  -- ⊢ ∃ P, IsEquipartition P ∧ t ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ ste …
  by_cases huniform : P.IsUniform G ε
  -- ⊢ ∃ P, IsEquipartition P ∧ t ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ ste …
  -- If `P` is already uniform, then no need to break it up further. We can just return `P` again.
  · refine' ⟨P, hP₁, hP₂, _, Or.inl huniform⟩
    -- ⊢ Finset.card P.parts ≤ stepBound^[Nat.succ i] t
    rw [iterate_succ_apply']
    -- ⊢ Finset.card P.parts ≤ stepBound (stepBound^[i] t)
    exact hP₃.trans (le_stepBound _)
    -- 🎉 no goals
  -- Else, `P` must instead have energy at least `ε ^ 5 / 4 * i`.
  replace hP₄ := hP₄.resolve_left huniform
  -- ⊢ ∃ P, IsEquipartition P ∧ t ≤ Finset.card P.parts ∧ Finset.card P.parts ≤ ste …
  -- We gather a few numerical facts.
  have hεl' : ↑100 < ↑4 ^ P.parts.card * ε ^ 5 :=
    (hundred_lt_pow_initialBound_mul hε l).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow (by norm_num) hP₂) <| by positivity)
  have hi : (i : ℝ) ≤ 4 / ε ^ 5 := by
    have hi : ε ^ 5 / 4 * ↑i ≤ 1 := hP₄.trans (by exact_mod_cast P.energy_le_one G)
    rw [div_mul_eq_mul_div, div_le_iff (show (0 : ℝ) < 4 by norm_num)] at hi
    norm_num at hi
    rwa [le_div_iff' (pow_pos hε _)]
  have hsize : P.parts.card ≤ stepBound^[⌊4 / ε ^ 5⌋₊] t :=
    hP₃.trans (monotone_iterate_of_id_le le_stepBound (Nat.le_floor hi) _)
  have hPα : P.parts.card * 16 ^ P.parts.card ≤ card α :=
    (Nat.mul_le_mul hsize (Nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hα
  -- We return the increment equipartition of `P`, which has energy `≥ ε ^ 5 / 4 * (i + 1)`.
  refine' ⟨increment hP₁ G ε, increment_isEquipartition hP₁ G ε, _, _, Or.inr <| le_trans _ <|
    energy_increment hP₁ ((seven_le_initialBound ε l).trans hP₂) hεl' hPα huniform hε₁⟩
  · rw [card_increment hPα huniform]
    -- ⊢ t ≤ stepBound (Finset.card P.parts)
    exact hP₂.trans (le_stepBound _)
    -- 🎉 no goals
  · rw [card_increment hPα huniform, iterate_succ_apply']
    -- ⊢ stepBound (Finset.card P.parts) ≤ stepBound (stepBound^[i] t)
    exact stepBound_mono hP₃
    -- 🎉 no goals
  · rw [Nat.cast_succ, mul_add, mul_one]
    -- ⊢ ε ^ 5 / 4 * ↑i + ε ^ 5 / 4 ≤ ↑(energy P G) + ε ^ 5 / 4
    exact add_le_add_right hP₄ _
    -- 🎉 no goals
#align szemeredi_regularity szemeredi_regularity

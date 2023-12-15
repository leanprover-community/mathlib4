/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.SetTheory.Ordinal.Basic

#align_import combinatorics.simple_graph.regularity.uniform from "leanprover-community/mathlib"@"bf7ef0e83e5b7e6c1169e97f055e58a2e4e9d52d"

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of non `ε`-uniform pairs of parts
is less than `ε`.

## Main declarations

* `SimpleGraph.IsUniform`: Graph uniformity of a pair of finsets of vertices.
* `SimpleGraph.nonuniformWitness`: `G.nonuniformWitness ε s t` and `G.nonuniformWitness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `Finpartition.nonUniforms`: Non uniform pairs of parts of a partition.
* `Finpartition.IsUniform`: Uniformity of a partition.
* `Finpartition.nonuniformWitnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset

variable {α 𝕜 : Type*} [LinearOrderedField 𝕜]

/-! ###  Graph uniformity -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

/-- A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density is close
to the density of any big enough pair of subsets. Intuitively, the edges between them are
random-like. -/
def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (s.card : 𝕜) * ε ≤ s'.card →
    (t.card : 𝕜) * ε ≤ t'.card → |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
#align simple_graph.is_uniform SimpleGraph.IsUniform

variable {G ε}

theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
  fun s' hs' t' ht' hs ht => by
  refine' (hε hs' ht' (le_trans _ hs) (le_trans _ ht)).trans_le h <;> gcongr
#align simple_graph.is_uniform.mono SimpleGraph.IsUniform.mono

theorem IsUniform.symm : Symmetric (IsUniform G ε) := fun s t h t' ht' s' hs' ht hs => by
  rw [edgeDensity_comm _ t', edgeDensity_comm _ t]
  exact h hs' ht' hs ht
#align simple_graph.is_uniform.symm SimpleGraph.IsUniform.symm

variable (G)

theorem isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align simple_graph.is_uniform_comm SimpleGraph.isUniform_comm

theorem isUniform_singleton (hε : 0 < ε) : G.IsUniform ε {a} {b} := by
  intro s' hs' t' ht' hs ht
  rw [card_singleton, Nat.cast_one, one_mul] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε ≤ 0 := by simpa using hs
    exact (hε.not_le hs).elim
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε ≤ 0 := by simpa using ht
    exact (hε.not_le ht).elim
  · rwa [sub_self, abs_zero]
#align simple_graph.is_uniform_singleton SimpleGraph.isUniform_singleton

theorem not_isUniform_zero : ¬G.IsUniform (0 : 𝕜) s t := fun h =>
  (abs_nonneg _).not_lt <| h (empty_subset _) (empty_subset _) (by simp) (by simp)
#align simple_graph.not_is_uniform_zero SimpleGraph.not_isUniform_zero

theorem isUniform_one : G.IsUniform (1 : 𝕜) s t := by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs),
    eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht), sub_self, abs_zero]
  exact zero_lt_one
#align simple_graph.is_uniform_one SimpleGraph.isUniform_one

variable {G}

theorem not_isUniform_iff :
    ¬G.IsUniform ε s t ↔ ∃ s', s' ⊆ s ∧ ∃ t', t' ⊆ t ∧ ↑s.card * ε ≤ s'.card ∧
      ↑t.card * ε ≤ t'.card ∧ ε ≤ |G.edgeDensity s' t' - G.edgeDensity s t| := by
  unfold IsUniform
  simp only [not_forall, not_lt, exists_prop, exists_and_left, Rat.cast_abs, Rat.cast_sub]
#align simple_graph.not_is_uniform_iff SimpleGraph.not_isUniform_iff

open Classical

variable (G)

/-- An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. See
`SimpleGraph.nonuniformWitness`. -/
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α) : Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).choose, (not_isUniform_iff.1 h).choose_spec.2.choose)
  else (s, t)
#align simple_graph.nonuniform_witnesses SimpleGraph.nonuniformWitnesses

theorem left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1 ⊆ s := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.1
#align simple_graph.left_nonuniform_witnesses_subset SimpleGraph.left_nonuniformWitnesses_subset

theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    (s.card : 𝕜) * ε ≤ (G.nonuniformWitnesses ε s t).1.card := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.1
#align simple_graph.left_nonuniform_witnesses_card SimpleGraph.left_nonuniformWitnesses_card

theorem right_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).2 ⊆ t := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.1
#align simple_graph.right_nonuniform_witnesses_subset SimpleGraph.right_nonuniformWitnesses_subset

theorem right_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    (t.card : 𝕜) * ε ≤ (G.nonuniformWitnesses ε s t).2.card := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.1
#align simple_graph.right_nonuniform_witnesses_card SimpleGraph.right_nonuniformWitnesses_card

theorem nonuniformWitnesses_spec (h : ¬G.IsUniform ε s t) :
    ε ≤
      |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 -
          G.edgeDensity s t| := by
  rw [nonuniformWitnesses, dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.2
#align simple_graph.nonuniform_witnesses_spec SimpleGraph.nonuniformWitnesses_spec

/-- Arbitrary witness of non-uniformity. `G.nonuniformWitness ε s t` and
`G.nonuniformWitness ε t s` form a pair of subsets witnessing the non-uniformity of `(s, t)`. If
`(s, t)` is uniform, returns `s`. -/
noncomputable def nonuniformWitness (ε : 𝕜) (s t : Finset α) : Finset α :=
  if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2
#align simple_graph.nonuniform_witness SimpleGraph.nonuniformWitness

theorem nonuniformWitness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε s t ⊆ s := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_subset h
  · exact G.right_nonuniformWitnesses_subset fun i => h i.symm
#align simple_graph.nonuniform_witness_subset SimpleGraph.nonuniformWitness_subset

theorem le_card_nonuniformWitness (h : ¬G.IsUniform ε s t) :
    (s.card : 𝕜) * ε ≤ (G.nonuniformWitness ε s t).card := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_card h
  · exact G.right_nonuniformWitnesses_card fun i => h i.symm
#align simple_graph.le_card_nonuniform_witness SimpleGraph.le_card_nonuniformWitness

theorem nonuniformWitness_spec (h₁ : s ≠ t) (h₂ : ¬G.IsUniform ε s t) : ε ≤ |G.edgeDensity
    (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) - G.edgeDensity s t| := by
  unfold nonuniformWitness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniformWitnesses_spec h₂
  · cases h₁ rfl
  · rw [if_neg (asymm gt), if_pos gt, edgeDensity_comm, edgeDensity_comm _ s]
    apply G.nonuniformWitnesses_spec fun i => h₂ i.symm
#align simple_graph.nonuniform_witness_spec SimpleGraph.nonuniformWitness_spec

end SimpleGraph

/-! ### Uniform partitions -/


variable [DecidableEq α] {A : Finset α} (P : Finpartition A) (G : SimpleGraph α)
  [DecidableRel G.Adj] {ε : 𝕜}

namespace Finpartition

open Classical

/-- The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself. -/
noncomputable def nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun uv => ¬G.IsUniform ε uv.1 uv.2
#align finpartition.non_uniforms Finpartition.nonUniforms

theorem mk_mem_nonUniforms_iff (u v : Finset α) (ε : 𝕜) :
    (u, v) ∈ P.nonUniforms G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ ¬G.IsUniform ε u v := by
  rw [nonUniforms, mem_filter, mem_offDiag, and_assoc, and_assoc]
#align finpartition.mk_mem_non_uniforms_iff Finpartition.mk_mem_nonUniforms_iff

theorem nonUniforms_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.nonUniforms G ε' ⊆ P.nonUniforms G ε :=
  monotone_filter_right _ fun _ => mt <| SimpleGraph.IsUniform.mono h
#align finpartition.non_uniforms_mono Finpartition.nonUniforms_mono

theorem nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  rintro ⟨u, v⟩
  simp only [Finpartition.mk_mem_nonUniforms_iff, Finpartition.parts_bot, mem_map, not_and,
    Classical.not_not, exists_imp]; dsimp
  rintro x ⟨_,xu⟩ y ⟨_,yv⟩ _
  rw [← xu, ← yv]
  exact G.isUniform_singleton hε
#align finpartition.non_uniforms_bot Finpartition.nonUniforms_bot

/-- A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`. -/
def IsUniform (ε : 𝕜) : Prop :=
  ((P.nonUniforms G ε).card : 𝕜) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε
#align finpartition.is_uniform Finpartition.IsUniform

theorem botIsUniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε := by
  rw [Finpartition.IsUniform, Finpartition.card_bot, nonUniforms_bot _ hε, Finset.card_empty,
    Nat.cast_zero]
  exact mul_nonneg (Nat.cast_nonneg _) hε.le
#align finpartition.bot_is_uniform Finpartition.botIsUniform

theorem isUniformOne : P.IsUniform G (1 : 𝕜) := by
  rw [IsUniform, mul_one, Nat.cast_le]
  refine' (card_filter_le _
    (fun uv => ¬SimpleGraph.IsUniform G 1 (Prod.fst uv) (Prod.snd uv))).trans _
  rw [offDiag_card, Nat.mul_sub_left_distrib, mul_one]
#align finpartition.is_uniform_one Finpartition.isUniformOne

variable {P G}

theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε ≤ ε') : P.IsUniform G ε' :=
  ((Nat.cast_le.2 <| card_le_of_subset <| P.nonUniforms_mono G h).trans hP).trans <| by gcongr
#align finpartition.is_uniform.mono Finpartition.IsUniform.mono

theorem isUniformOfEmpty (hP : P.parts = ∅) : P.IsUniform G ε := by
  simp [IsUniform, hP, nonUniforms]
#align finpartition.is_uniform_of_empty Finpartition.isUniformOfEmpty

theorem nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty :=
  nonempty_of_ne_empty fun h₁ => h <| isUniformOfEmpty h₁
#align finpartition.nonempty_of_not_uniform Finpartition.nonempty_of_not_uniform

variable (P G ε) (s : Finset α)

/-- A choice of witnesses of non-uniformity among the parts of a finpartition. -/
noncomputable def nonuniformWitnesses : Finset (Finset α) :=
  (P.parts.filter fun t => s ≠ t ∧ ¬G.IsUniform ε s t).image (G.nonuniformWitness ε s)
#align finpartition.nonuniform_witnesses Finpartition.nonuniformWitnesses

variable {P G ε s} {t : Finset α}

theorem nonuniformWitness_mem_nonuniformWitnesses (h : ¬G.IsUniform ε s t) (ht : t ∈ P.parts)
    (hst : s ≠ t) : G.nonuniformWitness ε s t ∈ P.nonuniformWitnesses G ε s :=
  mem_image_of_mem _ <| mem_filter.2 ⟨ht, hst, h⟩
#align finpartition.nonuniform_witness_mem_nonuniform_witnesses Finpartition.nonuniformWitness_mem_nonuniformWitnesses

end Finpartition

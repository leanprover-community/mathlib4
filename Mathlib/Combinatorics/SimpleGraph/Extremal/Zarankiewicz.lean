/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Rify

/-!
# The Zarankiewicz function

This file defines the **Zarankiewicz function** in terms of bipartite graphs.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

open Classical in
/-- The **Zarankiewicz function** of natural numbers `m`, `n`, `s`, and `t` is the maximum
number of edges in a `completeBipartiteGraph (Fin s) (Fin t)`-free bipartite graph with parts of
size `m` and `n`.

This is the *extremal graph theory* version of the **Zarankiewicz function**. -/
noncomputable def zarankiewicz (m n s t : ℕ) : ℕ :=
  sup { G : SimpleGraph (Fin m ⊕ Fin n) | G ≤ completeBipartiteGraph (Fin m) (Fin n)
    ∧ (completeBipartiteGraph (Fin s) (Fin t)).Free G} (#·.edgeFinset)

variable {m n s t : ℕ} {V W α β : Type*} [Fintype V] [Fintype W] [Fintype α] [Fintype β]

open Classical in
theorem zarankiewicz_of_fintypeCard_eq
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) :
    zarankiewicz m n s t =
      sup { G : SimpleGraph (V ⊕ W) | G ≤ completeBipartiteGraph V W
        ∧ (completeBipartiteGraph α β).Free G} (#·.edgeFinset) := by
  let e₁ := completeBipartiteGraph.overFinIso hm hn
  let K := completeBipartiteGraph (Fin s) (Fin t)
  let e₂ := completeBipartiteGraph.overFinIso hs ht
  rw [zarankiewicz, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    let e₁ := e₁.symm
    let K := completeBipartiteGraph α β
    let e₂ := e₂.symm
  all_goals
    simp_rw [Finset.sup_le_iff, mem_filter, mem_univ, true_and]
    intro G ⟨h_le, h_free⟩
    simp_rw [Iso.card_edgeFinset_eq (.map e₁.toEquiv G)]
    replace h' : G.map e₁.toEquiv.toEmbedding ∈ univ.filter fun G ↦
        G ≤ completeBipartiteGraph _ _ ∧ K.Free G := by
      rw [mem_filter, map_le_iff_le_comap, ← free_congr e₂ (.map e₁.toEquiv G)]
      refine ⟨mem_univ _, fun _ _ hadj ↦ ?_, h_free⟩
      simpa only [← Embedding.map_adj_iff e₁.toEmbedding, ← comap_adj] using h_le hadj
    have h_le_sup := @le_sup _ _ _ _ _ (#·.edgeFinset) (G.map e₁.toEquiv.toEmbedding) h'
    simp_rw [← card_coe, mem_edgeFinset] at h_le_sup ⊢
    exact h_le_sup

/-- `zarankiewicz (card V) (card W) (card α) (card β)` is at most `x` if and only if every
`completeBipartiteGraph α β`-free bipartite graph `G` has at most `x` edges. -/
theorem zarankiewicz_le_iff (x : ℕ) :
    zarankiewicz (card V) (card W) (card α) (card β) ≤ x ↔
      ∀ ⦃G : SimpleGraph (V ⊕ W)⦄ [DecidableRel G.Adj], G ≤ completeBipartiteGraph V W →
        (completeBipartiteGraph α β).Free G → #G.edgeFinset ≤ x := by
  simp_rw [zarankiewicz_of_fintypeCard_eq rfl rfl rfl rfl,
    Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun h _ _ h_le h_free ↦ by convert h _ ⟨h_le, h_free⟩,
    fun h _ ⟨h_le, h_free⟩ ↦ by convert h h_le h_free⟩

/-- `zarankiewicz (card V) (card W) (card α) (card β)` is greater than `x` if and only if there
exists a `completeBipartiteGraph α β`-free bipartite graph `G` with more than `x` edges. -/
theorem lt_zarankiewicz_iff (x : ℕ) :
    x < zarankiewicz (card V) (card W) (card α) (card β) ↔
      ∃ G : SimpleGraph (V ⊕ W), ∃ _ : DecidableRel G.Adj, G ≤ completeBipartiteGraph V W ∧
        (completeBipartiteGraph α β).Free G ∧  x < #G.edgeFinset := by
  simp_rw [zarankiewicz_of_fintypeCard_eq rfl rfl rfl rfl,
    Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, ⟨h_le, h_free⟩, h_lt⟩ ↦ ⟨_, _, h_le, h_free, by convert h_lt⟩,
    fun ⟨_, _, ⟨h_le, h_free, h_lt⟩⟩ ↦ ⟨_, ⟨h_le, h_free⟩, by convert h_lt⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

@[inherit_doc zarankiewicz_le_iff]
theorem zarankiewicz_le_iff_of_nonneg {x : R} (h : 0 ≤ x) :
    zarankiewicz (card V) (card W) (card α) (card β) ≤ x ↔
      ∀ ⦃G : SimpleGraph (V ⊕ W)⦄ [DecidableRel G.Adj], G ≤ completeBipartiteGraph V W →
        (completeBipartiteGraph α β).Free G → #G.edgeFinset ≤ x := by
  simp_rw [← Nat.le_floor_iff h]
  exact zarankiewicz_le_iff ⌊x⌋₊

@[inherit_doc lt_zarankiewicz_iff]
theorem lt_zarankiewicz_iff_of_nonneg {x : R} (h : 0 ≤ x) :
    x < zarankiewicz (card V) (card W) (card α) (card β) ↔
      ∃ G : SimpleGraph (V ⊕ W), ∃ _ : DecidableRel G.Adj, G ≤ completeBipartiteGraph V W ∧
        (completeBipartiteGraph α β).Free G ∧  x < #G.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_zarankiewicz_iff ⌊x⌋₊

open Classical in
/-- The Zarankiewicz function is at most the corresponding extremal number. -/
theorem zarankiewicz_le_extremalNumber :
    zarankiewicz m n (card α) (card β) ≤ extremalNumber (m + n) (completeBipartiteGraph α β) := by
  conv =>
    enter [2, 1]
    rw [← Fintype.card_fin (m + n)]
  simp_rw [zarankiewicz, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  intro B ⟨_, h⟩
  rw [(Iso.map finSumFinEquiv B).card_edgeFinset_eq]
  exact card_edgeFinset_le_extremalNumber <|
    (h.congr_left <| completeBipartiteGraph.overFinIso rfl rfl).congr_right
      (Iso.map finSumFinEquiv B).symm

/-- The symmetric Zarankiewicz function is at least twice a corresponding extremal number. -/
theorem two_mul_extremalNumber_le_zarankiewicz_symm [Nonempty α] [Nonempty β] :
    2 * extremalNumber n (completeBipartiteGraph α β) ≤ zarankiewicz n n (card α) (card β) := by
  conv =>
    enter [1, 2, 1]
    rw [← Fintype.card_fin n]
  rify
  rw [← le_div_iff₀' (by positivity), extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ h
  rw [le_div_iff₀' (by positivity), ← Nat.cast_two, ← Nat.cast_mul, Nat.cast_le]
  apply Finset.le_sup_of_le (b := G.bipartiteDoubleCover)
  · simp_rw [mem_filter, mem_univ, true_and]
    refine ⟨bipartiteDoubleCover_le, ?_⟩
    contrapose! h
    exact bipartiteDoubleCover_completeBipartiteGraph_isContained <|
      h.trans' ⟨(completeBipartiteGraph.overFinIso rfl rfl).toCopy⟩
  · convert bipartiteDoubleCover_card_edgeFinset.symm.le

end SimpleGraph

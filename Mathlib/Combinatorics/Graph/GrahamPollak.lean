/-
Copyright (c) 2026 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman, Aaron Hill
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!

# The Graham-Pollak theorem

-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V} {α ι : Type*} {a : α} {f : V → ι}

lemma neighborFinset_eq_empty_of_notMem_union
     {S : Set V} [Fintype ↑S] [Fintype ↑Sᶜ] [DecidableEq V] [Fintype ↑(G.neighborSet v)]
  (hv : v ∉ S.toFinset ∪ Sᶜ.toFinset) : G.neighborFinset v = ∅ := by grind

variable (G) in
def IsCompleteMultipartiteWith (f : V → ι) : Prop :=
  G.Adj = Ne.onFun f

namespace IsCompleteMultipartiteWith

variable {C : G.IsCompleteMultipartiteWith f}
include C

@[simp]
lemma adj_iff_ne : G.Adj v u ↔ f v ≠ f u :=
  congrFun (congrFun C v) u |>.to_iff

lemma neighborSet_eq (v : V) : G.neighborSet v = {u | f v ≠ f u} :=
  Filter.principal_eq_iff_eq.mp (congrArg Filter.principal (congrFun C v))

section finite

variable [Fintype (G.neighborSet v)] [Fintype {u | f v ≠ f u}]

variable (v) in
lemma neighborFinset_eq :
    G.neighborFinset v = {u | f v ≠ f u}.toFinset := by
  simp_rw [neighborFinset_def, C.neighborSet_eq]

end finite

end IsCompleteMultipartiteWith

def IsCompleteBipartiteWith (left : Set V) : Prop :=
  G.IsCompleteMultipartiteWith (· ∈ left)

namespace IsCompleteBipartiteWith

variable {left : Set V} (C : G.IsCompleteBipartiteWith left)
include C

lemma isCompleteMultipartiteWith : G.IsCompleteMultipartiteWith (· ∈ left) := C

@[simp]
lemma adj_iff_not_mem (hv : v ∈ left) : G.Adj v u ↔ u ∉ left := by
  simp [C.isCompleteMultipartiteWith.adj_iff_ne, hv]

@[simp]
lemma adj_iff_mem (hv : v ∉ left) : G.Adj v u ↔ u ∈ left := by
  simp [C.isCompleteMultipartiteWith.adj_iff_ne, hv]

@[simp]
lemma neighborSet_eq_of_mem_left (hv : v ∈ left) : G.neighborSet v = leftᶜ := by
  grind [C.isCompleteMultipartiteWith.neighborSet_eq v, Set.compl_def]

@[simp]
lemma neighborSet_eq_of_not_mem_left (hv : v ∉ left) : G.neighborSet v = left := by
  ext u
  simp [C.isCompleteMultipartiteWith.neighborSet_eq, hv]

lemma bipartite : G.IsBipartiteWith left leftᶜ := by
  refine ⟨disjoint_compl_right, fun v u hadj ↦ ?_⟩
  have h : (v ∈ left) ≠ (u ∈ left) := C.isCompleteMultipartiteWith.adj_iff_ne.mp hadj
  by_cases hv : v ∈ left
  · exact Or.inl ⟨hv, by simpa [hv] using h⟩
  · exact Or.inr ⟨(Set.mem_compl_iff left v).mpr hv, (adj_iff_mem C hv).mp hadj⟩

section finite

variable [Fintype ↑left] [Fintype ↑(G.neighborSet v)]

@[simp]
lemma neighborFinset_eq_of_mem_left [Fintype ↑leftᶜ] (hv : v ∈ left.toFinset) :
    G.neighborFinset v = leftᶜ.toFinset := by
  grind only [neighborFinset_def, Set.mem_toFinset, neighborSet_eq_of_mem_left, Set.toFinset_congr]

@[simp]
lemma neighborFinset_eq_of_not_mem_left (hv : v ∉ left.toFinset) :
    G.neighborFinset v = left.toFinset := by
  grind only [neighborFinset_def, neighborSet_eq_of_not_mem_left,
              Set.mem_toFinset, Set.toFinset_congr]

end finite

end IsCompleteBipartiteWith

variable (G) in
def IsCompleteBipartite :=
  ∃ left, G.IsCompleteBipartiteWith left

open Set
section finite

variable [Fintype V] [Fintype α] {𝓁 : TopEdgeLabeling V α}

open Finset

/--
If `c` sums to 0 over `V` and over the left side of each complete bipartite subgraph
in a partition of `K_n`, then `∑ c_v^2 = 0`.
-/
private lemma aux
  (completeBipartiteOf : ∀ a, IsCompleteBipartite <| 𝓁.labelGraph a)
  [∀ a, Fintype (completeBipartiteOf a).choose]
  (c : V → ℝ)
  (h_sum : ∑ v, c v = 0)
  (h_left : ∀ a, ∑ v ∈ (completeBipartiteOf a).choose, c v = 0) :
    ∑ v, c v ^ 2 = 0 := by
  rcases subsingleton_or_nontrivial V
  · simp_rw [sq, sum_mul_self_eq_zero_iff]
    grind [Fintype.sum_subsingleton c]
  · classical
    have h_disjoint (u : V) :
        ((univ : Finset α) : Set α).PairwiseDisjoint (𝓁.labelGraph · |>.neighborFinset u) := by
      intro
      grind [Finset.disjoint_left, mem_neighborFinset, 𝓁.labelGraph_adj]
    have h_partition (u : V) :
        univ.erase u = (univ : Finset α).biUnion (𝓁.labelGraph · |>.neighborFinset u) := by
      ext v
      simp only [mem_erase, Finset.mem_univ, Finset.mem_biUnion, mem_neighborFinset]
      constructor
      · exact fun _ ↦ ⟨𝓁 ⟨s(u, v), by tauto⟩, by tauto⟩
      · grind only [TopEdgeLabeling.labelGraph_adj]
    have : ∑ v, c v ^ 2 = -∑ u, ∑ v ∈ univ.erase u, c u * c v := by simp [← mul_sum, sq, h_sum]
    rw [this,
        neg_eq_zero,
        sum_congr rfl fun u _ ↦ by rw [h_partition, sum_biUnion <| h_disjoint _],
        sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    let cbp := completeBipartiteOf a
    let sum_eq (S : Finset V) := ∑ x ∈ S, ∑ i ∈ 𝓁.labelGraph a |>.neighborFinset x, c x * c i = 0
    have h_L_sum : sum_eq cbp.choose.toFinset := by
      dsimp [sum_eq]
      rw [sum_congr rfl fun v hv ↦ by
        rw [cbp.choose_spec.neighborFinset_eq_of_mem_left hv, ← mul_sum],
          ← sum_mul, h_left a, zero_mul]
    have h_R_sum : sum_eq cbp.chooseᶜ.toFinset := by
      dsimp [sum_eq]
      rw [sum_congr rfl fun _ hx ↦ by
        rw [cbp.choose_spec.neighborFinset_eq_of_not_mem_left (by grind), ← mul_sum],
          h_left]
      simp only [mul_zero, sum_const_zero]
    rw [← sum_subset (subset_univ (cbp.choose.toFinset ∪ cbp.chooseᶜ.toFinset)) <|
      fun _ _ hu ↦ by
        rw [neighborFinset_eq_empty_of_notMem_union hu, sum_empty],
      sum_union <| Finset.disjoint_left.mpr fun v hvL hvR ↦
        Set.disjoint_left.mp cbp.choose_spec.bipartite.disjoint
          (Set.mem_toFinset.mp hvL) (Set.mem_toFinset.mp hvR),
      h_L_sum,
      h_R_sum,
      add_zero]

open Fintype LinearMap in
open scoped Matrix in
/--
The Graham-Pollak theorem:

In a complete graph on `|V|` vertices, any edge labeling into complete bipartite subgraphs uses
at least `|V| - 1` distinct labels.
-/
theorem card_le_card_labels_add_one_of_CompleteBipartite
  (completeBipartiteOf : ∀ a, IsCompleteBipartite <| 𝓁.labelGraph a) :
    card V ≤ card α + 1 := by
  classical
  by_contra! h
  let M : Matrix (Fin 1 ⊕ α) V ℝ := Matrix.fromRows
    (Matrix.replicateCol V ![1])
    (Matrix.of fun m n ↦ (completeBipartiteOf m).choose.indicator 1 n)
  obtain ⟨c, hc, hc_nezero⟩ : ∃ x ∈ ker M.toLin', x ≠ 0 := (ker _).ne_bot_iff.mp <| by
    apply ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, card_sum, card_unique]
    grind
  have (a : α) : ∑ v ∈ (completeBipartiteOf a).choose, c v = 0 := by
    suffices ∑ x, ((completeBipartiteOf a).choose.toFinset : Set _).indicator c x = 0 by
      rwa [sum_indicator_subset _ (by simp)] at this
    have : (M *ᵥ c) (.inr a) = 0 := by simp_all
    simp only [M, Matrix.mulVec, dotProduct, Set.indicator_apply] at this
    aesop
  have := aux completeBipartiteOf c
  simp_all [Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg, funext_iff, Matrix.mulVec, dotProduct]
  aesop

end finite

end SimpleGraph

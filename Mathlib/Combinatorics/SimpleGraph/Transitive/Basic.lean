/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Transitivity properties of graphs

## Main definitions

* `SimpleGraph.IsVertexTransitive`: a graph is vertex-transitive if every two vertices are related
  by an automorphism.
* `SimpleGraph.IsEdgeTransitive`: a graph is edge-transitive if every two edges are related by
  an automorphism.
* `SimpleGraph.IsSymmetric`: a graph is symmetric if every two darts are related by an automorphism.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph is vertex-transitive if every two vertices are related by an automorphism. -/
def IsVertexTransitive (G : SimpleGraph V) : Prop :=
  ∀ v w, ∃ f : G ≃g G, f v = w

/-- A graph is edge-transitive if every two edges are related by an automorphism. -/
def IsEdgeTransitive (G : SimpleGraph V) : Prop :=
  ∀ ⦃e₁ e₂⦄, e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet → ∃ f : G ≃g G, e₁.map f = e₂

/-- A graph is symmetric (aka arc-transitive or flag-transitive) if every two darts are related
by an automorphism. -/
def IsSymmetric (G : SimpleGraph V) : Prop :=
  ∀ d₁ d₂ : G.Dart, ∃ f : G ≃g G, f d₁.fst = d₂.fst ∧ f d₁.snd = d₂.snd

lemma IsVertexTransitive.iso (vt : G.IsVertexTransitive) (f : G ≃g H) : H.IsVertexTransitive := by
  intro v w
  obtain ⟨g, hg⟩ := vt (f.symm v) (f.symm w)
  exact ⟨(f.symm.trans g).trans f, by simp_all⟩

lemma IsEdgeTransitive.iso (et : G.IsEdgeTransitive) (f : G ≃g H) : H.IsEdgeTransitive := by
  intro e₁ e₂ me₁ me₂
  rw [← f.symm.map_mem_edgeSet_iff] at me₁ me₂
  obtain ⟨g, hg⟩ := et me₁ me₂
  apply_fun Sym2.map f at hg
  exact ⟨(f.symm.trans g).trans f, by simp_all [Sym2.map_map]⟩

lemma IsSymmetric.iso (sym : G.IsSymmetric) (f : G ≃g H) : H.IsSymmetric := fun d₁ d₂ ↦ by
  obtain ⟨g, hg⟩ :=
    sym ⟨(_, _), f.symm.map_adj_iff.mpr d₁.adj⟩ ⟨(_, _), f.symm.map_adj_iff.mpr d₂.adj⟩
  exact ⟨(f.symm.trans g).trans f, ⟨by simp [congr(f $(hg.1))], by simp [congr(f $(hg.2))]⟩⟩

lemma IsVertexTransitive.isRegularOfDegree [G.LocallyFinite] (vt : G.IsVertexTransitive) (v : V) :
    G.IsRegularOfDegree (G.degree v) := fun w ↦ by
  obtain ⟨f, hf⟩ := vt v w
  exact hf ▸ f.degree_eq v

lemma IsSymmetric.isVertexTransitive (sym : G.IsSymmetric) (ni : ∀ v, ¬G.IsIsolated v) :
    G.IsVertexTransitive := fun v w ↦ by
  obtain ⟨v', av⟩ := exists_adj_iff_not_isIsolated.mpr (ni v)
  obtain ⟨w', aw⟩ := exists_adj_iff_not_isIsolated.mpr (ni w)
  grind [sym ⟨(v, v'), av⟩ ⟨(w, w'), aw⟩]

lemma IsSymmetric.isEdgeTransitive (sym : G.IsSymmetric) : G.IsEdgeTransitive := by
  intro e₁ e₂ me₁ me₂
  cases e₁, e₂ using Sym2.inductionOn₂
  obtain ⟨f, _, _⟩ := sym ⟨_, me₁⟩ ⟨_, me₂⟩
  exact ⟨f, by simp_all⟩

variable (V) in
lemma isSymmetric_bot : (⊥ : SimpleGraph V).IsSymmetric := fun d₁ d₂ ↦ by simpa using d₁.adj

variable (V) in
lemma isVertexTransitive_bot : (⊥ : SimpleGraph V).IsVertexTransitive := fun v w ↦ by
  classical exact ⟨⟨Equiv.swap v w, by simp⟩, by simp⟩

variable (V) in
lemma isEdgeTransitive_bot : (⊥ : SimpleGraph V).IsEdgeTransitive :=
  (isSymmetric_bot V).isEdgeTransitive

variable (V) in
lemma isSymmetric_top : (⊤ : SimpleGraph V).IsSymmetric := fun d₁ d₂ ↦ by
  classical
  by_cases h₁ : d₁.fst ≠ d₂.snd
  · exact ⟨⟨(Equiv.swap d₁.snd d₂.snd).trans (Equiv.swap d₁.fst d₂.fst), by simp⟩, by
      simp only [RelIso.coe_fn_mk]; grind [d₁.adj.ne, d₂.adj.ne]⟩
  by_cases h₂ : d₁.snd ≠ d₂.fst
  · exact ⟨⟨(Equiv.swap d₁.fst d₂.fst).trans (Equiv.swap d₁.snd d₂.snd), by simp⟩, by
      simp only [RelIso.coe_fn_mk]; grind [d₁.adj.ne, d₂.adj.ne]⟩
  exact ⟨⟨Equiv.swap d₁.fst d₂.fst, by simp⟩, by simp_all⟩

variable (V) in
lemma isVertexTransitive_top : (⊤ : SimpleGraph V).IsVertexTransitive := fun v w ↦ by
  classical exact ⟨⟨Equiv.swap v w, by simp⟩, by simp⟩

variable (V) in
lemma isEdgeTransitive_top : (⊤ : SimpleGraph V).IsEdgeTransitive :=
  (isSymmetric_top V).isEdgeTransitive

lemma isBipartiteWith_of_edge_not_vertex_transitive (et : G.IsEdgeTransitive)
    (nvt : ¬G.IsVertexTransitive) (ni : ∀ v, ¬G.IsIsolated v) {v w : V} (ha : G.Adj v w) :
    G.IsBipartiteWith (.range fun f : G ≃g G ↦ f v) (.range fun f : G ≃g G ↦ f w) := by
  set Ov : Set V := .range fun f : G ≃g G ↦ f v
  set Ow : Set V := .range fun f : G ≃g G ↦ f w
  have span (x y) (hxy : G.Adj x y) : x ∈ Ov ∧ y ∈ Ow ∨ x ∈ Ow ∧ y ∈ Ov := by
    rw [← mem_edgeSet] at ha hxy
    obtain ⟨f, hf⟩ := et ha hxy
    rw [Sym2.map_mk, Sym2.eq_iff] at hf
    grind
  refine ⟨?_, span⟩
  contrapose nvt
  rw [Set.not_disjoint_iff] at nvt
  obtain ⟨x, ⟨fv, hv⟩, ⟨fw, hw⟩⟩ := nvt
  replace span (x) : x ∈ Ov ∨ x ∈ Ow := by
    obtain ⟨y, hxy⟩ := exists_adj_iff_not_isIsolated.mpr (ni x)
    exact (span _ _ hxy).imp (·.1) (·.1)
  intro a b
  obtain ⟨fa, ha⟩ | ⟨fa, ha⟩ := span a <;> obtain ⟨fb, hb⟩ | ⟨fb, hb⟩ := span b
  · exact ⟨fa.symm.trans fb, by simp_all [← RelIso.eq_symm_apply]⟩
  · exact ⟨((fa.symm.trans fv).trans fw.symm).trans fb, by simp_all [← RelIso.eq_symm_apply]⟩
  · exact ⟨((fa.symm.trans fw).trans fv.symm).trans fb, by simp_all [← RelIso.eq_symm_apply]⟩
  · exact ⟨fa.symm.trans fb, by simp_all [← RelIso.eq_symm_apply]⟩

/-- A semi-symmetric (edge- but not vertex-transitive) graph with no isolated vertices
is bipartite. -/
theorem isBipartite_of_edge_not_vertex_transitive
    (et : G.IsEdgeTransitive) (nvt : ¬G.IsVertexTransitive) (ni : ∀ v, ¬G.IsIsolated v) :
    G.IsBipartite := by
  obtain _ | ⟨⟨e, me⟩⟩ := G.edgeSet.eq_empty_or_nonempty
  · simp_all [IsBipartite.bot]
  · cases e using Sym2.inductionOn
    exact (isBipartiteWith_of_edge_not_vertex_transitive et nvt ni me).isBipartite

open Finset in
/-- A half-transitive (vertex- and edge-transitive but not symmetric) graph with an odd-degree
vertex is symmetric. The finiteness condition is necessary; see [thomassenwatkins1989]. -/
theorem isSymmetric_of_transitive_of_odd_degree [Fintype V] [DecidableRel G.Adj]
    (vt : G.IsVertexTransitive) (et : G.IsEdgeTransitive) {v : V} (dv : Odd (G.degree v)) :
    G.IsSymmetric := by
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp dv.pos
  contrapose dv
  let R (a b) := ∃ f : G ≃g G, f v = a ∧ f w = b
  have invariant (f : G ≃g G) (a b) : R (f a) (f b) ↔ R a b := by
    refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
    · exact ⟨g.trans f.symm, by simpa using congr(f.symm $(hg.1)),
        by simpa using congr(f.symm $(hg.2))⟩
    · exact ⟨g.trans f, by simp [hg.1], by simp [hg.2]⟩
  have oriented {a b} (hab : G.Adj a b) : R a b ∨ R b a := by
    obtain ⟨f, hf⟩ := et (G.mem_edgeSet.mpr hvw) (G.mem_edgeSet.mpr hab)
    rw [Sym2.map_mk, Sym2.eq_iff] at hf
    grind
  have exclusive {a b} : ¬(R a b ∧ R b a) := by
    rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    let k := f.trans g.symm
    have kv : k v = w := by simp [k, hf.1, ← hg.2]
    have kw : k w = v := by simp [k, hf.2, ← hg.1]
    refine dv fun d₁ d₂ ↦ ?_
    obtain ⟨f₁, f₁v, f₁w⟩ | ⟨f₁, f₁v, f₁w⟩ := oriented d₁.adj <;>
    obtain ⟨f₂, f₂v, f₂w⟩ | ⟨f₂, f₂v, f₂w⟩ := oriented d₂.adj
    · exact ⟨f₁.symm.trans f₂, by simp [← f₁v, ← f₁w, f₂v, f₂w]⟩
    · exact ⟨(f₁.symm.trans k).trans f₂, by simp [← f₁v, ← f₁w, f₂v, f₂w, kv, kw]⟩
    · exact ⟨(f₁.symm.trans k).trans f₂, by simp [← f₁v, ← f₁w, f₂v, f₂w, kv, kw]⟩
    · exact ⟨f₁.symm.trans f₂, by simp [← f₁v, ← f₁w, f₂v, f₂w]⟩
  classical
  let out (a) : Finset V := {x | R a x}
  let inn (a) : Finset V := {x | R x a}
  have out_eq (a) : #(out a) = #(out v) := by
    obtain ⟨f, hf⟩ := vt a v
    exact card_bijective f f.bijective (by simp [out, ← hf, invariant])
  have in_eq (a) : #(inn a) = #(inn v) := by
    obtain ⟨f, hf⟩ := vt a v
    exact card_bijective f f.bijective (by simp [inn, ← hf, invariant])
  have total : ∑ a, #(out a) = ∑ a, #(inn a) := by
    simp only [out, inn, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have balance : #(out v) = #(inn v) := by
    have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    apply Nat.eq_of_mul_eq_mul_left hp
    simpa [out_eq, in_eq] using total
  have adjacent {a b} (h : R a b) : G.Adj a b := by
    obtain ⟨f, rfl, rfl⟩ := h
    rwa [← f.map_rel_iff] at hvw
  have partition : out v ∪ inn v = G.neighborFinset v := by
    ext x
    simp only [out, inn, mem_union, mem_filter_univ, mem_neighborFinset]
    exact ⟨fun h ↦ h.elim adjacent fun h ↦ (adjacent h).symm, oriented⟩
  have disjoint : Disjoint (out v) (inn v) :=
    Finset.disjoint_left.mpr fun b hb hb' ↦ exclusive ⟨(mem_filter.mp hb).2, (mem_filter.mp hb').2⟩
  have even_degree : Even (G.degree v) := by
    refine ⟨#(out v), ?_⟩
    rw [← card_neighborFinset_eq_degree, ← partition, card_union_of_disjoint disjoint, balance]
  rwa [Nat.not_odd_iff_even]

end SimpleGraph

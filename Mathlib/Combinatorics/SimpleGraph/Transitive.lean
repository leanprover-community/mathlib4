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
@[expose, wikidata Q220997]
def IsVertexTransitive (G : SimpleGraph V) : Prop :=
  ∀ v w, ∃ f : G ≃g G, f v = w

/-- A graph is edge-transitive if every two edges are related by an automorphism. -/
@[expose, wikidata Q4391289]
def IsEdgeTransitive (G : SimpleGraph V) : Prop :=
  ∀ ⦃e₁ e₂⦄, e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet → ∃ f : G ≃g G, e₁.map f = e₂

/-- A graph is symmetric (aka arc-transitive or flag-transitive) if every two darts are related
by an automorphism. -/
@[expose, wikidata Q1205074]
def IsSymmetric (G : SimpleGraph V) : Prop :=
  ∀ d₁ d₂, ∃ f : G ≃g G, f.toHom.mapDart d₁ = d₂

protected lemma IsVertexTransitive.congr (vt : G.IsVertexTransitive) (f : G ≃g H) :
    H.IsVertexTransitive := fun v w ↦ by
  obtain ⟨g, hg⟩ := vt (f.symm v) (f.symm w)
  exact ⟨(f.symm.trans g).trans f, by simp_all⟩

protected lemma IsEdgeTransitive.congr (et : G.IsEdgeTransitive) (f : G ≃g H) :
    H.IsEdgeTransitive := fun e₁ e₂ me₁ me₂ ↦ by
  rw [← f.symm.map_mem_edgeSet_iff] at me₁ me₂
  obtain ⟨g, hg⟩ := et me₁ me₂
  apply_fun Sym2.map f at hg
  exact ⟨(f.symm.trans g).trans f, by simp_all [Sym2.map_map]⟩

protected lemma IsSymmetric.congr (sym : G.IsSymmetric) (f : G ≃g H) :
    H.IsSymmetric := fun d₁ d₂ ↦ by
  obtain ⟨g, hg⟩ :=
    sym ⟨(_, _), f.symm.map_adj_iff.mpr d₁.adj⟩ ⟨(_, _), f.symm.map_adj_iff.mpr d₂.adj⟩
  exact ⟨(f.symm.trans g).trans f, by rw [Hom.mapDart_eq_iff]; simp_all⟩

lemma IsVertexTransitive.isRegularOfDegree [G.LocallyFinite] (vt : G.IsVertexTransitive) (v : V) :
    G.IsRegularOfDegree (G.degree v) := fun w ↦ by
  obtain ⟨f, hf⟩ := vt v w
  exact hf ▸ f.degree_eq v

lemma IsSymmetric.isVertexTransitive (sym : G.IsSymmetric) (ni : ∀ v, ¬G.IsIsolated v) :
    G.IsVertexTransitive := fun v w ↦ by
  obtain ⟨v', av⟩ := exists_adj_iff_not_isIsolated.mpr (ni v)
  obtain ⟨w', aw⟩ := exists_adj_iff_not_isIsolated.mpr (ni w)
  obtain ⟨f, hf⟩ := sym ⟨(v, v'), av⟩ ⟨(w, w'), aw⟩
  rw [Hom.mapDart_eq_iff] at hf
  exact ⟨f, hf.1⟩

lemma IsSymmetric.isEdgeTransitive (sym : G.IsSymmetric) : G.IsEdgeTransitive := by
  rintro ⟨_, _⟩ ⟨_, _⟩ me₁ me₂
  obtain ⟨f, _, _⟩ := sym ⟨_, me₁⟩ ⟨_, me₂⟩
  exact ⟨f, by simp⟩

variable (V) in
protected lemma IsSymmetric.bot : (⊥ : SimpleGraph V).IsSymmetric := fun d₁ d₂ ↦ by
  simpa using d₁.adj

variable (V) in
protected lemma IsVertexTransitive.bot : (⊥ : SimpleGraph V).IsVertexTransitive := fun v w ↦ by
  classical exact ⟨⟨Equiv.swap v w, by simp⟩, by simp⟩

variable (V) in
protected lemma IsEdgeTransitive.bot : (⊥ : SimpleGraph V).IsEdgeTransitive :=
  (IsSymmetric.bot V).isEdgeTransitive

variable (V) in
protected lemma IsSymmetric.top : (⊤ : SimpleGraph V).IsSymmetric := fun d₁ d₂ ↦ by
  classical
  by_cases h₁ : d₁.fst ≠ d₂.snd
  · exact ⟨⟨(Equiv.swap d₁.snd d₂.snd).trans (Equiv.swap d₁.fst d₂.fst), by simp⟩, by
      rw [Hom.mapDart_eq_iff, RelHom.coeFn_mk]; grind [d₁.adj.ne, d₂.adj.ne]⟩
  by_cases h₂ : d₁.snd ≠ d₂.fst
  · exact ⟨⟨(Equiv.swap d₁.fst d₂.fst).trans (Equiv.swap d₁.snd d₂.snd), by simp⟩, by
      rw [Hom.mapDart_eq_iff, RelHom.coeFn_mk]; grind [d₁.adj.ne, d₂.adj.ne]⟩
  exact ⟨⟨Equiv.swap d₁.fst d₂.fst, by simp⟩, by rw [Hom.mapDart_eq_iff]; simp_all⟩

variable (V) in
protected lemma IsVertexTransitive.top : (⊤ : SimpleGraph V).IsVertexTransitive := fun v w ↦ by
  classical exact ⟨⟨Equiv.swap v w, by simp⟩, by simp⟩

variable (V) in
protected lemma IsEdgeTransitive.top : (⊤ : SimpleGraph V).IsEdgeTransitive :=
  (IsSymmetric.top V).isEdgeTransitive

lemma IsEdgeTransitive.isBipartiteWith_of_not_isVertexTransitive (et : G.IsEdgeTransitive)
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

/-- An edge- but not vertex-transitive graph with no isolated vertices is bipartite. -/
theorem IsEdgeTransitive.isBipartite_of_not_isVertexTransitive
    (et : G.IsEdgeTransitive) (nvt : ¬G.IsVertexTransitive) (ni : ∀ v, ¬G.IsIsolated v) :
    G.IsBipartite := by
  obtain _ | ⟨⟨e, me⟩⟩ := G.edgeSet.eq_empty_or_nonempty
  · simp_all [IsBipartite.bot]
  · cases e using Sym2.inductionOn
    exact (et.isBipartiteWith_of_not_isVertexTransitive nvt ni me).isBipartite

open Finset in
/-- A finite vertex- and edge-transitive graph with an odd-degree vertex is symmetric.
See [thomassenwatkins1989], p. 260 for an _infinite_ counterexample. -/
theorem IsEdgeTransitive.isSymmetric_of_exists_odd_degree [Finite V] (vt : G.IsVertexTransitive)
    (et : G.IsEdgeTransitive) (dv : ∃ (v : V) (_ : Fintype (G.neighborSet v)), Odd (G.degree v)) :
    G.IsSymmetric := by
  obtain ⟨v, _, dv⟩ := dv
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp dv.pos
  contrapose dv with nsym
  -- If `G` is not symmetric, the orbit of the dart `v → w` under `G`'s automorphism group
  -- is an orientation of `G`.
  let R (a b) := ∃ f : G ≃g G, f v = a ∧ f w = b
  have R_adj {a b} (h : R a b) : G.Adj a b := by
    obtain ⟨f, rfl, rfl⟩ := h
    rwa [f.map_rel_iff]
  have R_trans {a b} (f : G ≃g G) : R (f a) (f b) ↔ R a b :=
    ⟨ fun ⟨g, hg⟩ ↦ ⟨g.trans f.symm, by simp [hg.1], by simp [hg.2]⟩,
      fun ⟨g, hg⟩ ↦ ⟨g.trans f, by simp [hg.1], by simp [hg.2]⟩⟩
  have R_or {a b} (hab : G.Adj a b) : R a b ∨ R b a := by
    obtain ⟨f, hf⟩ := et (G.mem_edgeSet.mpr hvw) (G.mem_edgeSet.mpr hab)
    rw [Sym2.map_mk, Sym2.eq_iff] at hf
    grind
  have R_nand {a b} : ¬(R a b ∧ R b a) := by
    rintro ⟨⟨f, fv, fw⟩, ⟨g, gv, gw⟩⟩
    refine nsym fun d₁ d₂ ↦ ?_
    obtain ⟨f₁, f₁v, f₁w⟩ | ⟨f₁, f₁v, f₁w⟩ := R_or d₁.adj <;>
    obtain ⟨f₂, f₂v, f₂w⟩ | ⟨f₂, f₂v, f₂w⟩ := R_or d₂.adj
    case inl.inl | inr.inr => exact ⟨f₁.symm.trans f₂, by
      rw [Hom.mapDart_eq_iff]; simp [← f₁v, ← f₁w, f₂v, f₂w]⟩
    all_goals exact ⟨(f₁.symm.trans f).trans (g.symm.trans f₂), by
      rw [Hom.mapDart_eq_iff]; simp [fv, fw, ← gv, ← gw, ← f₁v, ← f₁w, f₂v, f₂w]⟩
  classical
  have _ := Fintype.ofFinite V
  -- By vertex-transitivity and the handshaking lemma, `v`'s indegree and outdegree are equal
  -- in the orientation, so it has even degree in `G`. Contradiction.
  let O (a) : Finset V := {x | R a x}
  let I (a) : Finset V := {x | R x a}
  have O_const (a) : #(O a) = #(O v) := by
    obtain ⟨f, hf⟩ := vt a v
    exact card_bijective _ f.bijective (by simp [O, ← hf, R_trans])
  have I_const (a) : #(I a) = #(I v) := by
    obtain ⟨f, hf⟩ := vt a v
    exact card_bijective _ f.bijective (by simp [I, ← hf, R_trans])
  have dv : G.degree v = #(O v) + #(I v) := by
    rw [← card_union_of_disjoint <| Finset.disjoint_left.mpr fun a Oa Ia ↦
      R_nand ⟨(mem_filter.mp Oa).2, (mem_filter.mp Ia).2⟩, ← card_neighborFinset_eq_degree]
    congr; ext
    simp only [mem_union, mem_filter_univ, mem_neighborFinset]
    exact ⟨R_or, fun h ↦ h.elim R_adj (.symm ∘ R_adj)⟩
  have key : ∑ a, #(I a) = ∑ a, #(O a) := by
    simp only [O, I, card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [Nat.not_odd_iff_even]
  exact ⟨#(O v), by simp_all [@Fintype.card_ne_zero _ _ ⟨v⟩]⟩

end SimpleGraph

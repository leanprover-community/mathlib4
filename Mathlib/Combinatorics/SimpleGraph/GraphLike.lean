/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Simple graphs as graph-like structures

This file defines an incidence presentation of a `SimpleGraph` and proves its graph-like
properties.
-/

public section

variable {V : Type*} {G : SimpleGraph V}

open HypergraphPresentation

namespace SimpleGraph

/-- The presentation of a simple graph whose edges are unordered vertex pairs and whose
incidences are ordered vertex pairs. -/
@[expose, simps verts edges isIncident isLink adj]
def sym2Presentation (G : SimpleGraph V) : HypergraphPresentation V (V × V) (Sym2 V) G where
  verts := Set.univ
  edges := G.edgeSet
  IsIncident i e v := G.Adj i.1 i.2 ∧ s(i.1, i.2) = e ∧ i.1 = v
  IsSource i := G.Adj i.1 i.2
  IsTarget i := G.Adj i.1 i.2
  vert_mem_of_isIncident {_ _ v} _ := Set.mem_univ v
  edge_mem_of_isIncident {_ _ _} hi := hi.2.1 ▸ hi.1
  eq_and_eq_of_isIncident_of_isIncident {_ _ _ _ _} hi hf := by grind
  isIncident_iff {i} := by
    rw [or_self]
    exact ⟨fun h ↦ by grind, fun h ↦ ⟨s(i.1, i.2), i.1, h, rfl, rfl⟩⟩
  Adj := G.Adj
  adj_def {u v} := ⟨fun huv ↦ ⟨s(u, v), (u, v), (v, u), by simp [huv.ne], by simp [huv],
    by simp [huv.symm], by simp [huv, huv.symm]⟩, by grind⟩

attribute [grind =] verts_sym2Presentation edges_sym2Presentation isLink_sym2Presentation
  adj_sym2Presentation

instance : GraphLike G.sym2Presentation where
  order_eq_two {e} := Sym2.inductionOn e fun u v he => by
    rw [order]
    have hne : (u, v) ≠ (v, u) := by simp [he.ne]
    have h : (edgeFun G.sym2Presentation).preimage {s(u, v)} = {(u, v), (v, u)} := by
      ext i
      simp only [PFun.mem_preimage, Set.mem_singleton_iff, mem_edgeFun_iff_exists_isIncident,
        isIncident_sym2Presentation, exists_and_left, ↓existsAndEq, and_true, exists_eq_left,
        Sym2.eq, Prod.mk.eta, Sym2.rel_iff', Prod.swap_prod_mk, Set.mem_insert_iff,
        and_iff_right_iff_imp]
      rintro (rfl | rfl) <;> simpa [adj_comm]
    rw [h]
    exact Set.encard_pair hne
  exists_isSource_of_mem_edgeSet {e} he := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_edgeFun_iff_exists_isIncident, isIncident_sym2Presentation, exists_and_left,
        ↓existsAndEq, and_true, Prod.exists]
      use x, y, ⟨he, rfl⟩, he
  exists_isTarget_of_mem_edgeSet {e} he := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_edgeFun_iff_exists_isIncident, isIncident_sym2Presentation, exists_and_left,
        ↓existsAndEq, and_true, Prod.exists]
      use x, y, ⟨he, rfl⟩, he

instance : Undirected G.sym2Presentation where
  isSource_iff _ := Iff.rfl

instance : NoParallelEdge G.sym2Presentation where
  edge_eq_of_isLink h h' := by grind

lemma edgeFun_eq {i : V × V} (hi : G.Adj i.1 i.2) :
    edgeFun G.sym2Presentation i = Part.some (s(i.1, i.2)) := by
  ext e
  rw [mem_edgeFun_iff_exists_isIncident]
  simp [hi, eq_comm]

lemma endPoint_eq {i : V × V} (hi : G.Adj i.1 i.2) :
    endPoint G.sym2Presentation i = Part.some i.1 := by
  ext v
  rw [mem_endPoint_iff_exists_isIncident]
  simp [hi, eq_comm]

instance : Loopless G.sym2Presentation where
  no_loops_of_mem_mem {i j} hi hj hij hne := by
    simp only [G.sym2Presentation.incs_def, isIncident_sym2Presentation, exists_and_left,
      ↓existsAndEq, and_true, Set.mem_ofPred_eq] at hi hj
    simp only [edgeFun_eq hi, edgeFun_eq hj, Part.some_inj, Sym2.eq, Prod.mk.eta,
      Sym2.rel_iff'] at hij
    simp only [endPoint_eq hi, endPoint_eq hj, ne_eq, Part.some_inj]
    obtain rfl | rfl := hij
    · simp at hne
    simp [hj.ne']

end SimpleGraph

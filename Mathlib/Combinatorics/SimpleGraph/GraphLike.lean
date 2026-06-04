/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# SimpleGraphs as GraphLike

This file makes `SimpleGraph` an instance of `GraphLike`. Every adjacent pair is a dart and every
adjacent pair is an edge.
-/

public section

variable {V : Type*} {G : SimpleGraph V}

open HyperGraphLike

namespace SimpleGraph

@[simps (attr := grind =)]
instance : HyperGraphLike V (V × V) (Sym2 V) (SimpleGraph V) where
  verts _ := Set.univ
  edges G := G.edgeSet
  IsIncident G i e v := G.Adj i.1 i.2 ∧ s(i.1, i.2) = e ∧ i.1 = v
  IsSource G i := G.Adj i.1 i.2
  IsTarget G i := G.Adj i.1 i.2
  vert_mem_of_isIncident _ _ _ _ _ := Set.mem_univ _
  edge_mem_of_isIncident G i e v hi := hi.2.1 ▸ hi.1
  eq_and_eq_of_isIncident_of_isIncident G i e f u v hi hf := by grind
  isIncident_iff G i := by
    rw [or_self]
    exact ⟨fun h ↦ by grind, fun h ↦ ⟨s(i.1, i.2), i.1, h, rfl, rfl⟩⟩
  Adj G := G.Adj
  adj_def G u v := ⟨fun huv ↦ ⟨s(u, v), (u, v), (v, u), by simp [huv.ne], by simp [huv],
    by simp [huv.symm], by simp [huv, huv.symm]⟩, by grind⟩

instance : GraphLike V (V × V) (Sym2 V) (SimpleGraph V) where
  order_eq_two G e := Sym2.inductionOn e fun u v he => by
    rw [order]
    have hne : (u, v) ≠ (v, u) := by simp [he.ne]
    have h : (edgeFun G).preimage {s(u, v)} = {(u, v), (v, u)} := by
      ext i
      simp only [PFun.mem_preimage, Set.mem_singleton_iff, mem_edgeFun_iff_exists_isIncident,
        isIncident_def, exists_and_left, ↓existsAndEq, and_true, exists_eq_left, Sym2.eq,
        Prod.mk.eta, Sym2.rel_iff', Prod.swap_prod_mk, Set.mem_insert_iff, and_iff_right_iff_imp]
      rintro (rfl | rfl) <;> simpa [adj_comm]
    rw [h]
    exact Set.encard_pair hne
  exists_isSource_of_mem_edgeSet G e he := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_edgeFun_iff_exists_isIncident, isIncident_def, exists_and_left, ↓existsAndEq,
        and_true, isSource_def, Prod.exists]
      use x, y, ⟨he, rfl⟩, he
  exists_isTarget_of_mem_edgeSet G e he := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_edgeFun_iff_exists_isIncident, isIncident_def, exists_and_left, ↓existsAndEq,
        and_true, isTarget_def, Prod.exists]
      use x, y, ⟨he, rfl⟩, he

instance : Undirected V (V × V) (Sym2 V) (SimpleGraph V) where
  isSource_iff G i := by simp

instance : NoMultiEdge V (V × V) (Sym2 V) (SimpleGraph V) where
  col_inj G e he f hf h := by
    classical
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
    obtain ⟨u', v', huv'⟩ := exists_isLink_of_mem_edgeSet hf
    have hne : u ≠ v := fun heq => G.loopless.irrefl u (heq ▸ IsLink.adj huv)
    have hne' : u' ≠ v' := fun heq => G.loopless.irrefl u' (heq ▸ IsLink.adj huv')
    rw [huv.incMatrixWith_col_eq_of_undirected, huv'.incMatrixWith_col_eq_of_undirected] at h
    have hu'_mem : u' = u ∨ u' = v := by
      by_contra! hc
      simpa [hc.1, hc.2, hne'] using congr_fun (congr_fun h u') 2
    obtain rfl | rfl : u = u' ∨ u = v' := by
      by_contra! hc
      simpa [hc.1, hc.2, hne] using congr_fun (congr_fun h u) 2
    · obtain rfl : v = v' := by
        by_contra! hc
        simpa [hc, hne] using congr_fun (congr_fun h v) 2
      grind
    grind

lemma edgeFun_eq {i : V × V} (hi : G.Adj i.1 i.2) : edgeFun G i = Part.some (s(i.1, i.2)) := by
  ext e
  rw [mem_edgeFun_iff_exists_isIncident]
  simp [hi, eq_comm]

lemma endPoint_eq {i : V × V} (hi : G.Adj i.1 i.2) : endPoint G i = Part.some i.1 := by
  ext v
  rw [mem_endPoint_iff_exists_isIncident]
  simp [hi, eq_comm]

instance : Loopless V (V × V) (Sym2 V) (SimpleGraph V) where
  no_loops_of_mem_mem G i j hi hj hij hne := by
    simp only [incs_def, exists_and_left, ↓existsAndEq, and_true, Set.mem_setOf_eq] at hi hj
    simp only [edgeFun_eq hi, edgeFun_eq hj, Part.some_inj, Sym2.eq, Prod.mk.eta,
      Sym2.rel_iff'] at hij
    simp only [endPoint_eq hi, endPoint_eq hj, ne_eq, Part.some_inj]
    obtain rfl | rfl := hij
    · simp at hne
    simp [hj.ne']

end SimpleGraph

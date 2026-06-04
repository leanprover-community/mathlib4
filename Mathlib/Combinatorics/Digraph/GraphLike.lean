/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-!
# Digraphs as GraphLike

This file makes `Digraph` an instance of `GraphLike`. Every adjacent pair is a dart and every
adjacent `Sym2 V` is an edge.
-/

public section

variable {V : Type*} {G : Digraph V}

open HyperGraphLike

namespace Digraph

@[simps (attr := grind =)]
instance : HyperGraphLike V (Bool × V × V) (V × V) (Digraph V) where
  verts _ := Set.univ
  edges G := { (u, v) | G.Adj u v }
  IsIncident G i e v := G.Adj e.1 e.2 ∧ i.2 = e ∧ if i.1 then e.1 = v else e.2 = v
  IsSource G i := i.1 ∧ G.Adj i.2.1 i.2.2
  IsTarget G i := ¬ i.1 ∧ G.Adj i.2.1 i.2.2
  vert_mem_of_isIncident _ _ _ _ _ := Set.mem_univ _
  edge_mem_of_isIncident G i e v := by grind
  eq_and_eq_of_isIncident_of_isIncident _ _ _ _ _ _ := by grind
  isIncident_iff G i := by
    simp +contextual only [↓existsAndEq, true_and, exists_and_left, Bool.not_eq_true, iff_def,
      and_true, Bool.eq_true_or_eq_false_self, implies_true]
    rintro (⟨hi1, hi2⟩ | ⟨hi1, hi2⟩)
    · use hi2, i.2.1, by grind
    · use hi2, i.2.2, by grind
  Adj G := G.Adj
  adj_def G u v := by simp

instance : GraphLike V (Bool × V × V) (V × V) (Digraph V) where
  order_eq_two G := by
    simp only [edges_def, Set.mem_setOf_eq, order, Prod.forall]
    intro u v hab
    have h : (edgeFun G).preimage {(u, v)} = {(true, u, v), (false, u, v)} := by
      ext i
      simp only [PFun.mem_preimage, Set.mem_singleton_iff, mem_edgeFun_iff_exists_isIncident,
        isIncident_def, exists_and_left, exists_eq_left, hab, true_and, Set.mem_insert_iff]
      refine ⟨by grind, ?_⟩
      rintro (rfl | rfl) <;> simp
    rw [h]
    exact Set.encard_pair (by simp)
  exists_isSource_of_mem_edgeSet G := by
    rintro ⟨u, v⟩ he
    simpa
  exists_isTarget_of_mem_edgeSet G := by
    rintro ⟨u, v⟩ he
    simpa

instance : Directed V (Bool × V × V) (V × V) (Digraph V) where
  not_isTarget_of_isSource G i hi := by simp_all
  not_isSource_of_isTarget G i hi := by simp_all

instance : NoMultiEdge V (Bool × V × V) (V × V) (Digraph V) where
  col_inj G e he f hf h := by
    classical
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
    obtain ⟨u', v', huv'⟩ := exists_isLink_of_mem_edgeSet hf
    rw [huv.incMatrixWith_col_eq_of_directed, huv'.incMatrixWith_col_eq_of_directed] at h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : u = u' ∧ v = v' ∨ u = v' ∧ v = u' := by
      by_contra! hc
      obtain hv : v = u' ∨ v = v' := by
        by_contra! hc
        simpa [hc.1, hc.2] using congr_fun (congr_fun h v) 1
      obtain rfl | rfl : u = u' ∨ u = v' := by
        by_contra! hc
        simpa [hc.1, hc.2] using congr_fun (congr_fun h u) 0
      all_goals
      · simp only [or_false, false_or, hc] at hv
        simp only [ne_eq, forall_const, not_true_eq_false, imp_false, and_self, hv] at hc
        simpa [hc, hv] using And.intro (congr_fun (congr_fun h v) 0) (congr_fun (congr_fun h v) 1)
    · grind
    obtain rfl | hne := eq_or_ne u v
    · grind
    simpa [hne] using congr_fun (congr_fun h u) 0

end Digraph

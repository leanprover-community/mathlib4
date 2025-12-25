/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.SuccPred.Relation
public import Mathlib.Tactic.FinCases

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `CovBy`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `SimpleGraph.hasse`: Hasse diagram of an order.
* `SimpleGraph.pathGraph`: Path graph on `n` vertices.
-/

@[expose] public section


open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type*)

section Preorder

variable [Preorder α]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm _a _b := Or.symm
  loopless _a h := h.elim (irrefl _) (irrefl _)

variable {α β} {a b : α}

@[simp]
theorem hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl

/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with map_rel_iff' := by simp [or_comm] }

@[simp]
theorem hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl

@[simp]
theorem hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

@[simp]
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by
  ext x y
  simp_rw [boxProd_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covBy_succ_of_not_isMax hc.2.not_isMax)
      fun c hc => Or.inr <| covBy_succ_of_not_isMax hc.2.not_isMax

theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen, ← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covBy_of_not_isMin hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covBy_of_not_isMin hc.1.not_isMin

end LinearOrder

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _

theorem pathGraph_adj {n : ℕ} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by
  simp only [pathGraph, hasse]
  simp_rw [← Fin.coe_covBy_iff, covBy_iff_add_one_eq]

theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _

theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩

theorem pathGraph_two_eq_top : pathGraph 2 = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph, ← Fin.coe_covBy_iff, covBy_iff_add_one_eq]

namespace Walk

variable {V : Type*} [BEq V] {G : SimpleGraph V} {u v : V} (w : G.Walk u v)

/-- The subgraph of a walk contains the path graph with the same number of vertices -/
def pathGraphHomToSubgraph : pathGraph w.support.length →g w.toSubgraph.coe where
  toFun n := ⟨w.support[n], w.mem_verts_toSubgraph.mpr <| List.getElem_mem _⟩
  map_rel' {a b} h := by
    grind [support_getElem_eq_getVert, Subgraph.coe_adj, pathGraph_adj, toSubgraph_adj_getVert,
      Subgraph.Adj.symm]

/-- A walk induces a homomorphism from a path graph to the graph -/
def pathGraphHom : pathGraph w.support.length →g G :=
  w.toSubgraph.hom.comp w.pathGraphHomToSubgraph

variable {w} in
/-- The subgraph of a path is isomorphic to the path graph with the same number of vertices -/
def IsPath.pathGraphIsoToSubgraph [LawfulBEq V] (hw : w.IsPath) :
    pathGraph w.support.length ≃g w.toSubgraph.coe where
  toFun := w.pathGraphHomToSubgraph
  invFun v :=
    ⟨w.support.idxOf v.val, List.idxOf_lt_length_of_mem <| w.mem_verts_toSubgraph.mp v.prop⟩
  left_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup]
  right_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk]
  map_rel_iff' := by
    refine ⟨fun hadj ↦ ?_, w.pathGraphHomToSubgraph.map_rel'⟩
    grind [w.toSubgraph_adj_iff.mp hadj, pathGraph_adj, getVert_eq_getD_support,
      pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup.getElem_inj_iff]

variable {w} in
/-- A walk induces a homomorphism from a path graph to the graph -/
def pathGraphCopy [LawfulBEq V] (hw : w.IsPath) : Copy (pathGraph w.support.length) G :=
  w.toSubgraph.coeCopy.comp hw.pathGraphIsoToSubgraph.toCopy

end Walk

end SimpleGraph

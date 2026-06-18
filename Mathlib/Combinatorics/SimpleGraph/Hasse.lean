/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
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

instance [Fintype α] [LT α] [DecidableLT α] : DecidableRel (CovBy : α → α → Prop) :=
  inferInstanceAs <| DecidableRel fun a b ↦ a < b ∧ ∀ ⦃c : α⦄, a < c → ¬c < b

variable [Preorder α]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a

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

/-- The Hasse diagram of a preorder is triangle-free. This is the graph-theoretic formulation of
`not_covBy_of_lt_of_lt`: if `a ⋖ b` and `b ⋖ c` then `¬a ⋖ c`. -/
theorem cliqueFree_hasse_three : (hasse α).CliqueFree 3 := by
  classical
  intro s ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := s.card_eq_three.mp hcard
  have := hc (by simp) (by simp) hab
  have := hc (by simp) (by simp) hbc
  have := hc (by simp) (by simp) hac
  grind [hasse_adj, CovBy]

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

/-- A discrete form of the intemediate value theorem – a walk in a linear graph visits all of
the vertices between its endpoints. -/
theorem discrete_intermediate_value_theorem {u v : α} (w : (hasse α).Walk u v) :
    ∀ x : α, u ≤ x ∧ x ≤ v → x ∈ w.support := by
  intro x hx
  by_cases hv : x = v
  · rw [hv]; exact w.end_mem_support
  · have ⟨d, hd, _⟩ := w.exists_boundary_dart {y | y ≤ x} hx.left (hv <| le_antisymm hx.right ·)
    rw [show x = d.fst by grind [not_le, d.adj, hasse, CovBy]]
    exact w.dart_fst_mem_support_of_mem_darts hd

/-- A discrete form of the intemediate value theorem – a walk in a linear graph visits all of
the darts between its endpoints, oriented from the walk's start to its end. -/
theorem discrete_intermediate_value_theorem_darts {u v : α} (w : (hasse α).Walk u v) :
    ∀ d : (hasse α).Dart, u ≤ d.fst ∧ d.fst < d.snd ∧ d.snd ≤ v → d ∈ w.darts := by
  intro d ⟨hud, hd, hvd⟩
  have ⟨e, he, _⟩ :=
    w.exists_boundary_dart {x | x ≤ d.fst} hud
      (lt_irrefl v <| lt_of_le_of_lt · <| lt_of_lt_of_le hd hvd)
  convert he
  ext <;> grind [d.adj, e.adj, hasse, CovBy, covBy_iff_lt_iff_le_left]

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

theorem isAcyclic_hasse_of_linearOrder : (hasse α).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  wlog hle : u < v with h
  · rw [show s(u, v) = s(v, u) by simp]
    exact h _ huv.symm <| lt_of_le_of_ne (le_of_not_gt hle) (ne_of_adj _ huv.symm)
  rw [isBridge_iff]
  intro ⟨w⟩
  have ⟨d, _⟩ := w.exists_boundary_dart {x | x < v} hle (lt_irrefl v)
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  grind [hasse, CovBy, covBy_iff_lt_iff_le_left]

end LinearOrder

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _

theorem pathGraph_adj {n : ℕ} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by simp [pathGraph, hasse]

theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _

theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩

theorem isAcyclic_pathGraph (n : ℕ) : (pathGraph n).IsAcyclic := isAcyclic_hasse_of_linearOrder _

theorem pathGraph_isTree (n : ℕ) : (pathGraph (n + 1)).IsTree :=
  ⟨pathGraph_connected n, isAcyclic_pathGraph (n + 1)⟩

theorem pathGraph_two_eq_top : pathGraph 2 = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph]

instance {n : ℕ} : LocallyFinite (pathGraph n) := by
  unfold pathGraph hasse
  infer_instance

namespace Walk

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} (w : G.Walk u v)

/-- The subgraph of a walk contains the path graph with the same number of vertices -/
def pathGraphHomToSubgraph : pathGraph (w.length + 1) →g w.toSubgraph.coe where
  toFun n := ⟨w.support[n], w.mem_verts_toSubgraph.mpr <| List.getElem_mem _⟩
  map_rel' {a b} h := by
    grind [support_getElem_eq_getVert, Subgraph.coe_adj, pathGraph_adj, toSubgraph_adj_getVert,
      Subgraph.Adj.symm]

/-- A walk induces a homomorphism from a path graph to the graph -/
def pathGraphHom : pathGraph (w.length + 1) →g G :=
  w.toSubgraph.hom.comp w.pathGraphHomToSubgraph

variable {w} in
/-- The subgraph of a path is isomorphic to the path graph with the same number of vertices -/
def IsPath.pathGraphIsoToSubgraph (hw : w.IsPath) :
    pathGraph (w.length + 1) ≃g w.toSubgraph.coe where
  toFun := w.pathGraphHomToSubgraph
  invFun v := ⟨w.support.idxOf v.val, by grind [w.mem_verts_toSubgraph]⟩
  left_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup]
  right_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk]
  map_rel_iff' := by
    refine ⟨fun hadj ↦ ?_, w.pathGraphHomToSubgraph.map_rel'⟩
    grind [w.toSubgraph_adj_iff.mp hadj, pathGraph_adj, getVert_eq_getD_support,
      pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup.getElem_inj_iff]

variable {w} in
/-- A path induces an injective homomorphism from a path graph to the graph -/
def IsPath.pathGraphCopy (hw : w.IsPath) : Copy (pathGraph <| w.length + 1) G :=
  w.toSubgraph.coeCopy.comp hw.pathGraphIsoToSubgraph.toCopy

variable {w} in
omit [DecidableEq V] in
theorem IsPath.isContained_pathGraph (hw : w.IsPath) : pathGraph (w.length + 1) ⊑ G := by
  classical
  exact ⟨hw.pathGraphCopy⟩

end Walk

end SimpleGraph

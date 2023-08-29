/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.SuccPred.Relation

#align_import combinatorics.simple_graph.hasse from "leanprover-community/mathlib"@"8a38a697305292b37a61650e2c3bd3502d98c805"

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `Covby`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `SimpleGraph.hasse`: Hasse diagram of an order.
* `SimpleGraph.pathGraph`: Path graph on `n` vertices.
-/


open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type*)

section Preorder

variable [Preorder α] [Preorder β]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm _a _b := Or.symm
  loopless _a h := h.elim (irrefl _) (irrefl _)
#align simple_graph.hasse SimpleGraph.hasse

variable {α β} {a b : α}

@[simp]
theorem hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl
#align simple_graph.hasse_adj SimpleGraph.hasse_adj

/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with map_rel_iff' := by simp [or_comm] }
                                   -- 🎉 no goals
#align simple_graph.hasse_dual_iso SimpleGraph.hasseDualIso

@[simp]
theorem hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl
#align simple_graph.hasse_dual_iso_apply SimpleGraph.hasseDualIso_apply

@[simp]
theorem hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl
#align simple_graph.hasse_dual_iso_symm_apply SimpleGraph.hasseDualIso_symm_apply

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

@[simp]
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by
  ext x y
  -- ⊢ Adj (hasse (α × β)) x y ↔ Adj (hasse α □ hasse β) x y
  simp_rw [boxProd_adj, hasse_adj, Prod.covby_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]
#align simple_graph.hasse_prod SimpleGraph.hasse_prod

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  -- ⊢ ReflTransGen (hasse α).Adj a b
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covby_succ_of_not_isMax hc.2.not_isMax)
      fun c hc => Or.inr <| covby_succ_of_not_isMax hc.2.not_isMax
#align simple_graph.hasse_preconnected_of_succ SimpleGraph.hasse_preconnected_of_succ

theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen, ← reflTransGen_swap]
  -- ⊢ ReflTransGen (Function.swap (hasse α).Adj) b a
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covby_of_not_isMin hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covby_of_not_isMin hc.1.not_isMin
#align simple_graph.hasse_preconnected_of_pred SimpleGraph.hasse_preconnected_of_pred

end LinearOrder

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _
#align simple_graph.path_graph SimpleGraph.pathGraph

theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _
#align simple_graph.path_graph_preconnected SimpleGraph.pathGraph_preconnected

theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩
#align simple_graph.path_graph_connected SimpleGraph.pathGraph_connected

end SimpleGraph

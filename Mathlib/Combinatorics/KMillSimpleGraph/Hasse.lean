/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.simple_graph.hasse
! leanprover-community/mathlib commit 8a38a697305292b37a61650e2c3bd3502d98c805
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Combinatorics.KMillSimpleGraph.Prod
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.SuccPred.Relation

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `Covby`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `SimpleGraph.hasse`: Hasse diagram of an order.
* `SimpleGraph.pathGraph`: Path graph on `n` vertices.
-/


open Order OrderDual Relation Graph

namespace SimpleGraph

variable (α β : Type _)

section Preorder

variable [Preorder α] [Preorder β]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm _a _b := Or.symm
  loopless _a h := h.elim (irrefl _) (irrefl _)

variable {α β} {a b : α}

@[simp]
theorem hasse_adj : Adj (hasse α) a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl

/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with map_rel_iff' := by simp [or_comm] }

-- Porting note: needed to add type ascription
@[simp]
theorem hasseDualIso_apply (a : αᵒᵈ) : (hasseDualIso : hasse αᵒᵈ ≃g hasse α) a = ofDual a :=
  rfl

-- Porting note: needed to add type ascription
@[simp]
theorem hasseDualIso_symm_apply (a : α) : (hasseDualIso : hasse αᵒᵈ ≃g hasse α).symm a = toDual a :=
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

@[simp]
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by
  ext (x y)
  simp_rw [boxProd_adj, hasse_adj, Prod.covby_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covby_succ_of_not_isMax hc.2.not_isMax)
      fun c hc => Or.inr <| covby_succ_of_not_isMax hc.2.not_isMax

theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen, ← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covby_of_not_isMin hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covby_of_not_isMin hc.1.not_isMin

end LinearOrder

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _

theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _

theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩

end SimpleGraph

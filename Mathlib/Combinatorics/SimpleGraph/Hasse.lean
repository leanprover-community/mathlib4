/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.ZMod.Basic
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
  simp_rw [boxProd_adj, hasse_adj, Prod.covby_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]
#align simple_graph.hasse_prod SimpleGraph.hasse_prod

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covby_succ_of_not_isMax hc.2.not_isMax)
      fun c hc => Or.inr <| covby_succ_of_not_isMax hc.2.not_isMax
#align simple_graph.hasse_preconnected_of_succ SimpleGraph.hasse_preconnected_of_succ

theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen, ← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covby_of_not_isMin hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covby_of_not_isMin hc.1.not_isMin
#align simple_graph.hasse_preconnected_of_pred SimpleGraph.hasse_preconnected_of_pred

end LinearOrder

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _
#align simple_graph.path_graph SimpleGraph.pathGraph

theorem pathGraph_adj {n : ℕ} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by
  simp only [pathGraph, hasse]
  simp_rw [← Fin.coe_covby_iff, Nat.covby_iff_succ_eq]

theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _
#align simple_graph.path_graph_preconnected SimpleGraph.pathGraph_preconnected

theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩
#align simple_graph.path_graph_connected SimpleGraph.pathGraph_connected

theorem pathGraph_two_eq_top : pathGraph 2 = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph, ← Fin.coe_covby_iff, Nat.covby_iff_succ_eq]

/-- Hommorphism from smaller path graph to bigger path graph· -/
@[simps]
protected def Hom.pathGraph {n m : ℕ} (hnm : n ≤ m) : pathGraph n →g pathGraph m where
  toFun v := ⟨v.val, trans v.is_lt hnm⟩
  map_rel' := by simp [pathGraph_adj]

protected theorem Hom.pathGraph_val {n m : ℕ} (hnm : n ≤ m) (u : Fin n) :
    (Hom.pathGraph hnm u).val = u.val := rfl


/-- Convert a homomrfism from a pathGraph to a walk -/
def pathGraph_hom_to_walk {α} (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G) :
    G.Walk (hom ⊤) (hom ⊥) := by
  induction n with
  | zero => exact Walk.nil
  | succ n ih =>
    let hom' : pathGraph (n + 1) →g G := hom.comp (.pathGraph (n + 1).le_succ)
    let w : Walk G (hom' ⊤) (hom' ⊥) := ih hom'
    have hlast : Fin.last n = ⊤ := rfl
    have hpgadj : (pathGraph (Nat.succ n + 1)).Adj ⊤ (Fin.last n) := by
      rw [pathGraph_adj]
      apply Or.inr
      rw [hlast]
      simp
      rfl
    have hlast' : (Hom.pathGraph (n + 1).le_succ) ⊤ = Fin.last n := by
      rw [Fin.coe_eq_castSucc]
      rfl
    have hGadj : G.Adj (hom ⊤) (hom' ⊤) := by
      rw [←hlast'] at hpgadj
      exact hom.map_rel hpgadj
    exact Walk.cons hGadj w

-- def walk_to_pathGraph_hom {α} (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
--     pathGraph w.length →g G where
--   toFun v := sorry
--   map_rel' := sorry

end SimpleGraph

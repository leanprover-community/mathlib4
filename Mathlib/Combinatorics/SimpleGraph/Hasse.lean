/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.Relation
import Mathlib.Tactic.FinCases

#align_import combinatorics.simple_graph.hasse from "leanprover-community/mathlib"@"8a38a697305292b37a61650e2c3bd3502d98c805"

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `CovBy`, the covering relation) and the
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
  simp_rw [boxProd_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]
#align simple_graph.hasse_prod SimpleGraph.hasse_prod

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covBy_succ_of_not_isMax hc.2.not_isMax)
      fun c hc => Or.inr <| covBy_succ_of_not_isMax hc.2.not_isMax
#align simple_graph.hasse_preconnected_of_succ SimpleGraph.hasse_preconnected_of_succ

theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen, ← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covBy_of_not_isMin hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covBy_of_not_isMin hc.1.not_isMin
#align simple_graph.hasse_preconnected_of_pred SimpleGraph.hasse_preconnected_of_pred

end LinearOrder

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _
#align simple_graph.path_graph SimpleGraph.pathGraph

theorem pathGraph_adj {n : ℕ} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by
  simp only [pathGraph, hasse]
  simp_rw [← Fin.coe_covBy_iff, Nat.covBy_iff_succ_eq]

theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _
#align simple_graph.path_graph_preconnected SimpleGraph.pathGraph_preconnected

theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩
#align simple_graph.path_graph_connected SimpleGraph.pathGraph_connected

theorem pathGraph_two_eq_top : pathGraph 2 = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph, ← Fin.coe_covBy_iff, Nat.covBy_iff_succ_eq]

/-- Hommorphism from smaller path graph to bigger path graph· -/
@[simps]
protected def Hom.pathGraph {n m : ℕ} (hnm : n ≤ m) : pathGraph n →g pathGraph m where
  toFun v := ⟨v.val, trans v.is_lt hnm⟩
  map_rel' := by simp [pathGraph_adj]

protected theorem Hom.pathGraph_val {n m : ℕ} (hnm : n ≤ m) (u : Fin n) :
    (Hom.pathGraph hnm u).val = u.val := rfl


/-- Create a walk from a path graph homomorphism. -/
def Walk.ofPathGraphHom (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G) :
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
      rw [← hlast'] at hpgadj
      exact hom.map_rel hpgadj
    exact Walk.cons hGadj w

/-- Create a path graph homomorphism and a proof that it is as expected from a walk -/
def Walk.toPathGraphHomAux (G : SimpleGraph α) :
    ∀ {u v : α} (w : G.Walk u v), Σ' (hom : pathGraph (w.length + 1) →g G), hom ⊥ = v ∧ hom ⊤ = u
  | _, _, nil' u => by
    let toFun : Fin 1 → α := fun _ => u
    let map_rel' : ∀ {a b}, (pathGraph 1).Adj a b → G.Adj (toFun a) (toFun b) := by
      intro (a : Fin 1) (b : Fin 1) (h : (pathGraph 1).Adj a b)
      have hba : b = a := Subsingleton.elim b a
      rw [hba] at h
      exact ((pathGraph 1).loopless a h).elim
    exact ⟨⟨toFun, map_rel'⟩, Prod.mk.inj_iff.mp rfl⟩
  | _, _, cons' u v w h p => by
    let hom'_w_v : Σ' (hom' : pathGraph (length p + 1) →g G), hom' ⊥ = w ∧ hom' ⊤ = v :=
      Walk.toPathGraphHomAux G p
    match hom'_w_v with
    | ⟨hom', hw, hv⟩ =>
      let fun' : Fin (length p + 1) → α := hom'.toFun
      let toFun : Fin (p.length + 2) → α := fun i =>
        if h : i.val < p.length + 1
          then fun' ⟨i.val, h⟩
          else u
      let map_rel' : ∀ {a b}, (pathGraph (p.length + 2)).Adj a b → G.Adj (toFun a) (toFun b) := by
        intro (a : Fin (length p + 2)) (b : Fin (length p + 2))
        wlog hab : a ≤ b
        · have hba : b ≤ a := le_of_not_le hab
          have hsymm : (pathGraph (p.length + 2)).Adj b a → G.Adj (toFun b) (toFun a) :=
            this α β G u w v h p hom' hw hv hba
          intro hadjab
          exact adj_symm G (hsymm (adj_symm (pathGraph (p.length + 2)) hadjab))
        intro (h' : (pathGraph (p.length + 2)).Adj a b)
        have htoFun : ∀ (c : Fin (length p + 1)), toFun c = fun' c := by
          simp [toFun]
        have hv' : v = toFun (Fin.last p.length) := by
          rw [htoFun]
          simp
          exact hv.symm
        have ha : a.val < p.length + 1 ∨ a.val = p.length + 1 :=
          Nat.lt_or_eq_of_le (Nat.le_pred_of_lt a.is_lt)
        have hb : b.val < p.length + 1 ∨ b.val = p.length + 1 :=
          Nat.lt_or_eq_of_le (Nat.le_pred_of_lt b.is_lt)
        match ha, hb with
        | Or.inl ha, Or.inl hb =>
          let a' : Fin (length p + 1) := ⟨a.val, ha⟩
          let b' : Fin (length p + 1) := ⟨b.val, hb⟩
          have hpgadj : (pathGraph (p.length + 1)).Adj a' b' := by
            rw [pathGraph_adj] at *
            exact h'
          rw [a.cast_val_eq_self.symm, b.cast_val_eq_self.symm]
          rw [htoFun a', htoFun b']
          exact hom'.map_rel hpgadj
        | Or.inl _, Or.inr hb =>
          have ha' : a.val = p.length := by
            have hab' : b.val + 1 ≠ a.val := by
              rw [hb]
              exact Nat.ne_of_gt a.prop
            have hab : a.val + 1 = b.val := (pathGraph_adj.mp h').elim id (fun h ↦ (hab' h).elim)
            rw [← hab] at hb
            exact Nat.succ_inj'.mp hb
          have ha'' : toFun a = v := by
            rw [hv']
            apply congrArg toFun
            have hlast : (Fin.last p.length).val = p.length := rfl
            rw [hlast]
            apply Fin.ext
            rw [ha']
            simp
            exact (Nat.mod_eq_of_lt (Nat.lt_add_right_iff_pos.mpr Nat.two_pos)).symm
          have hb' : toFun b = u := by
            simp [toFun, hb]
          rw [ha'', hb']
          exact adj_symm G h
        | Or.inr ha, Or.inl hb =>
          have hba : b < a := Fin.lt_def.mpr (Nat.lt_of_lt_of_eq hb ha.symm)
          apply (Nat.not_lt.mpr hab hba).elim
        | Or.inr ha, Or.inr hb =>
          have hab : b = a := Fin.ext (Eq.trans hb ha.symm)
          rw [hab] at h'
          exact ((pathGraph (p.length + 2)).loopless a h').elim
      let hom : pathGraph (p.length + 2) →g G := ⟨toFun, map_rel'⟩
      have hhom : hom ⊥ = w ∧ hom ⊤ = u := by
        have hhom' : ∀ (a : Fin (p.length + 2)), hom a = toFun a := fun a ↦ rfl
        simp only [length]
        rw [hhom' ⊥, hhom' ⊤]
        simp [toFun]
        apply And.intro
        · have hbot : (⊥ : Fin (p.length + 2)).val < p.length + 1 := Nat.compare_eq_gt.mp rfl
          simp [hbot]
          simp_rw [← hw]
          exact congrArg hom' rfl
        · intro h_
          have htop : (⊤ : Fin (p.length + 2)).val = p.length + 1 := rfl
          rw [htop] at h_
          apply (Nat.lt_irrefl (p.length + 1)).elim h_
      exact ⟨hom, hhom⟩

/-- Create a path graph homomorphism from a walk -/
def Walk.toPathGraphHom (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    pathGraph (w.length + 1) →g G := (w.toPathGraphHomAux).1

theorem Walk.toPathGraphHom_bot (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    w.toPathGraphHom ⊥ = v := (w.toPathGraphHomAux).2.1

theorem Walk.toPathGraphHom_top (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    w.toPathGraphHom ⊤ = u := (w.toPathGraphHomAux).2.2

@[simp]
theorem Walk.length_ofPathGraphHom {G : SimpleGraph α} {n : ℕ} (hom : pathGraph (n + 1) →g G) :
    (ofPathGraphHom α G hom).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Nat.succ_inj'.mpr (ih (hom.comp (Hom.pathGraph (n + 1).le_succ)))

-- Probably this is not nessessary
theorem hom_toFun (G : SimpleGraph α) (G' : SimpleGraph β) (hom : G →g G') (u : α) :
    hom u = hom.toFun u := rfl

theorem Walk.toPathGraphHom_rec (G : SimpleGraph α) {u v w : α} (h : Adj G u v) (p : Walk G v w)
    (i : Fin (p.length + 1)) :
    (cons' u v w h p).toPathGraphHom ⟨i.val, by simp [length_cons, Nat.lt_add_right]⟩ =
      p.toPathGraphHom i := by
  simp [toPathGraphHom, toPathGraphHomAux]
  match toPathGraphHomAux α G p with
  | ⟨hom', _, _⟩ =>
    rw [hom_toFun]
    simp

theorem Walk.toPathGraphHom_rec' (G : SimpleGraph α) {u v w : α} (h : Adj G u v) (p : Walk G v w)
    (i : Fin (p.length + 2)) (hi : i ≠ ⊤) :
    (cons' u v w h p).toPathGraphHom i = p.toPathGraphHom ⟨i.val, Fin.val_lt_last hi⟩ := by
  simp [toPathGraphHom, toPathGraphHomAux]
  match toPathGraphHomAux α G p with
  | ⟨hom', _, _⟩ =>
    rw [hom_toFun]
    simp [Fin.val_lt_last hi]

theorem Walk.toPathGraphHom_val (G : SimpleGraph α) {u v : α} (w : G.Walk u v)
    (i : Fin (w.length + 1)) : w.toPathGraphHom i = w.getVert (w.length - i.val) := by
  induction w with
  | nil =>
    simp [toPathGraphHom, toPathGraphHomAux]
    simp [hom_toFun]
  | @cons u v w h p ih =>
    have hi : i.val < p.length + 1 ∨ i.val = p.length + 1 :=
      Nat.lt_or_eq_of_le (Nat.le_pred_of_lt i.is_lt)
    match hi with
    | Or.inl hi =>
      rw [toPathGraphHom_rec' α G h p i (Fin.ne_of_lt hi), ih]
      simp
      rw [Nat.succ_sub (Nat.lt_succ.mp hi)]
      simp [getVert]
    | Or.inr hi =>
      simp [toPathGraphHom, toPathGraphHomAux]
      match toPathGraphHomAux α G p with
      | ⟨hom', _, _⟩ =>
        rw [hom_toFun]
        simp [hi]

theorem Walk.ofPathGraphHom_rec (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 2) →g G) (i : ℕ) :
    (ofPathGraphHom α G (hom.comp (.pathGraph (n + 1).le_succ))).getVert i =
      (ofPathGraphHom α G hom).getVert (i + 1) := rfl

theorem Walk.ofPathGraphHom_val (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G)
    (i : Fin (n + 1)) : (ofPathGraphHom α G hom).getVert (n - i.val) = hom i := by
  induction n with
  | zero =>
    simp [eq_top_of_bot_eq_top (by rfl) i]
  | succ n ih =>
    have hi : i.val < n + 1 ∨ i.val = n + 1 := Nat.lt_or_eq_of_le (Nat.le_pred_of_lt i.is_lt)
    match hi with
    | Or.inl hi =>
      rw [Nat.succ_sub (Nat.lt_succ.mp hi)]
      rw [← ofPathGraphHom_rec α G hom (n - i.val)]
      rw [ih (hom.comp (.pathGraph (n + 1).le_succ)) ⟨i.val, hi⟩]
      simp
      exact congrArg hom rfl
    | Or.inr hi =>
      have hi' : i = ⊤ := Fin.ext hi
      simp [hi]
      simp [hi']

theorem Walk.of_to_PathGraphHom (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G) :
    ∀ (i : Fin (n + 1)),
      hom i =
        (ofPathGraphHom α G hom).toPathGraphHom
          ⟨i.val, by rw [length_ofPathGraphHom]; exact i.prop⟩ := by
  simp [toPathGraphHom_val, ofPathGraphHom_val]

theorem Walk.to_of_PathGraphHom (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    ∀ (i : Fin (w.length + 1)),
      w.getVert i.val = (Walk.ofPathGraphHom α G (w.toPathGraphHom)).getVert i.val := by
  intro (i : Fin (w.length + 1))
  let j : Fin (w.length + 1) := ⟨w.length - i.val, Nat.sub_lt_succ w.length i.val⟩
  have hij : i.val = w.length - j.val := by simp [Nat.sub_sub_self i.is_le]
  rw [hij, ofPathGraphHom_val α G (w.toPathGraphHom) j]
  exact (toPathGraphHom_val α G w j).symm

end SimpleGraph

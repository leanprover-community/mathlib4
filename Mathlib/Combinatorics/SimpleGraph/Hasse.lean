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

/-- Homomorphism that includes a path graph as a prefix of another path graph. -/
@[simps]
protected def Hom.pathGraph {n m : ℕ} (hnm : n ≤ m) : pathGraph n →g pathGraph m where
  toFun v := ⟨v.val, trans v.is_lt hnm⟩
  map_rel' := by simp [pathGraph_adj]

protected theorem Hom.pathGraph_val {n m : ℕ} (hnm : n ≤ m) (u : Fin n) :
    (Hom.pathGraph hnm u).val = u.val := rfl

/-- Create a walk from a path graph homomorphism starting on the `i`-th element. -/
def Walk.ofPathGraphHom_end (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G)
    (i : Fin (n + 1)) :
    G.Walk (hom i) (hom ⊤) :=
  if hi : i = ⊤ then by rw [hi]
  else
    have hi' : i.val < n := Fin.val_lt_last hi
    let j : Fin (n + 1) := ⟨i.val + 1, Nat.add_lt_add_right hi' 1⟩
    have hij : G.Adj (hom i) (hom j) := Hom.map_adj hom (pathGraph_adj.mpr (Or.inl rfl))
    let w' : G.Walk (hom j) (hom ⊤) := Walk.ofPathGraphHom_end G hom j
    Walk.cons hij w'
termination_by n - i.val

/-- Create a walk from a path graph homomorphism. -/
def Walk.ofPathGraphHom (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G) :
    G.Walk (hom ⊥) (hom ⊤) := ofPathGraphHom_end α G hom ⊥

/-- Create a path graph homomorphism and a proof that it is as expected from a walk -/
def Walk.toPathGraphHomAux (G : SimpleGraph α) :
    ∀ {u v : α} (w : G.Walk u v), Σ' (hom : pathGraph (w.length + 1) →g G), hom ⊥ = u ∧ hom ⊤ = v
  | _, _, nil' u => by
    let toFun : Fin 1 → α := fun _ => u
    let map_rel' : ∀ {a b}, (pathGraph 1).Adj a b → G.Adj (toFun a) (toFun b) := by
      intro (a : Fin 1) (b : Fin 1) (h : (pathGraph 1).Adj a b)
      have hba : b = a := Subsingleton.elim b a
      rw [hba] at h
      exact ((pathGraph 1).loopless a h).elim
    exact ⟨⟨toFun, map_rel'⟩, Prod.mk.inj_iff.mp rfl⟩
  | _, _, cons' u v w h p => by
    let hom'_v_w : Σ' (hom' : pathGraph (length p + 1) →g G), hom' ⊥ = v ∧ hom' ⊤ = w :=
      Walk.toPathGraphHomAux G p
    match hom'_v_w with
    | ⟨hom', hv, hw⟩ =>
      let fun' : Fin (length p + 1) → α := hom'.toFun
      let toFun : Fin (p.length + 2) → α := fun i =>
        if h : i.val = 0 then
          u
        else
          fun' (i.pred (Fin.ne_of_vne h))
      let map_rel' : ∀ {a b}, (pathGraph (p.length + 2)).Adj a b → G.Adj (toFun a) (toFun b) := by
        intro (a : Fin (length p + 2)) (b : Fin (length p + 2))
        wlog hab : a ≤ b
        · have hba : b ≤ a := le_of_not_le hab
          have hsymm : (pathGraph (p.length + 2)).Adj b a → G.Adj (toFun b) (toFun a) :=
            this α β G u w v h p hom' hv hw hba
          intro hadjab
          exact adj_symm G (hsymm (adj_symm (pathGraph (p.length + 2)) hadjab))
        intro (h' : (pathGraph (p.length + 2)).Adj a b)
        match em (a.val = 0), em (b.val = 0) with
        | Or.inl ha, Or.inl hb =>
          rw [Fin.ext (Eq.trans hb ha.symm)] at h'
          exact ((pathGraph (p.length + 2)).loopless a h').elim
        | Or.inl ha, Or.inr _ =>
          have ha' : toFun a = u := by simp [toFun, ha]
          have hb : b = 1 := by
            simp only [pathGraph_adj, ha, add_eq_zero, and_false, or_false] at h'
            exact Fin.ext h'.symm
          have hb' : toFun b = v := by
            simp only [toFun, hb]
            exact hv
          rw [ha', hb']
          exact h
        | Or.inr ha, Or.inl hb =>
          have hba : b.val < a.val := hb.trans_lt (Nat.pos_of_ne_zero ha)
          apply (Nat.not_lt.mpr hab hba).elim
        | Or.inr ha, Or.inr hb =>
          let a' : Fin (length p + 1) := a.pred (Fin.ne_of_vne ha)
          have ha' : a = a'.succ := (a.succ_pred (Fin.ne_of_vne ha)).symm
          let b' : Fin (length p + 1) := b.pred (Fin.ne_of_vne hb)
          have hb' : b = b'.succ := (b.succ_pred (Fin.ne_of_vne hb)).symm
          have hab' : a.val + 1 = b.val := by
            simp only [pathGraph_adj] at h'
            apply h'.elim id ?_
            intro hba
            exact (Nat.not_lt_of_ge (Nat.succ_le.mp (Nat.le_of_eq hba)) (Nat.lt_succ.mpr hab)).elim
          rw [ha', hb']
          simp only [toFun]
          apply hom'.map_rel ?_
          simp only [Fin.pred, pathGraph_adj, Fin.coe_subNat, Fin.val_succ, b']
          rw [← hab']
          exact Or.inl (Fin.mk_eq_mk.mp ha'.symm)
      let hom : pathGraph (p.length + 2) →g G := ⟨toFun, map_rel'⟩
      have hhom : hom ⊥ = u ∧ hom ⊤ = w := by
        have hhom' : ∀ (a : Fin (p.length + 2)), hom a = toFun a := fun a ↦ rfl
        rw [hhom' ⊥, hhom' ⊤]
        apply And.intro
        · rfl
        · simp only [toFun, Nat.succ_ne_zero p.length]
          exact hw
      exact ⟨hom, hhom⟩

/-- Create a path graph homomorphism from a walk -/
def Walk.toPathGraphHom (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    pathGraph (w.length + 1) →g G := (w.toPathGraphHomAux).1

theorem Walk.toPathGraphHom_bot (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    w.toPathGraphHom ⊥ = u := (w.toPathGraphHomAux).2.1

theorem Walk.toPathGraphHom_top (G : SimpleGraph α) {u v : α} (w : G.Walk u v) :
    w.toPathGraphHom ⊤ = v := (w.toPathGraphHomAux).2.2

@[simp]
theorem Walk.length_ofPathGraphHom_end {G : SimpleGraph α} {n : ℕ} (hom : pathGraph (n + 1) →g G)
    (i : Fin (n + 1)) :
    (ofPathGraphHom_end α G hom i).length = n - i.val := by
  unfold ofPathGraphHom_end
  split_ifs
  next hi =>
    rw [Fin.mk_eq_mk.mp hi, Nat.sub_self]
    simp only [eq_mpr_eq_cast]
    refine nil_iff_length_eq.mp (nil_iff_support_eq.mpr ?_)
    subst hi
    simp [cast, support_nil]
  next hi =>
    have hi' : i.val < n := Fin.val_lt_last hi
    let j : Fin (n + 1) := ⟨i.val + 1, Nat.add_lt_add_right hi' 1⟩
    simp only [length_cons, length_ofPathGraphHom_end hom j]
    have hni : 1 ≤ n - i.val := Nat.le_sub_of_add_le' hi'
    rw [← tsub_add_cancel_of_le hni]
    rfl
termination_by n - i.val

@[simp]
theorem Walk.length_ofPathGraphHom {G : SimpleGraph α} {n : ℕ} (hom : pathGraph (n + 1) →g G) :
    (ofPathGraphHom α G hom).length = n := by
  simp only [ofPathGraphHom, length_ofPathGraphHom_end]
  rfl

theorem Walk.toPathGraphHom_val (G : SimpleGraph α) {u v : α} (w : G.Walk u v)
    (i : Fin (w.length + 1)) : w.toPathGraphHom i = w.getVert i.val := by
  induction w with
  | nil =>
    simp only [toPathGraphHom, toPathGraphHomAux]
    rfl
  | @cons u v w h p ih =>
    simp only [toPathGraphHom, toPathGraphHomAux]
    split
    if hi : i = ⊥ then
      subst hi
      rfl
    else
      have hi' : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr (Ne.intro (fun h => hi (Fin.ext h)))
      let i' : Fin (p.length + 1) := ⟨i.val - 1, (tsub_lt_iff_right hi').mpr i.prop⟩
      have hii' : i = ⟨i'.val + 1, by simp [i']; exact Nat.sub_lt_right_of_lt_add hi' i.prop⟩ := by
        apply Fin.ext
        simp only [i']
        exact Nat.eq_add_of_sub_eq hi' rfl
      rw [hii']
      simp only [getVert, Nat.add_eq, add_zero]
      rw [← ih i']
      unfold toPathGraphHom
      rename_i heq
      simp only [heq]
      rfl

theorem Walk.ofPathGraphHom_val_rec (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G)
    (i : Fin (n + 1)) (j : Fin (n + 1 - i.val)) :
    (ofPathGraphHom_end α G hom i).getVert j.val =
      hom ⟨i.val + j.val, Nat.add_lt_of_lt_sub' j.prop⟩ := by
  unfold ofPathGraphHom_end
  split_ifs
  next h =>
    have hj0 : j.val < n + 1 - i.val := j.is_lt
    simp only [Fin.mk_eq_mk.mp h, add_tsub_cancel_left, Nat.lt_one_iff] at hj0
    simp [hj0]
  next h =>
    if hj : j.val = 0 then
      simp [hj]
    else
      have h' : 1 ≤ j.val := Nat.pos_of_ne_zero hj
      have hi : i.val < n := Fin.val_lt_last h
      let i' : Fin (n + 1) := ⟨i.val + 1, Nat.add_lt_add_right hi 1⟩
      let j' : Fin (n + 1 - i'.val) := ⟨j.val - 1, by
          simp only [Nat.succ_sub_succ_eq_sub]
          apply (tsub_lt_iff_right h').mpr ?_
          rw [tsub_add_eq_add_tsub hi.le]
          exact j.prop⟩
      have ih := Walk.ofPathGraphHom_val_rec G hom i' j'
      have h2 : (cons (ofPathGraphHom_end.proof_8 α G hom i (Fin.val_lt_last h))
            (ofPathGraphHom_end α G hom i')).getVert (j'.val + 1) =
          (ofPathGraphHom_end α G hom i').getVert j'.val :=
        rfl
      simp only
      simp only [i', Nat.sub_add_cancel h'] at h2
      rw [h2, ih]
      refine DFunLike.congr_arg hom (Fin.eq_mk_iff_val_eq.mpr ?_)
      simp [i', j']
      rw [← j.val.succ_add_sub_one i.val]
      exact (Nat.add_sub_assoc h' (i.val + 1)).symm
termination_by n - i.val

theorem Walk.ofPathGraphHom_val (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G)
    (i : Fin (n + 1)) : (ofPathGraphHom α G hom).getVert i.val = hom i := by
  unfold ofPathGraphHom
  rw [ofPathGraphHom_val_rec α G hom ⊥ i]
  refine DFunLike.congr_arg hom (Fin.eq_mk_iff_val_eq.mpr ?_)
  simp only [add_left_eq_self]
  rfl

theorem Walk.of_to_PathGraphHom (G : SimpleGraph α) {n : ℕ} (hom : pathGraph (n + 1) →g G)
    (i : Fin (n + 1)) :
    hom i =
      (ofPathGraphHom α G hom).toPathGraphHom
        ⟨i.val, by rw [length_ofPathGraphHom]; exact i.prop⟩ := by
  simp [toPathGraphHom_val, ofPathGraphHom_val]

theorem Walk.to_of_PathGraphHom (G : SimpleGraph α) {u v : α} (w : G.Walk u v)
    (i : Fin (w.length + 1)) :
    w.getVert i.val = (Walk.ofPathGraphHom α G (w.toPathGraphHom)).getVert i.val := by
  rw [ofPathGraphHom_val α G (w.toPathGraphHom) i]
  exact (toPathGraphHom_val α G w i).symm

end SimpleGraph

/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Lemmas

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

namespace SimpleGraph

/-- Bicoloring of a path graph -/
def pathGraph.bicoloring (n : ℕ) :
    Coloring (pathGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

/-- Embedding of `pathGraph 2` into the first two elements of `pathGraph n` for `2 ≤ n` -/
def pathGraph_two_embedding (n : ℕ) (h : 2 ≤ n) : pathGraph 2 ↪g pathGraph n where
  toFun v := ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [pathGraph, ← Fin.coe_covby_iff]

theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).to_colorable
  apply le_antisymm
  · exact chromaticNumber_le_of_colorable hc
  · simpa only [pathGraph_two_eq_top, chromaticNumber_top] using
      hc.chromaticNumber_mono_of_embedding (pathGraph_two_embedding n h)

/-- In a bicolored graph colors alternate on every path -/
theorem pathGraph_Hom_coloring {α} (G : SimpleGraph α) (c : G.Coloring Prop) {n : ℕ}
    (hom : pathGraph (n + 1) →g G) (hc0 : c (hom ⊥)) (u : Fin (n + 1)) :
    c (hom u) ↔ Even u.val := by
  induction n with
  | zero => simpa [eq_bot_of_bot_eq_top (by decide) u] using hc0
  | succ n ih =>
    let new_hom : pathGraph (n + 1) →g G := hom.comp (.pathGraph (n + 1).le_succ)
    have h_new_hom := ih new_hom hc0
    obtain (hu : u.val < n + 1) | (hu : u.val = n + 1) := u.is_le.lt_or_eq
    · exact h_new_hom ⟨u.val, hu⟩
    -- c (hom u) ↔ Even ↑u
    let prev_last : Fin (n + 2) := ⟨n, (n + 1).le_succ⟩
    have hpgadj : (pathGraph (n + 2)).Adj prev_last u := by
      simp [pathGraph_adj, hu]
    have hGadj : G.Adj (hom prev_last) (hom u) := hom.map_rel hpgadj
    have h_c_prev_last : c (hom prev_last) ↔ Even n := h_new_hom ⟨n, Nat.lt.base n⟩
    have h_c_last : c (hom u) ↔ ¬Even n := by
      have h := eq_iff_iff.not.mp (c.valid hGadj).symm
      rw [h_c_prev_last] at h
      exact (not_iff_comm.mp (not_iff.mp h)).symm
    simp_all [Nat.even_add_one.symm, Fin.eq_mk_iff_val_eq.mpr hu, h_c_last]

theorem pathGraph_Hom_coloring' {α} (G : SimpleGraph α) (c : G.Coloring Prop) {n : ℕ}
    (hom : pathGraph (n + 1) →g G) (hc0 : ¬c (hom ⊥)) (u : Fin (n + 1)) :
    c (hom u) ↔ Odd u.val := by
  let c' : G.Coloring Prop := recolorOfEmbedding G ⟨Not, injective_not⟩ c
  have hcc' : ∀ (a : α), c a ↔ ¬c' a := fun a ↦ iff_not_comm.mp Iff.rfl
  simpa [hcc'] using (pathGraph_Hom_coloring G c' hom hc0 u).not

theorem walk_coloring_rev {α} (G : SimpleGraph α) (c : G.Coloring Prop) {u v : α} (w : G.Walk u v)
    (hcv : c v) (i : Fin (w.length + 1)) : c (w.getVert (w.length - i.val)) ↔ Even i.val := by
  let hom : pathGraph (w.length + 1) →g G := w.toPathGraphHom
  let j : Fin (w.length + 1) := ⟨w.length - i.val, Nat.sub_lt_succ w.length i.val⟩
  have hc0 : c (hom ⊥) := by
    rw [Walk.toPathGraphHom_bot]
    exact hcv
  rw [Walk.to_of_PathGraphHom α G w j]
  rw [Walk.ofPathGraphHom_val α G w.toPathGraphHom i]
  exact pathGraph_Hom_coloring G c hom hc0 i

theorem walk_coloring  {α} (G : SimpleGraph α) (c : G.Coloring Prop) {u v : α} (w : G.Walk u v)
    (hcu : c u) (i : Fin (w.length + 1)) : c (w.getVert i.val) ↔ Even i.val := by
  let w' : G.Walk v u := w.reverse
  let i' : Fin (w'.length + 1) := ⟨i.val, by simp [Walk.length_reverse]⟩
  rw [← walk_coloring_rev G c w' hcu i']
  simp [Walk.reverse_getVert, Nat.sub_sub_self i.is_le]

end SimpleGraph

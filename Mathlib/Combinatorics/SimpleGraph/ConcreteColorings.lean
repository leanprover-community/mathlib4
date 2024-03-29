/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Nat.Parity
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Logic.Function.Basic

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
    fin_cases v <;> fin_cases w <;> simp [pathGraph, ← Fin.coe_covBy_iff]

theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · simpa only [pathGraph_two_eq_top, chromaticNumber_top] using
      chromaticNumber_mono_of_embedding (pathGraph_two_embedding n h)

theorem coloring_apply_iff_of_bicoloring_of_walk_general {α} (G : SimpleGraph α)
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    c v ↔ (c u ↔ Even p.length) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff, ← Bool.eq_iff_iff]
      exact c.valid h
    tauto

theorem coloring_apply_iff_of_bicoloring_of_walk {α} (G : SimpleGraph α)
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) (hcu : c u) :
    c v ↔ Even p.length := by
  rw [coloring_apply_iff_of_bicoloring_of_walk_general G c p]
  exact iff_true_left hcu

theorem coloring_apply_iff_of_bicoloring_of_walk' {α} (G : SimpleGraph α)
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) (hcu : !c u) :
    c v ↔ Odd p.length := by
  rw [coloring_apply_iff_of_bicoloring_of_walk_general G c p, Nat.even_iff_not_odd]
  simp [(Bool.not_inj hcu : c u = false)]

theorem coloring_apply_iff_of_bicoloring_of_pathGraph {α} (G : SimpleGraph α)
    (c : G.Coloring Bool) {n : ℕ} (hom : pathGraph (n + 1) →g G) (hc0 : c (hom ⊥))
    (u : Fin (n + 1)) : c (hom u) ↔ Even u.val := by
  obtain ⟨val, hval⟩ := u
  induction val with
  | zero => simpa using hc0
  | succ val ih =>
    have : ¬ c (hom ⟨val, Nat.lt_of_succ_lt hval⟩) = true ↔ c (hom ⟨val + 1, hval⟩) := by
      rw [← not_iff, ← Bool.eq_iff_iff]
      apply c.valid
      apply hom.map_adj
      rw [pathGraph_adj]
      simp
    rw [ih] at this
    simp only [Nat.even_add_one] at this ⊢
    rw [this]

theorem coloring_apply_iff_of_bicoloring_of_pathGraph' {α} (G : SimpleGraph α)
    (c : G.Coloring Bool) {n : ℕ} (hom : pathGraph (n + 1) →g G) (hc0 : !c (hom ⊥))
    (u : Fin (n + 1)) : c (hom u) ↔ Odd u.val := by
  let c' : G.Coloring Bool :=
    recolorOfEmbedding G ⟨not, Bool.injective_iff.mpr (Bool.not_ne.mpr rfl)⟩ c
  have hcc' : ∀ (a : α), c a ↔ !c' a := fun a ↦ by
    simp [c', recolorOfEmbedding, Embedding.completeGraph]
  simpa [hcc'] using (coloring_apply_iff_of_bicoloring_of_pathGraph G c' hom hc0 u).not

/- In a bicolored graph colors alternate on evry walk -/
theorem walk_coloring {α} (G : SimpleGraph α) (c : G.Coloring Bool) {u v : α} (w : G.Walk u v)
    (hcv : c u) (i : Fin (w.length + 1)) : c (w.getVert i.val) ↔ Even i.val := by
  let hom : pathGraph (w.length + 1) →g G := w.toPathGraphHom
  have hc0 : c (hom ⊥) := by
    rw [Walk.toPathGraphHom_bot]
    exact hcv
  rw [Walk.to_of_PathGraphHom α G w i]
  rw [Walk.ofPathGraphHom_val α G w.toPathGraphHom i]
  exact coloring_apply_iff_of_bicoloring_of_pathGraph G c hom hc0 i

end SimpleGraph

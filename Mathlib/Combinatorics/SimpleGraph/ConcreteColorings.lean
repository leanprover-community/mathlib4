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
    · -- c (hom u) ↔ Even ↑u
      let last : Fin (n + 2) := ⟨n + 1, Nat.lt.base (n + 1)⟩
      let prev_last : Fin (n + 2) := ⟨n, Nat.sub_lt_succ (n + 1) 1⟩
      have hpgadj : (pathGraph (n + 2)).Adj prev_last last := by
        simp [pathGraph_adj]
      have hGadj : G.Adj (hom prev_last) (hom last) := hom.map_rel hpgadj
      have h_c_prev_last : c (hom prev_last) ↔ Even n := h_new_hom ⟨n, Nat.lt.base n⟩
      have h_c_last : c (hom last) ↔ ¬Even n := by
        have h := eq_iff_iff.not.mp (c.valid hGadj).symm
        rw [h_c_prev_last] at h
        exact (not_iff_comm.mp (not_iff.mp h)).symm
      simp [Fin.eq_mk_iff_val_eq.mpr hu, h_c_last]
      exact Nat.even_add_one.symm

theorem pathGraph_Hom_coloring' {α} (G : SimpleGraph α) (c : G.Coloring Prop) {n : ℕ}
    (hom : pathGraph (n + 1) →g G) (hc0 : ¬c (hom ⊥)) (u : Fin (n + 1)) :
    c (hom u) ↔ Odd u.val := by
  let c' : G.Coloring Prop := recolorOfEmbedding G ⟨Not, injective_not⟩ c
  have hc'c : ∀ (a : α), c' a ↔ ¬c a := fun a ↦ Iff.rfl
  have hcc' : ∀ (a : α), c a ↔ ¬c' a := fun a ↦ iff_not_comm.mp (hc'c a)
  have hc'0 : c' (hom ⊥) := by
    rw [hc'c]
    exact hc0
  rw [hcc', Nat.odd_iff_not_even]
  exact Iff.not (pathGraph_Hom_coloring G c' hom hc'0 u)

end SimpleGraph

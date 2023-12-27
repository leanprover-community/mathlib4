/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Basic

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
theorem pathGraph_G_Hom_coloring {α} (G : SimpleGraph α) (c : G.Coloring Prop) {n : ℕ} (hn : 1 ≤ n)
    (hom : pathGraph n →g G) (hc0 : c (hom ⟨0, hn⟩)) (u : Fin n) :
    c (hom u) ↔ (Even u.val) := by
  induction n with
  | zero => exact (Nat.not_succ_le_zero 0 hn).elim
  | succ n ih =>
    have hn_cases : n = 0 ∨ 1 ≤ n := or_iff_not_imp_right.mpr Nat.eq_zero_of_not_pos
    apply Or.elim hn_cases
    · intro (hn' : n = 0)
      have hu : u = 0 :=
        Fin.le_zero_iff.mp (le_of_le_of_eq (Fin.le_val_last u) (congrArg Nat.cast hn'))
      simp [hu]
      exact hc0
    · intro (hn' : 1 ≤ n)
      let new_hom : pathGraph n →g G :=
        Hom.comp hom (pathGraph_self_Hom (Nat.le_add_right n 1))
      have hhom0 : c (new_hom ⟨0, hn'⟩) := by
        simp [pathGraph_self_Hom_val, pathGraph_self_Hom]
        exact hc0
      have h_new_hom := ih hn' new_hom hhom0
      have hu : u.val < n ∨ u.val = n := le_iff_lt_or_eq.mp (Fin.is_le u)
      apply Or.elim hu
      · intro (hun : u.val < n)
        exact h_new_hom ⟨u.val, hun⟩
      · intro (hun : u.val = n)
        -- c (hom u) ↔ Even ↑u
        let last : Fin (n + 1) := ⟨n, Nat.lt.base n⟩
        let prev_last : Fin (n + 1) := ⟨n - 1, Nat.sub_lt_succ n 1⟩
        have hpgadj : (pathGraph (n + 1)).Adj prev_last last := by
          simp [pathGraph_adj]
          exact Or.intro_left (n + 1 = n - 1) (Nat.sub_add_cancel hn')
        have hGadj : G.Adj (hom prev_last) (hom last) := hom.map_rel hpgadj
        have h_c_prev_last : c (hom prev_last) ↔ (Even (n - 1)) :=
          h_new_hom ⟨n-1, Nat.sub_lt hn' Nat.one_pos⟩
        have h_c_last : c (hom last) ↔ (¬Even (n - 1)) := by
          have h := eq_iff_iff.not.1 (Coloring.valid c hGadj).symm
          rw [h_c_prev_last] at h
          exact (not_iff_comm.mp (not_iff.mp h)).symm
        simp [Fin.eq_mk_iff_val_eq.mpr hun, h_c_last]
        rw [← @Nat.sub_add_cancel n 1 hn']
        exact Nat.even_add_one.symm

theorem pathGraph_G_Hom_coloring' {α} (G : SimpleGraph α) (c : G.Coloring Prop) {n : ℕ} (hn : 1 ≤ n)
    (hom : pathGraph n →g G) (hc0 : c (hom ⟨0, hn⟩) ↔ False) (u : Fin n) :
    c (hom u) ↔ (¬Even u.val) := by
  let c' : G.Coloring Prop := Coloring.mk (fun v ↦ ¬(c v)) <| by
    intro v w
    intro (h : G.Adj v w)
    simp
    rw [not_iff_not]
    exact eq_iff_iff.not.1 (c.valid h)
  have hc'c : ∀ (a : α), c' a ↔ ¬(c a) := fun a ↦ Iff.rfl
  have hcc' : ∀ (a : α), c a ↔ ¬(c' a) := by
    intro a
    exact iff_not_comm.mp (hc'c a)
  have hc'0 : c' (hom ⟨0, hn⟩) := by
    rw [hc'c, hc0]
    exact not_false
  rw [hcc']
  exact Iff.not (pathGraph_G_Hom_coloring G c' hn hom hc'0 u)

end SimpleGraph

/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.ZMod.Basic

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph
-/

theorem aux (m n : ℕ) (h : m + 1 = n) : (m % 2 == 0) ≠ (n % 2 == 0) := by
  intro h₁
  rw [Bool.eq_iff_eq_true_iff, beq_iff_eq] at h₁
  simp only [beq_iff_eq, ←h, ←Nat.even_iff, Nat.even_add_one] at h₁
  exact not_iff_self h₁.symm

def SimpleGraph.pathGraph.bicoloring (n : ℕ) :
    SimpleGraph.Coloring (pathGraph n) Bool :=
  Coloring.mk (fun u => u.val % 2 == 0)
    (by
      intro u v h
      simp
      have : u ⋖ v ∨ v ⋖ u := by simp_all [pathGraph]
      have : u.val ⋖ v.val ∨ v.val ⋖ u.val := by simp_all [Fin.coe_covby_iff]
      have : u.val + 1 = v.val ∨ v.val + 1 = u.val := by simp_all [Nat.covby_iff_succ_eq]
      match this with
        | Or.inl h' => exact aux u v h'
        | Or.inr h' => exact (aux v u h').symm
    )


def SimpleGraph.Coloring.BoolToFin2 {α} {G : SimpleGraph α} (c : SimpleGraph.Coloring G Bool) :
    SimpleGraph.Coloring G (Fin 2) :=
  (SimpleGraph.recolorOfEquiv G (finTwoEquiv)).invFun c

theorem SimpleGraph.pathGraph.clique (n : ℕ) (h : n > 1) :
    SimpleGraph.IsClique (pathGraph n) {⟨0, Nat.zero_lt_of_lt h⟩, ⟨1, h⟩} := by
  let s : Finset (Fin n) := {⟨0, Nat.zero_lt_of_lt h⟩, ⟨1, h⟩}
  have hs : SimpleGraph.IsClique (pathGraph n) s := by
    refine (pairwise_subtype_iff_pairwise_set s (pathGraph n).Adj).mp ?_
    intro (x : s) (y : s) (hxy : x ≠ y)
    -- Adj (pathGraph n) ↑x ↑y
    simp [pathGraph]
    -- ↑x ⋖ ↑y ∨ ↑y ⋖ ↑x
    have x_val : x.val.val = 0 ∨ x.val.val = 1 := by aesop
    have i1 : x.val.val = 0 ↔ y.val.val = 1 := by aesop
    have i2 : x.val.val = 1 ↔ y.val.val = 0 := by aesop
    apply Or.elim x_val
    · intro (x0 : x.val.val = 0)
      have y1 : y.val.val = 1 := by rw [←i1, x0]
      apply Or.inl
      -- ↑x ⋖ ↑y
      simp_all [Fin.coe_covby_iff.symm]
      exact Nat.covby_iff_succ_eq.mpr rfl
    · intro (x1 : x.val.val = 1)
      have y0 : y.val.val = 0 := by rw [←i2, x1]
      apply Or.inr
      -- ↑y ⋖ ↑x
      simp_all [Fin.coe_covby_iff.symm]
      exact Nat.covby_iff_succ_eq.mpr rfl

  simp_all [Finset.mem_singleton, Fin.mk.injEq, Finset.coe_insert,
            Finset.coe_singleton, Set.mem_singleton_iff]

theorem SimpleGraph.pathGraph.chromaticNumber (n : ℕ) (h : n > 1) :
    (pathGraph n).chromaticNumber = 2 := by
  refine Nat.le_antisymm_iff.mpr ?_
  apply And.intro
  · apply SimpleGraph.chromaticNumber_le_of_colorable
    exact Nonempty.intro (SimpleGraph.pathGraph.bicoloring n).BoolToFin2
  · let s : Finset (Fin n) := {⟨0, Nat.zero_lt_of_lt h⟩, ⟨1, h⟩}
    have hs : SimpleGraph.IsClique (pathGraph n) s := by
      simp [(SimpleGraph.pathGraph.clique n)]
    apply SimpleGraph.IsClique.card_le_chromaticNumber hs

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

/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.CombinatorialMap
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Planar Graphs

This file defines planar graphs using combinatorial maps.

-/

namespace SimpleGraph

variable {D : Type}

def fromCombinatorialMap (M : CombinatorialMap D) : SimpleGraph M.vertices where
  Adj v₁ v₂ := ∃ d₁ d₂ : D, M.dartVertex d₁ = v₁ ∧ M.dartVertex d₂ = v₂ ∧ M.α d₁ = d₂ ∧ v₁ ≠ v₂
  symm := by
    intro v₁ v₂ ⟨d₁, d₂, h₁, h₂, h₃, h₄⟩
    use d₂, d₁
    exact ⟨h₂, h₁, (M.involutive.eq_iff.mp h₃).symm, h₄.symm⟩
  loopless := by tauto

end SimpleGraph

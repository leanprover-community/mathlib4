/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic.Linarith

/-!
# Dirac's theorem

In this file we state `Dirac's theorem` about `Hamiltonian graphs`.


## Main results

- `Dirac`: the statement of `Dirac's theorem`.
-/

open BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

/-- Dirac's theorem (1952): Let |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is *hamiltonian*. -/
theorem Dirac {G : SimpleGraph V} [DecidableRel G.Adj]
(CardinalityCondition: Fintype.card V ≥ 3) (MinDegreeCondition: G.minDegree ≥ Fintype.card V/2) :
G.IsHamiltonian := by
  sorry

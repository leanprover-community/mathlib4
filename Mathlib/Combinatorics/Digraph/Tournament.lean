/-
Copyright (c) 2025 Jaafar Tanoukhi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaafar Tanoukhi
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
variable {V : Type*}

namespace Digraph

def IsTournament (G : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → (G.Adj v w ↔ ¬ G.Adj w v)

-- lemma is_complete_simple_graph (G : Digraph V) (k : G.IsTournament) :
-- G.toSimpleGraphInclusive = ⊤ := by

theorem every_tournament_has_hamiltonian {V : DecidableEq} (G : Digraph V) (k : G.IsTournament) :
G.toSimpleGraphInclusive.IsHamiltonian := by sorry




end Digraph

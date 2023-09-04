import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails

open Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {u v : V}

def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1

-- See
#check SimpleGraph.Walk.IsEulerian

def SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) : Prop := sorry

def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop := sorry

theorem Dirac {G : SimpleGraph V} (degree_condition : sorry) : G.IsHamiltonian := sorry

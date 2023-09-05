import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails

open Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {u v : V}

def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1
-- See
#check SimpleGraph.Walk.IsEulerian

def SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) : Prop :=
  -- ∃ W : SimpleGraph.Walk.IsHamiltonian V ∧ Walk is from v to v.
  sorry

def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  -- ∃ W : SimpleGraph.Walk.IsHamiltonianCycle ∧ |W| = |V|
  sorry

theorem Dirac {G : SimpleGraph V} (degree_condition : sorry) : G.IsHamiltonian :=
  -- |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is hamiltonian
  sorry

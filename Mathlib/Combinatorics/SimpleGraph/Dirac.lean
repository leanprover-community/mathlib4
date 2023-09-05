import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails

open Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {u v : V}

-- #check SimpleGraph.Walk.IsEulerian

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. -/
def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1

/-- A *Hamiltonian cycle* is a *Hamiltonian path* that is a *Cycle* -/
def SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) : Prop :=
  SimpleGraph.Walk.IsHamiltonian p ∧ p.IsCycle

def SimpleGraph.IsConneted (G: SimpleGraph V) : Prop :=
  ∀ u : V, ∀ v : V, ∃ p : G.Walk u v

/-- A *Hamiltonian graph* is a *connected graph* that contains a *Hamiltonian cycle*. -/
def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  ∃ p : SimpleGraph.Walk.IsHamiltonianCycle p ∧ G SimpleGraph.IsConnected

/-- -/
def SimpleGraph.MinDegree  (G : SimpleGraph V) : Prop :=
  sorry

/-- Dirac's theorem (1952): Let |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is *hamiltonian*. -/
theorem Dirac {G : SimpleGraph V} (degree_condition : sorry) : G.IsHamiltonian :=
  -- |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is hamiltonian
  sorry

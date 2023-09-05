import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. -/
def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1

/-- If `p` is a Hamiltonian path and `w` is a member of the vertex set,
`w` is in the vertex set of `p`. -/
lemma SimpleGraph.Walk.IsHamiltonian.contains_vertex (p : G.Walk u v) (hp : p.IsHamiltonian)
    (w : V) : w ∈ p.support := by
  specialize hp w
  rw [←List.count_pos_iff_mem, hp]
  norm_num1

/-- If `p` is a Hamiltonian path -/
lemma SimpleGraph.Walk.IsHamiltonian.length (p : G.Walk u v) (hp : p.IsHamiltonian) :
    p.length = Fintype.card V - 1 := by
  sorry

/-- A *Hamiltonian cycle* is a Walk that visits every vertex once, except the initial
vertex, which is visited twice. -/
def SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) : Prop :=
  (∀ u : V, u ≠ v → p.support.count u = 1) ∧ p.support.count v = 2

lemma SimpleGraph.Walk.IsHamiltonianCycle.length (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
  p.length = Fintype.card V := by
  sorry

lemma SimpleGraph.Walk.IsHamiltonianCycle.not_nil (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    p ≠ nil := by
  rw 

lemma SimpleGraph.Walk.IsHamiltonianCycle.cycle (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
  p.IsCycle := by
  rw [SimpleGraph.Walk.IsHamiltonianCycle] at hp

  sorry

/-- A *Hamiltonian graph* is a *connected graph* that contains a *Hamiltonian cycle*. -/
def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle

/-- Dirac's theorem (1952): Let |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is *hamiltonian*. -/
theorem Dirac {G : SimpleGraph V} [DecidableRel G.Adj] (CardinalityCondition: Fintype.card V ≥ 3) (MinDegreeCondition: G.minDegree ≥ Fintype.card V/2) : G.IsHamiltonian := by
  sorry

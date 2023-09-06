import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

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
    dsimp only [IsHamiltonian] at hp
    have length_relation : p.length = p.support.length - 1
    · cases p
      case nil => 
        rfl
      case cons h' p' =>
      simp 
    · have : p.support.length = Fintype.card V
      · have : ∑ u : V, p.support.count u = Fintype.card V - 1
        · sorry
        . sorry 
      · rw [this] at length_relation
        -- exact Iff.mp Nat.succ_inj' length_relation
    


/-- A *Hamiltonian cycle* is a Walk that visits every vertex once, except the initial
vertex, which is visited twice. -/
def SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) : Prop :=
  (∀ u : V, u ≠ v → p.support.count u = 1) ∧ p.support.count v = 2

lemma SimpleGraph.Walk.IsHamiltonianCycle.length (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
  p.length = Fintype.card V := by
  dsimp only [IsHamiltonianCycle] at hp
  have length_relation : p.length + 1 = p.support.length
  · cases p
    case nil =>
      rfl
    case cons h' p' =>
      simp -- what happened here?
  · have : p.support.length = Fintype.card V + 1
    · have : ∑ u : V, p.support.count u = Fintype.card V + 1
      · sorry
      · sorry
    · rw [this] at length_relation
      exact Iff.mp Nat.succ_inj' length_relation

lemma SimpleGraph.Walk.IsHamiltonianCycle.support_tail_nodup (p : G.Walk v v)
  (hp : p.IsHamiltonianCycle) : (support p).tail.Nodup := by
  unfold IsHamiltonianCycle at hp
  rw [List.nodup_iff_count_le_one]
  intro u
  have h₁ : support p = v :: (support p).tail := by
    rw [←support_eq_cons]
  by_cases u = v
  · subst u
    replace hp := hp.2
    rw [h₁, List.count_cons] at hp
    simp at hp
    rw [hp]
  replace hp := hp.1 u h
  rw [h₁, List.count_cons] at hp
  simp [h] at hp
  rw [hp]

lemma SimpleGraph.Walk.IsHamiltonianCycle.not_nil (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    p ≠ nil := by
  unfold IsHamiltonianCycle at hp
  rintro rfl
  rw [support_nil, List.count_singleton] at hp
  simp at hp

-- BM: `cons_isCycle_iff` will be useful for going between hamiltonian cycles and paths
lemma SimpleGraph.Walk.IsHamiltonianCycle.cycle (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    p.IsCycle := by
  rw [SimpleGraph.Walk.IsHamiltonianCycle] at hp
  rw [SimpleGraph.Walk.isCycle_def]

  sorry

/-- A *Hamiltonian graph* is a *connected graph* that contains a *Hamiltonian cycle*. -/
def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle

/-- Dirac's theorem (1952): Let |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is *hamiltonian*. -/
theorem Dirac {G : SimpleGraph V} [DecidableRel G.Adj] (CardinalityCondition: Fintype.card V ≥ 3) (MinDegreeCondition: G.minDegree ≥ Fintype.card V/2) : G.IsHamiltonian := by
  sorry

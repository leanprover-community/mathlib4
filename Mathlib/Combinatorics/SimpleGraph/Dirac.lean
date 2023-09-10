import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Linarith
open BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. -/
def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1

/-- If `p` is a Hamiltonian path and `w` is a member of the vertex set of `p`. -/
lemma SimpleGraph.Walk.IsHamiltonian.contains_vertex (p : G.Walk u v) (hp : p.IsHamiltonian)
    (w : V) : w ∈ p.support := by
  specialize hp w
  rw [←List.count_pos_iff_mem, hp]
  norm_num1

/-- If `p` is a Hamiltonian path of a graph `G` its length is equal to the number of vertices of `G`.-/
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
        sorry
        -- exact Iff.mp Nat.succ_inj' length_relation

lemma Nil_iff_eq_nil {v : V} : ∀ p : G.Walk v v, p.Nil ↔ p = SimpleGraph.Walk.nil
| .nil | .cons _ _ => by simp

/-- A *Hamiltonian cycle* is a cycle `p` that visits every vertex once.-/
structure SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) extends p.IsCycle : Prop :=
(path_hamiltonian : (p.tail (by
  intro np
  rw [Nil_iff_eq_nil p] at np
  contradiction
)).IsHamiltonian)
  -- ∃ h : p.IsCycle, (p.tail (by sorry)).IsHamiltonian

/--We previously had an incorrect weaker definition, in terms of which we wrote some other proofs.
   We should eventually remove this. -/
lemma new_definition_implies_old (p : G.Walk v v) : p.IsHamiltonianCycle →
  ((∀ u : V, u ≠ v → p.support.count u = 1) ∧ p.support.count v = 2) := by
  intro hp
  constructor
  · have := hp.path_hamiltonian
    -- to do linus
    · intro u hu
      rw [@SimpleGraph.Walk.support_eq_cons]
      rw [List.count_cons]
      simp [hu]
      sorry
  · have v_ge_2 : 2 ≤ p.support.count v
    · sorry
    · have tail_nodup := hp.support_nodup
      sorry
    -- have v_ge_2 : 2 ≤ p.support.count v
    -- · -- List.count_pos_iff_mem
    --   -- count_concat
    --   have : p.support = List.concat p.support.tail v
    --   · simp
    --     rw [@SimpleGraph.Walk.support_eq_cons]
    --     simp
    --     sorry
    --   · sorry
    --   -- have : p.support.count v = p.support.tail.count v + 1
    --   -- · refine List.count_concat _ _
    --   -- · sorry
    -- · have tail_nodup := hp.support_nodup
    --   sorry

lemma SimpleGraph.Walk.IsHamiltonianCycle.contains_vertex.old (p : G.Walk v v) (hp : p.IsHamiltonianCycle)
    (w : V) : w ∈ p.support := by
  replace hp := new_definition_implies_old p hp
  rw [←List.count_pos_iff_mem]
  by_cases w = v
  · subst h
    rw [hp.2]
    norm_num
  · have := hp.1 w h
    rw [this]
    exact Nat.one_pos

lemma SimpleGraph.Walk.support_of_tail_eq_tail_of_support (p : G.Walk v v) (hnil : ¬p.Nil) : (p.tail hnil).support = p.support.tail := by
  rw [←SimpleGraph.Walk.cons_support_tail p hnil]
  rw [@List.tail_cons]

lemma SimpleGraph.Walk.IsHamiltonianCycle.contains_vertex (p : G.Walk v v) (hp : p.IsHamiltonianCycle)
    (w : V) : w ∈ p.support := by
    have : w ∈ p.support.tail
    · have hnil : ¬ Nil p
      · rw [Nil_iff_eq_nil]
        apply hp.ne_nil
      · rw [←SimpleGraph.Walk.support_of_tail_eq_tail_of_support p hnil]
        apply SimpleGraph.Walk.IsHamiltonian.contains_vertex (p.tail hnil) hp.path_hamiltonian w
    · exact List.mem_of_mem_tail this

lemma SimpleGraph.Walk.IsHamiltonianCycle.length (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
  p.length = Fintype.card V := by
  have hp' := hp
  replace hp := new_definition_implies_old p hp
  have length_relation : p.length + 1 = p.support.length
  · cases p
    case nil =>
      rfl
    case cons h' p' =>
      simp
  · have : p.support.length = Fintype.card V + 1
    · have : ∑ u : V, p.support.count u = Fintype.card V + 1
      · rw [←Finset.add_sum_erase Finset.univ p.support.count (Finset.mem_univ v)]
        rw [hp.2]
        have : ∑ u in Finset.erase Finset.univ v, p.support.count u = ∑ u in Finset.erase Finset.univ v, 1
        · apply Finset.sum_congr
          · rfl
          · intro x hx
            have hpx := hp.1 x
            rw [Finset.mem_erase] at hx
            rw [hpx hx.1]
        · rw [this]
          have : ∑ u in Finset.erase Finset.univ v, 1 = Fintype.card V - 1
          · rw [@Finset.erase_eq]
            rw [← @Finset.card_eq_sum_ones]
            rw [@Finset.card_univ_diff]
            simp
          · rw [this]
            have : 1 ≤ Fintype.card V
            · rw [@Nat.succ_le]
              rw [Fintype.card_pos_iff]
              exact Nonempty.intro u
            · rw [←add_tsub_assoc_of_le this]
              simp
              ring
      · rw [←this]
        have h₁ := Multiset.toFinset_sum_count_eq (support p : Multiset V)
        simp only [List.toFinset_coe, Multiset.mem_coe, Multiset.coe_nodup, Multiset.coe_count,
          Multiset.coe_card, length_support] at h₁
        have h₂ : p.support.toFinset = Finset.univ
        · ext a
          constructor
          · exact fun a_1 ↦ Finset.mem_univ a
          · intro ha
            rw [List.mem_toFinset]
            exact SimpleGraph.Walk.IsHamiltonianCycle.contains_vertex p hp' a
        · rw [←h₂]
          rw [h₁]
          rw [length_relation]
    · rw [this] at length_relation
      exact Iff.mp Nat.succ_inj' length_relation

lemma SimpleGraph.Walk.IsHamiltonianCycle.support_tail_nodup (p : G.Walk v v)
  (hp : p.IsHamiltonianCycle) : (support p).tail.Nodup := by
  replace hp := new_definition_implies_old p hp
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
  replace hp := new_definition_implies_old p hp
  rintro rfl
  rw [support_nil, List.count_singleton] at hp
  simp at hp

lemma SupportNodupImpliesTrail (p : G.Walk v v) (h : p.support.tail.Nodup) : p.IsTrail :=
  sorry

-- BM: `cons_isCycle_iff` will be useful for going between hamiltonian cycles and paths
lemma SimpleGraph.Walk.IsHamiltonianCycle.cycle (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    p.IsCycle := by
  exact hp.toIsCycle

/-- A *Hamiltonian graph* `G` is a *connected graph* that contains a *Hamiltonian cycle* `p`.
    By convention, the singleton graph is considered to be Hamiltonian. -/
def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  (G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle) ∨ (Fintype.card V = 1)

-- /-- Dirac's theorem (1952): Let |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is *hamiltonian*. -/
-- theorem Dirac {G : SimpleGraph V} [DecidableRel G.Adj] (CardinalityCondition: Fintype.card V ≥ 3) (MinDegreeCondition: G.minDegree ≥ Fintype.card V/2) : G.IsHamiltonian := by
--  sorry

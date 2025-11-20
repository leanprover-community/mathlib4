import Mathlib

open SimpleGraph Finset Walk Function

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A finite simple graph with at least three vertices and a bridge is not Hamiltonian.

More precisely, let `G : SimpleGraph V` be a simple graph on a finite vertex type `V`.
If `Fintype.card V ≥ 3` and there exists an edge of `G` which is a bridge,
then `G` does not admit a Hamiltonian cycle, i.e. `¬ G.IsHamiltonian`.
-/
theorem not_isHamiltonian_of_exists_isBridge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_order : Fintype.card V ≥ 3)
    (h_bridge : ∃ e : Sym2 V, G.IsBridge e) :
    ¬G.IsHamiltonian := by
  classical
  rcases h_bridge with ⟨e, he⟩

  refine Sym2.ind
    (fun x y hbr => ?_) e he

  intro hHam

  have hAdj : G.Adj x y :=
    (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbr).1
  have hxne : x ≠ y := hAdj.ne
  haveI : Nontrivial V := ⟨⟨x, y, hxne⟩⟩

  have hne : Fintype.card V ≠ 1 := by
    have : 1 < Fintype.card V := by omega
    exact ne_of_gt this
  obtain ⟨u, c, hcHam⟩ := hHam hne
  have hcycle : c.IsCycle := hcHam.isCycle

  have he_not_in_cycle : s(x, y) ∉ c.edges :=
    (SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem.mp hbr).2 c hcycle

  have hWalkAllMem :
      ∀ p : G.Walk x y, s(x, y) ∈ p.edges :=
    (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbr).2

  have hx : x ∈ c.support := hcHam.mem_support x
  have hy : y ∈ c.support := hcHam.mem_support y

  let cX := c.rotate hx
  have hcycleX : cX.IsCycle := hcycle.rotate hx

  have he_not_in_cX : s(x, y) ∉ cX.edges :=
    fun h => he_not_in_cycle ((Walk.rotate_edges c hx).mem_iff.mp h)

  have hyX : y ∈ cX.support := by
    by_cases hxy : x = y
    · subst hxy
      exact Walk.start_mem_support _
    ·
      have htail := hcHam.isHamiltonian_tail
      have hy_tail : y ∈ c.tail.support := htail.mem_support y
      have hc_not_nil : ¬c.Nil := by
        intro h
        cases h
        simp at hcycle
      have : c.tail.support = c.support.tail := Walk.support_tail c hc_not_nil
      rw [this] at hy_tail
      have hperm : cX.support.tail.Perm c.support.tail := (Walk.support_rotate c hx).perm
      have : y ∈ cX.support.tail := hperm.symm.mem_iff.mp hy_tail
      exact List.mem_of_mem_tail this

  let p := cX.takeUntil y hyX

  have he_not_in_p : s(x, y) ∉ p.edges :=
    fun h => he_not_in_cX (Walk.edges_takeUntil_subset cX hyX h)

  exact he_not_in_p (hWalkAllMem p)

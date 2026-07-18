/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer, Yue Sun, Snir Broshi
-/
module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-!
# Hamiltonian Graphs

In this file we introduce Hamiltonian paths, cycles and graphs.

## Main definitions

- `SimpleGraph.Walk.IsHamiltonian`: Predicate for a walk to be Hamiltonian.
- `SimpleGraph.Walk.IsHamiltonianCycle`: Predicate for a walk to be a Hamiltonian cycle.
- `SimpleGraph.IsHamiltonian`: Predicate for a graph to be Hamiltonian.
-/

@[expose] public section

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}
variable {a b v : α} {p : G.Walk a b} {f : G →g H}

namespace Walk

/-- A Hamiltonian path is a walk `p` that visits every vertex exactly once. Note that while
this definition doesn't contain that `p` is a path, `p.isPath` gives that. -/
def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1

variable (f) in
lemma IsHamiltonian.map (hf : Bijective f) (hp : p.IsHamiltonian) :
    (p.map f).IsHamiltonian := by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]

/-- A Hamiltonian path visits every vertex. -/
@[simp] lemma IsHamiltonian.mem_support (hp : p.IsHamiltonian) (c : α) : c ∈ p.support :=
  p.support.one_le_count_iff.mp <| hp c |>.symm.le

/-- Hamiltonian paths are paths. -/
lemma IsHamiltonian.isPath (hp : p.IsHamiltonian) : p.IsPath :=
  IsPath.mk' <| List.nodup_iff_count_le_one.2 <| (le_of_eq <| hp ·)

/-- A path whose support contains every vertex is Hamiltonian. -/
lemma IsPath.isHamiltonian_of_mem (hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) :
    p.IsHamiltonian := fun _ ↦
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff.2 (hp' _))

lemma IsPath.isHamiltonian_iff (hp : p.IsPath) : p.IsHamiltonian ↔ ∀ w, w ∈ p.support :=
  ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

theorem IsHamiltonian.of_subsingleton [Subsingleton α] : p.IsHamiltonian := by
  intro v
  rw [nil_iff_support_eq.mp p.nil_of_subsingleton, Subsingleton.elim v a, List.count_singleton_self]

/-- If a path `p` is Hamiltonian then the graph has finitely many vertices. -/
@[instance_reducible]
protected def IsHamiltonian.fintype (hp : p.IsHamiltonian) : Fintype α where
  elems := p.support.toFinset
  complete x := List.mem_toFinset.mpr (mem_support hp x)

/-- If a path `p` is Hamiltonian then the graph has finitely many vertices. -/
protected lemma IsHamiltonian.finite (hp : p.IsHamiltonian) : Finite α := by
  have := hp.fintype; infer_instance

@[simp] lemma not_isHamiltonian_of_infinite [h : Infinite α] : ¬ p.IsHamiltonian := by
  contrapose! h; exact h.finite

section
variable [Fintype α]

/-- The support of a Hamiltonian walk is the entire vertex set. -/
lemma IsHamiltonian.toFinset_support (hp : p.IsHamiltonian) : p.support.toFinset = Finset.univ := by
  simp [eq_univ_iff_forall, hp]

@[deprecated (since := "2026-03-11")]
alias IsHamiltonian.support_toFinset := IsHamiltonian.toFinset_support

omit [Fintype α] in
theorem IsHamiltonian.setOfPred_support (hp : p.IsHamiltonian) : {v | v ∈ p.support} = Set.univ :=
  Set.eq_univ_iff_forall.mpr hp.mem_support

@[deprecated (since := "2026-07-09")]
alias IsHamiltonian.setOf_support := IsHamiltonian.setOfPred_support

/-- The length of a Hamiltonian path is one less than the number of vertices of the graph. -/
lemma IsHamiltonian.length_eq (hp : p.IsHamiltonian) : p.length = Fintype.card α - 1 :=
  eq_tsub_of_add_eq <| by
    rw [← length_support, ← List.sum_toFinset_count_eq_length, Finset.sum_congr rfl fun _ _ ↦ hp _,
      ← card_eq_sum_ones, hp.toFinset_support, card_univ]

/-- The length of the support of a Hamiltonian path equals the number of vertices of the graph. -/
lemma IsHamiltonian.length_support (hp : p.IsHamiltonian) : p.support.length = Fintype.card α := by
  have : Inhabited α := ⟨a⟩
  grind [Fintype.card_ne_zero, length_eq]

end

/-- If a path `p` is Hamiltonian, then `p.support.get` defines an equivalence between
`Fin p.support.length` and `α`. -/
@[simps!]
def IsHamiltonian.supportGetEquiv (hp : p.IsHamiltonian) : Fin p.support.length ≃ α :=
  p.support.getEquivOfForallCountEqOne hp

/-- If a path `p` is Hamiltonian, then `p.getVert` defines an equivalence between
`Fin p.support.length` and `α`. -/
@[simps]
def IsHamiltonian.getVertEquiv (hp : p.IsHamiltonian) : Fin p.support.length ≃ α where
  toFun := p.getVert ∘ Fin.val
  invFun := hp.supportGetEquiv.invFun
  left_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.left_inv
  right_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.right_inv

theorem isHamiltonian_iff_support_get_bijective : p.IsHamiltonian ↔ p.support.get.Bijective :=
  p.support.get_bijective_iff.symm

theorem IsHamiltonian.getVert_surjective (hp : p.IsHamiltonian) : p.getVert.Surjective :=
  .of_comp <| p.getVert_comp_val_eq_get_support ▸
    isHamiltonian_iff_support_get_bijective.mp hp |>.surjective

omit [DecidableEq β] in
theorem IsHamiltonian.injective_of_isPath_map (hp : p.IsHamiltonian) (h : (p.map f).IsPath) :
    Function.Injective f := by
  rw [← Set.injOn_univ, ← hp.setOfPred_support]
  exact h.injOn_support_of_isPath_map

lemma isHamiltonian_iff_isPath_and_length_eq [Fintype α] :
    p.IsHamiltonian ↔ p.IsPath ∧ p.length = Fintype.card α - 1 := by
  by_cases! h : IsEmpty α
  · exact h.elim' a
  refine ⟨fun h ↦ ⟨h.isPath, h.length_eq⟩, fun ⟨hp, h⟩ ↦ ?_⟩
  have := p.isPath_iff_injective_get_support.mp hp
  refine isHamiltonian_iff_support_get_bijective.mpr ⟨this, this.surjective_of_finite ?_⟩
  refine (Fintype.equivFinOfCardEq ?_).symm
  simp_rw [length_support, h, Nat.sub_one_add_one Fintype.card_ne_zero]

/-- A Hamiltonian cycle is a cycle that visits every vertex once. -/
structure IsHamiltonianCycle (p : G.Walk a a) : Prop extends p.IsCycle where
  isHamiltonian_tail : p.tail.IsHamiltonian

variable {p : G.Walk a a}

lemma IsHamiltonianCycle.isCycle (hp : p.IsHamiltonianCycle) : p.IsCycle :=
  hp.toIsCycle

lemma IsHamiltonianCycle.map (hf : Bijective f)
    (hp : p.IsHamiltonianCycle) : (p.map f).IsHamiltonianCycle where
  toIsCycle := hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp only [IsHamiltonian, hf.surjective.forall]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [map_cons, getVert_cons_succ, tail_cons, support_copy, support_map]
    rw [List.count_map_of_injective _ _ hf.injective]
    simpa using hp.isHamiltonian_tail x

/-- If a cycle `p` is Hamiltonian then the graph has finitely many vertices. -/
protected lemma IsHamiltonianCycle.finite (hp : p.IsHamiltonianCycle) : Finite α :=
  hp.isHamiltonian_tail.finite

@[simp] lemma not_isHamiltonianCycle_of_infinite [h : Infinite α] : ¬ p.IsHamiltonianCycle := by
  contrapose! h; exact h.finite

lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩

lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ a, (support p).tail.count a = 1 := by
  simp +contextual [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    IsHamiltonian, support_tail_of_not_nil, IsCycle.not_nil]

/-- A Hamiltonian cycle visits every vertex. -/
lemma IsHamiltonianCycle.mem_support (hp : p.IsHamiltonianCycle) (b : α) :
    b ∈ p.support :=
  List.mem_of_mem_tail <|
    support_tail_of_not_nil p hp.1.not_nil ▸ hp.isHamiltonian_tail.mem_support _

/-- The length of a Hamiltonian cycle is the number of vertices. -/
lemma IsHamiltonianCycle.length_eq [Fintype α] (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card α := by
  rw [← length_tail_add_one hp.not_nil, hp.isHamiltonian_tail.length_eq, Nat.sub_add_cancel]
  rw [Nat.succ_le_iff, Fintype.card_pos_iff]
  exact ⟨a⟩

lemma IsHamiltonianCycle.count_support_self (hp : p.IsHamiltonianCycle) :
    p.support.count a = 2 := by
  rw [← cons_tail_support, List.count_cons_self,
    ← support_tail_of_not_nil _ hp.1.not_nil, hp.isHamiltonian_tail]

lemma IsHamiltonianCycle.support_count_of_ne (hp : p.IsHamiltonianCycle) (h : a ≠ b) :
    p.support.count b = 1 := by
  rw [← cons_support_tail hp.1.not_nil, List.count_cons_of_ne h, hp.isHamiltonian_tail]

lemma isHamiltonianCycle_iff_isCycle_and_length_eq [Fintype α] :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.length = Fintype.card α := by
  refine ⟨fun h ↦ ⟨h.isCycle, h.length_eq⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
  refine isHamiltonian_iff_isPath_and_length_eq.mpr ⟨h₁.isPath_tail, ?_⟩
  grind [length_tail_add_one, IsCycle.not_nil]

@[simp]
lemma isHamiltonianCycle_rotate (hv : v ∈ p.support) :
    (p.rotate v hv).IsHamiltonianCycle ↔ p.IsHamiltonianCycle := by
  cases (finite_or_infinite α).symm
  · simp
  cases nonempty_fintype α
  simp [isHamiltonianCycle_iff_isCycle_and_length_eq]

protected alias ⟨IsHamiltonianCycle.of_rotate, IsHamiltonianCycle.rotate⟩ :=
  isHamiltonianCycle_rotate

end Walk

variable [Fintype α]

/-- A Hamiltonian graph is a graph that contains a Hamiltonian cycle.

This is equivalent to there being an Hamiltonian cycle based at each vertex.
See `IsHamiltonian.exists_isHamiltonianCycle`.

By convention, the singleton graph is considered to be Hamiltonian and the empty graph is not. -/
def IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle

lemma IsHamiltonian.exists_isHamiltonianCycle [Nontrivial α] (hG : G.IsHamiltonian) (v : α) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  obtain ⟨u, p, hp⟩ := hG Fintype.one_lt_card.ne'; exact ⟨p.rotate v <| hp.mem_support _, by simpa⟩

lemma IsHamiltonian.mono {H : SimpleGraph α} (hGH : G ≤ H) (hG : G.IsHamiltonian) :
    H.IsHamiltonian :=
  fun hα ↦ let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map <| .ofLE hGH, hp.map bijective_id⟩

lemma not_isHamiltonian_of_isEmpty [IsEmpty α] : ¬G.IsHamiltonian :=
  (IsEmpty.exists_iff.mp <| · <| by simp)

lemma IsHamiltonian.connected (hG : G.IsHamiltonian) : G.Connected where
  preconnected a b := by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append <| p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.mp fun _ ↦ not_isHamiltonian_of_isEmpty hG

lemma IsHamiltonian.of_card_eq_one (h : Fintype.card α = 1) : G.IsHamiltonian :=
  (· h |>.elim)

lemma not_isHamiltonian_of_card_eq_two (h : Fintype.card α = 2) : ¬G.IsHamiltonian := by
  intro hG
  have ⟨v, p, hp⟩ := hG <| by lia
  grind [hp.three_le_length, hp.length_eq]

@[simp]
lemma not_isHamiltonian_bot_of_card_ne_one (h : Fintype.card α ≠ 1) :
    ¬(⊥ : SimpleGraph α).IsHamiltonian := by
  intro hG
  have ⟨v, p, hp⟩ := hG h
  exact p.adj_snd hp.not_nil

lemma IsHamiltonian.of_unique [Unique α] : G.IsHamiltonian :=
  of_card_eq_one <| Fintype.card_unique

/-- A finite simple graph with a bridge is not hamiltonian. -/
theorem IsBridge.not_isHamiltonian {e : Sym2 α} (he : G.IsBridge e) : ¬G.IsHamiltonian := by
  induction e with | h u v
  have := he.nontrivial
  intro hG
  obtain ⟨p, hp⟩ := hG.exists_isHamiltonianCycle u
  refine hp.isHamiltonian_tail.isPath.isTrail.not_mem_support_of_not_reachable
    (fun huv ↦ he <| .trans ?_ huv) he (hp.isHamiltonian_tail.mem_support v)
  apply hp.isTrail.isEdgeReachable_two <;> simp

-- #41721
set_option warn.sorry false in set_option linter.style.longLine false in
theorem isHamiltonian_sup_edge {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {u v : V} : (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian ∨ ∃ p : G.Walk u v, p.IsHamiltonian ∧ 2 ≤ p.length := sorry

section
variable {V : Type*} {G H : SimpleGraph V}

/-- The **Bondy-Chvátal theorem**: Adding an edge to a graph where the sum of the degrees of its
endpoints is at least the number of vertices does not change whether the graph is Hamiltonian. -/
@[wikidata Q60978620]
theorem isHamiltonian_sup_edge_iff_of_card_le_degree_add_degree [DecidableEq V] [Fintype V]
    [G.LocallyFinite] {u v : V} (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  refine ⟨fun hsup ↦ ?_, .mono le_sup_left⟩
  by_contra hG
  have ⟨p, hp, hlen⟩ := isHamiltonian_sup_edge.mp hsup |>.resolve_left hG
  -- `p` is Hamiltonian and so its support contains all the vertices exactly once.
  -- Since `a` is not adjacent to itself, all of its neighbors appear from index `1` to `|V| - 2`.
  -- Since `b` is not adjacent to itself, all of its neighbors appear from index `0` to `|V| - 1`.
  classical
  let sa := (Finset.range <| Fintype.card V - 1).filter (G.Adj u <| p.getVert <| · + 1)
  let sb := (Finset.range <| Fintype.card V - 1).filter (G.Adj v <| p.getVert ·)
  have ha : (G.neighborFinset u).card ≤ sa.card := by
    refine sa.card_le_card_of_surjOn (p.getVert <| · + 1) fun w hw ↦ ⟨p.support.idxOf w - 1, ?_⟩
    have hadj := G.mem_neighborFinset u w |>.mp hw
    have : p.support.idxOf w ≠ 0 := by grind [p.support_getElem_zero, hadj.ne]
    grind [hp.length_support, hp.mem_support, p.getVert_support_idxOf]
  have hb : (G.neighborFinset v).card ≤ sb.card := by
    refine sb.card_le_card_of_surjOn p.getVert fun w hw ↦ ⟨p.support.idxOf w, ?_⟩
    have hadj := G.mem_neighborFinset v w |>.mp hw
    have : p.support.idxOf w ≠ p.support.length - 1 := by grind [p.support_getElem_length, hadj.ne]
    grind [hp.length_support, hp.mem_support, p.getVert_support_idxOf]
  -- By assumption `|V| ≤ G.degree u + G.degree v`, and we distributed the neighbors into `|V| - 1`
  -- boxes, so by the piegonhole principle there must exist some `0 ≤ i < |V| - 1` such that
  -- `G.Adj u (p.getVert (i + 1))` and `G.Adj v (p.getVert i)`.
  grw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, ha, hb] at hdeg
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (t := sa) (u := sb)
    (Finset.filter_subset ..) (Finset.filter_subset ..) (by grind [Finset.card_range])
  have hia := (Finset.mem_filter.mp <| sa.mem_of_mem_inter_left hi).right
  have hib := (Finset.mem_filter.mp <| sa.mem_of_mem_inter_right hi).right
  -- Using those two edges and `p` we can construct a Hamiltonian cycle without `(u, v)`,
  refine hG fun _ ↦ ⟨v, p.take i |>.reverse.cons hib |>.append <| p.drop (i + 1) |>.cons hia, ?_⟩
  -- and so `G` is Hamiltonian; contradiction!
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq, Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [Walk.isPath_def, Walk.support_append, List.nodup_append]
  grind [Walk.support_take_append_support_drop, hp.length_eq, hp.isPath.support_nodup]

open scoped Classical in
/-- Two graphs `G`, `G'` are related by the Bondy-Chvátal relation if `G'` is the result of adding
an edge to `G` where the sum of the degrees of its endpoints is at least the number of vertices. -/
def BondyChvatalRel [Fintype V] (G G' : SimpleGraph V) : Prop :=
  ∃ u v, G' = G ⊔ edge u v ∧ Fintype.card V ≤ G.degree u + G.degree v

/-- The **Bondy-Chvátal theorem**, spelled using a relation. -/
@[wikidata Q60978620]
theorem isHamiltonian_iff_of_eqvGen_bondyChvatalRel [DecidableEq V] [Fintype V]
    (h : Relation.EqvGen BondyChvatalRel G H) : G.IsHamiltonian ↔ H.IsHamiltonian := by
  suffices BondyChvatalRel (V := V) ≤ Iff.onFun SimpleGraph.IsHamiltonian by
    simpa [Equivalence.of_isEquiv _ |>.eqvGen_eq] using Relation.EqvGen.mono this G H h
  rintro G H ⟨u, v, rfl, hdeg⟩
  classical
  exact .symm <| isHamiltonian_sup_edge_iff_of_card_le_degree_add_degree hdeg

-- #34799
set_option warn.sorry false in set_option linter.style.longLine false in
theorem isHamiltonian_top {V : Type*} [Fintype V] [DecidableEq V] (h : 2 < Fintype.card V) : (completeGraph V).IsHamiltonian := sorry

/-- **Ore's theorem**: If the sum of the degrees of every pair of non-adjacent vertices is at least
the number of vertices, then the graph is Hamiltonian. -/
@[wikidata Q225973]
theorem isHamiltonian_of_pairwise_not_adj_imp_card_le_degree_add_degree [DecidableEq V] [Fintype V]
    [G.LocallyFinite] (h₃ : 3 ≤ Fintype.card V)
    (h : Pairwise fun u v ↦ ¬G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  -- If `G` isn't Hamiltonian, there's a maximal non-Hamiltonian graph `H` that contains it.
  by_contra hG
  obtain ⟨H, hle, ⟨hH, hmax⟩⟩ := Finite.exists_le_maximal (p := (¬IsHamiltonian ·)) hG
  -- Since the complete graph is Hamiltonian, `H` must be missing some edge `(u, v)`,
  have ⟨u, v, hne, hadj⟩ := H.ne_top_iff_exists_not_adj.mp <| by grind [isHamiltonian_top]
  -- and by maximality adding it to `H` results in a Hamiltonian graph.
  have : (H ⊔ edge u v).IsHamiltonian := by grind [le_sup_left, sup_le_iff, edge_le_iff]
  -- By assumption we have `|V| ≤ G.degree u + G.degree v`, and the same for `H` since `G ≤ H`.
  have : Fintype.card V ≤ G.degree u + G.degree v := h hne <| mt (le_iff_adj.mp hle u v) hadj
  classical
  grw [degree_le_of_le hle, degree_le_of_le hle] at this
  -- This contradicts the Bondy-Chvátal theorem.
  grind [isHamiltonian_sup_edge_iff_of_card_le_degree_add_degree]

/-- **Dirac's theorem**: If the degree of every vertex is least half of the number of vertices,
then the graph is Hamiltonian. -/
theorem isHamiltonian_of_forall_card_le_two_mul_degree {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [G.LocallyFinite] (h₃ : 3 ≤ Fintype.card V)
    (h : ∀ v, Fintype.card V ≤ 2 * G.degree v) : G.IsHamiltonian :=
  isHamiltonian_of_pairwise_not_adj_imp_card_le_degree_add_degree h₃ <| by grind [Pairwise]

end

end SimpleGraph

/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-!
# Hamiltonian Graphs

In this file we introduce hamiltonian paths, cycles and graphs.

## Main definitions

- `SimpleGraph.Walk.IsHamiltonian`: Predicate for a walk to be hamiltonian.
- `SimpleGraph.Walk.IsHamiltonianCycle`: Predicate for a walk to be a hamiltonian cycle.
- `SimpleGraph.IsHamiltonian`: Predicate for a graph to be hamiltonian.
-/

open Finset Function
open scoped BigOperators

namespace SimpleGraph
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {G : SimpleGraph α}
  {a b : α} {p : G.Walk a b}

namespace Walk

/-- A hamiltonian path is a walk `p` that visits every vertex exactly once. Note that while
this definition doesn't contain that `p` is a path, `p.isPath` gives that. -/
def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1

lemma IsHamiltonian.map {H : SimpleGraph β} (f : G →g H) (hf : Bijective f) (hp : p.IsHamiltonian) :
    (p.map f).IsHamiltonian := by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]

/-- A hamiltonian path visits every vertex. -/
@[simp] lemma IsHamiltonian.mem_support (hp : p.IsHamiltonian) (c : α) : c ∈ p.support := by
  simp only [← List.count_pos_iff_mem, hp _, Nat.zero_lt_one]

/-- The support of a hamiltonian walk is the entire vertex set. -/
lemma IsHamiltonian.support_toFinset (hp : p.IsHamiltonian) : p.support.toFinset = Finset.univ := by
  simp [eq_univ_iff_forall, hp]

/-- The length of a hamiltonian path is one less than the number of vertices of the graph. -/
lemma IsHamiltonian.length_eq (hp : p.IsHamiltonian) : p.length = Fintype.card α - 1 :=
  eq_tsub_of_add_eq $ by
    rw [← length_support, ← List.sum_toFinset_count_eq_length, Finset.sum_congr rfl fun _ _ ↦ hp _,
      ← card_eq_sum_ones, hp.support_toFinset, card_univ]

/-- Hamiltonian paths are paths. -/
lemma IsHamiltonian.isPath (hp : p.IsHamiltonian) : p.IsPath :=
  IsPath.mk' <| List.nodup_iff_count_le_one.2 <| (le_of_eq <| hp ·)

/-- A path whose support contains every vertex is hamiltonian. -/
lemma IsPath.isHamiltonian_of_mem (hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) :
    p.IsHamiltonian := fun _ ↦
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff_mem.2 (hp' _))

lemma IsPath.isHamiltonian_iff (hp : p.IsPath) : p.IsHamiltonian ↔ ∀ w, w ∈ p.support :=
  ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

/-- A hamiltonian cycle is a cycle that visits every vertex once. -/
structure IsHamiltonianCycle (p : G.Walk a a) extends p.IsCycle : Prop :=
  isHamiltonian_tail : (p.tail toIsCycle.not_nil).IsHamiltonian

variable {p : G.Walk a a}

lemma IsHamiltonianCycle.isCycle (hp : p.IsHamiltonianCycle) : p.IsCycle :=
  hp.toIsCycle

lemma IsHamiltonianCycle.map {H : SimpleGraph β} (f : G →g H) (hf : Bijective f)
    (hp : p.IsHamiltonianCycle) : (p.map f).IsHamiltonianCycle where
  toIsCycle := hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp [IsHamiltonian, support_tail, hf.surjective.forall, List.count_tail, hf.injective]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [support_cons, List.count_cons, List.map_cons, List.head_cons, hf.injective.eq_iff,
      add_tsub_cancel_right]
    exact hp.isHamiltonian_tail _

lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail  :
    p.IsHamiltonianCycle ↔ ∃ h : p.IsCycle, (p.tail h.not_nil).IsHamiltonian :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩

lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ a, (support p).tail.count a = 1 := by
  simp only [isHamiltonianCycle_isCycle_and_isHamiltonian_tail , IsHamiltonian, support_tail,
   exists_prop]

/-- A hamiltonian cycle visits every vertex. -/
lemma IsHamiltonianCycle.mem_support (hp : p.IsHamiltonianCycle) (b : α) :
    b ∈ p.support := List.mem_of_mem_tail <| support_tail p _ ▸ hp.isHamiltonian_tail.mem_support _

/-- The length of a hamiltonian cycle is the number of vertices. -/
lemma IsHamiltonianCycle.length_eq (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card α := by
  rw [← length_tail_add_one hp.not_nil, hp.isHamiltonian_tail.length_eq, Nat.sub_add_cancel]
  rw [Nat.succ_le, Fintype.card_pos_iff]
  exact ⟨a⟩

lemma IsHamiltonianCycle.count_support_self (hp : p.IsHamiltonianCycle) :
    p.support.count a = 2 := by
  rw [support_eq_cons, List.count_cons_self, ← support_tail, hp.isHamiltonian_tail]

lemma IsHamiltonianCycle.support_count_of_ne (hp : p.IsHamiltonianCycle) (h : a ≠ b) :
    p.support.count b = 1 := by
  rw [← cons_support_tail p, List.count_cons_of_ne h.symm, hp.isHamiltonian_tail]

end Walk

/-- A hamiltonian graph is a graph that contains a hamiltonian cycle.

By convention, the singleton graph is considered to be hamiltonian. -/
def IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle

lemma IsHamiltonian.mono {H : SimpleGraph α} (hGH : G ≤ H) (hG : G.IsHamiltonian) :
    H.IsHamiltonian :=
  fun hα ↦ let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map $ .ofLE hGH, hp.map _ bijective_id⟩

lemma IsHamiltonian.connected (hG : G.IsHamiltonian) : G.Connected where
  preconnected a b := by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append $ p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.1 fun _ ↦ by simpa using hG $ by simp [@Fintype.card_eq_zero]

end SimpleGraph

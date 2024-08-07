/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Path

/-!
# Hamiltonian Graphs

In this file we introduce hamiltonian paths, cycles and graphs.

## Main definitions

- `SimpleGraph.Walk.IsHamiltonian`: Predicate for a walk to be hamiltonian.
- `SimpleGraph.Walk.IsHamiltonianCycle`: Predicate for a walk to be a hamiltonian cycle.
- `SimpleGraph.IsHamiltonian`: Predicate for a graph to be hamiltonian.
-/

open Finset Function

namespace SimpleGraph
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {G : SimpleGraph α}
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

/-- Hamiltonian paths are paths. -/
lemma IsHamiltonian.isPath (hp : p.IsHamiltonian) : p.IsPath :=
  IsPath.mk' <| List.nodup_iff_count_le_one.2 <| (le_of_eq <| hp ·)

/-- A path whose support contains every vertex is hamiltonian. -/
lemma IsPath.isHamiltonian_of_mem (hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) :
    p.IsHamiltonian := fun _ ↦
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff_mem.2 (hp' _))

lemma IsPath.isHamiltonian_iff (hp : p.IsPath) : p.IsHamiltonian ↔ ∀ w, w ∈ p.support :=
  ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

section
variable [Fintype α] [Fintype β]

/-- The support of a hamiltonian walk is the entire vertex set. -/
lemma IsHamiltonian.support_toFinset (hp : p.IsHamiltonian) : p.support.toFinset = Finset.univ := by
  simp [eq_univ_iff_forall, hp]

/-- The length of a hamiltonian path is one less than the number of vertices of the graph. -/
lemma IsHamiltonian.length_eq (hp : p.IsHamiltonian) : p.length = Fintype.card α - 1 :=
  eq_tsub_of_add_eq $ by
    rw [← length_support, ← List.sum_toFinset_count_eq_length, Finset.sum_congr rfl fun _ _ ↦ hp _,
      ← card_eq_sum_ones, hp.support_toFinset, card_univ]

end

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
    simp only [IsHamiltonian, support_tail, support_map, ne_eq, List.map_eq_nil, support_ne_nil,
      not_false_eq_true, List.count_tail, List.head_map, beq_iff_eq, hf.surjective.forall,
      hf.injective, List.count_map_of_injective]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [support_cons, List.count_cons, beq_iff_eq, List.head_cons, hf.injective.eq_iff,
      add_tsub_cancel_right]
    exact hp.isHamiltonian_tail _

lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail  :
    p.IsHamiltonianCycle ↔ ∃ h : p.IsCycle, (p.tail h.not_nil).IsHamiltonian :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩

lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ a, (support p).tail.count a = 1 := by
  simp only [isHamiltonianCycle_isCycle_and_isHamiltonian_tail, IsHamiltonian, support_tail,
    exists_prop]

/-- A hamiltonian cycle visits every vertex. -/
lemma IsHamiltonianCycle.mem_support (hp : p.IsHamiltonianCycle) (b : α) :
    b ∈ p.support := List.mem_of_mem_tail <| support_tail p _ ▸ hp.isHamiltonian_tail.mem_support _

namespace IsHamiltonianCycle

/-- The length of a hamiltonian cycle is the number of vertices. -/
lemma length_eq [Fintype α] (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card α := by
  rw [← length_tail_add_one hp.not_nil, hp.isHamiltonian_tail.length_eq, Nat.sub_add_cancel]
  rw [Nat.succ_le, Fintype.card_pos_iff]
  exact ⟨a⟩

lemma count_support_self (hp : p.IsHamiltonianCycle) :
    p.support.count a = 2 := by
  rw [support_eq_cons, List.count_cons_self, ← support_tail, hp.isHamiltonian_tail]

lemma support_count_of_ne (hp : p.IsHamiltonianCycle) (h : a ≠ b) :
    p.support.count b = 1 := by
  rw [← cons_support_tail p, List.count_cons_of_ne h.symm, hp.isHamiltonian_tail]

protected theorem transfer (hp : p.IsHamiltonianCycle) {H} (h) :
    (p.transfer H h).IsHamiltonianCycle := by
  rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at *
  refine And.intro (hp.1.transfer _) (fun a => ?_)
  simp only [support_transfer]
  exact hp.2 a

variable (b)

protected theorem rotate (hp : p.IsHamiltonianCycle) :
    IsHamiltonianCycle (p.rotate (hp.mem_support b)) := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at *
  refine And.intro ?_ (fun v => ?_)
  · apply hp.1.rotate
  · rw [← hp.2 v]
    exact List.perm_iff_count.mp (List.IsRotated.perm (by simp)) v

def mem_tail_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.tail := by
  rw [← List.count_pos_iff_mem]
  have := hp.2 b
  simp at this
  omega

def mem_dropLast_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.dropLast := by
  rw [List.IsRotated.mem_iff (IsCycle.IsRotated_dropLast_tail hp.1)]
  apply hp.mem_tail_support

noncomputable def dart_with_fst (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃d ∈ p.darts, d.fst = b by
    simpa [← Walk.map_fst_darts] using hp.mem_dropLast_support b

noncomputable def dart_with_snd (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃d ∈ p.darts, d.snd = b by
    simpa [← Walk.map_snd_darts] using hp.mem_tail_support b

protected noncomputable def next (hp : p.IsHamiltonianCycle) := (hp.dart_with_fst b).snd
protected noncomputable def prev (hp : p.IsHamiltonianCycle) := (hp.dart_with_snd b).fst

def prev_self_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = hp.prev b ∧ d.snd = b := by
  unfold IsHamiltonianCycle.prev dart_with_snd
  generalize_proofs hd
  have := hd.choose_spec
  set d := hd.choose
  use d
  simpa using this

def self_next_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = b ∧ d.snd = hp.next b := by
  unfold IsHamiltonianCycle.next dart_with_fst
  generalize_proofs hd
  have := hd.choose_spec
  set d := hd.choose
  use d
  simpa using this

def Adj_prev_self (hp : p.IsHamiltonianCycle) : G.Adj (hp.prev b) b := by
  obtain ⟨d, _, hd'⟩ := hp.prev_self_in_darts b
  exact hd'.1 ▸ hd'.2 ▸ d.adj

def Adj_self_next (hp : p.IsHamiltonianCycle) : G.Adj b (hp.next b) := by
  obtain ⟨d, _, hd'⟩ := hp.self_next_in_darts b
  exact hd'.2 ▸ hd'.1 ▸ d.adj

@[simp] def prev_next (hp : p.IsHamiltonianCycle) : hp.prev (hp.next b) = b := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hp.prev_self_in_darts (hp.next b)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hp.self_next_in_darts b
  rw [← hd₁'.1, ← hd₂'.1]
  rw [← hd₂'.2] at hd₁'
  exact hp.1.prev_unique hd₁ hd₂ hd₁'.2

@[simp] def next_prev (hp : p.IsHamiltonianCycle) : hp.next (hp.prev b) = b := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hp.self_next_in_darts (hp.prev b)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hp.prev_self_in_darts b
  rw [← hd₁'.2, ← hd₂'.2]
  rw [← hd₂'.1] at hd₁'
  exact hp.1.next_unique hd₁ hd₂ hd₁'.1

def rotate_next (hp : p.IsHamiltonianCycle) (b': α) : (hp.rotate b').next b = hp.next b := by
  unfold IsHamiltonianCycle.next dart_with_fst
  congr
  ext d
  apply Iff.and
  rw [List.IsRotated.mem_iff (p.rotate_darts _)]
  apply Iff.rfl

def next_inj (hp : p.IsHamiltonianCycle) : Function.Injective hp.next := by
  intro v₁ v₂ eq
  apply_fun hp.prev at eq
  simpa using eq

variable {b}

theorem next_ne (hp : p.IsHamiltonianCycle) : hp.next b ≠ b := by
  intro h
  exact G.irrefl (h ▸ hp.Adj_self_next b)

def support_getElem_succ (hp : p.IsHamiltonianCycle)
    {i : ℕ} (hi : i < p.length) (hi' : p.support[i]'(by simp; omega) = b) :
    p.support[i + 1]'(by simp; omega) = hp.next b := by
  have mem := List.getElem_mem p.darts i (by simpa)
  obtain ⟨d, mem', hd₂, hd₃⟩ := hp.self_next_in_darts b
  rw [← hi', ← p.darts_getElem_fst i hi] at hd₂
  rw [← p.darts_getElem_snd i hi, ← hd₃]
  exact hp.isCycle.next_unique mem mem' hd₂.symm

theorem next_next_ne (hp : p.IsHamiltonianCycle) : hp.next (hp.next b) ≠ b := by
  have mem : b ∈ p.support := by apply hp.mem_support
  let p' := p.rotate mem
  have hp' : p'.IsHamiltonianCycle := hp.rotate b
  have len_ge_3 := hp'.isCycle.three_le_length
  have p'_at_0 : p'.support[0] = b := by simp [List.getElem_zero]
  have p'_at_1 : p'.support[1]'(by simp; omega) = hp'.next b :=
    hp'.support_getElem_succ (i := 0) (by omega) p'_at_0
  have p'_at_2 : p'.support[2]'(by simp; omega) = hp'.next (hp'.next b) :=
    hp'.support_getElem_succ (i := 1) (by omega) p'_at_1
  simp only [← hp.rotate_next _ b]
  intro h
  change hp'.next (hp'.next b) = b at h
  simp_rw [← p'_at_2, ← p'_at_0] at h
  rw [← List.getElem_dropLast _ 2 (by simp; omega)] at h
  rw [← List.getElem_dropLast _ 0 (by simp; omega)] at h
  rw [List.Nodup.getElem_inj_iff hp'.support_dropLast_Nodup] at h
  simp at h

end IsHamiltonianCycle

end Walk

variable [Fintype α]

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

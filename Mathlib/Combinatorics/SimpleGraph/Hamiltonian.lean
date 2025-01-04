/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Count
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
  simp only [← List.count_pos_iff, hp _, Nat.zero_lt_one]

/-- Hamiltonian paths are paths. -/
lemma IsHamiltonian.isPath (hp : p.IsHamiltonian) : p.IsPath :=
  IsPath.mk' <| List.nodup_iff_count_le_one.2 <| (le_of_eq <| hp ·)

/-- A path whose support contains every vertex is hamiltonian. -/
lemma IsPath.isHamiltonian_of_mem (hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) :
    p.IsHamiltonian := fun _ ↦
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff.2 (hp' _))

lemma IsPath.isHamiltonian_iff (hp : p.IsPath) : p.IsHamiltonian ↔ ∀ w, w ∈ p.support :=
  ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

section
variable [Fintype α]

/-- The support of a hamiltonian walk is the entire vertex set. -/
lemma IsHamiltonian.support_toFinset (hp : p.IsHamiltonian) : p.support.toFinset = Finset.univ := by
  simp [eq_univ_iff_forall, hp]

/-- The length of a hamiltonian path is one less than the number of vertices of the graph. -/
lemma IsHamiltonian.length_eq (hp : p.IsHamiltonian) : p.length = Fintype.card α - 1 :=
  eq_tsub_of_add_eq <| by
    rw [← length_support, ← List.sum_toFinset_count_eq_length, Finset.sum_congr rfl fun _ _ ↦ hp _,
      ← card_eq_sum_ones, hp.support_toFinset, card_univ]

end

/-- A hamiltonian cycle is a cycle that visits every vertex once. -/
structure IsHamiltonianCycle (p : G.Walk a a) extends p.IsCycle : Prop where
  isHamiltonian_tail : p.tail.IsHamiltonian

variable {p : G.Walk a a}

lemma IsHamiltonianCycle.isCycle (hp : p.IsHamiltonianCycle) : p.IsCycle :=
  hp.toIsCycle

lemma IsHamiltonianCycle.map {H : SimpleGraph β} (f : G →g H) (hf : Bijective f)
    (hp : p.IsHamiltonianCycle) : (p.map f).IsHamiltonianCycle where
  toIsCycle := hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp only [IsHamiltonian, hf.surjective.forall]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [map_cons, getVert_cons_succ, tail_cons_eq, support_copy,support_map]
    rw [List.count_map_of_injective _ _ hf.injective, ← support_copy, ← tail_cons_eq]
    exact hp.isHamiltonian_tail _

lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail  :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩

lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ a, (support p).tail.count a = 1 := by
  simp +contextual [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    IsHamiltonian, support_tail, IsCycle.not_nil, exists_prop]

/-- A hamiltonian cycle visits every vertex. -/
lemma IsHamiltonianCycle.mem_support (hp : p.IsHamiltonianCycle) (b : α) :
    b ∈ p.support :=
  List.mem_of_mem_tail <| support_tail p hp.1.not_nil ▸ hp.isHamiltonian_tail.mem_support _

namespace IsHamiltonianCycle

open scoped List

/-- The length of a hamiltonian cycle is the number of vertices. -/
lemma length_eq [Fintype α] (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card α := by
  rw [← length_tail_add_one hp.not_nil, hp.isHamiltonian_tail.length_eq, Nat.sub_add_cancel]
  rw [Nat.succ_le, Fintype.card_pos_iff]
  exact ⟨a⟩

lemma count_support_self (hp : p.IsHamiltonianCycle) :
    p.support.count a = 2 := by
  rw [support_eq_cons, List.count_cons_self, ← support_tail _ hp.1.not_nil, hp.isHamiltonian_tail]

lemma support_count_of_ne (hp : p.IsHamiltonianCycle) (h : a ≠ b) :
    p.support.count b = 1 := by
  rw [← cons_support_tail p hp.1.not_nil, List.count_cons_of_ne h.symm, hp.isHamiltonian_tail]

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

lemma mem_tail_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.tail := by
  rw [← List.count_pos_iff_mem]
  have := hp.2 b
  rw [← Walk.support_tail _ hp.not_nil]
  omega

lemma mem_dropLast_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.dropLast := by
  rw [List.IsRotated.mem_iff (IsRotated_dropLast_tail p)]
  apply hp.mem_tail_support

/-- The dart in the Hamiltonian cycle that starts at `b` -/
noncomputable def dartWithFst (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃d ∈ p.darts, d.fst = b by
    simpa [← Walk.map_fst_darts] using hp.mem_dropLast_support b

/-- The dart in the Hamiltonian cycle that ends at `b` -/
noncomputable def dartWithSnd (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃d ∈ p.darts, d.snd = b by
    simpa [← Walk.map_snd_darts] using hp.mem_tail_support b

/-- The next vertex in the Hamiltonian cycle -/
protected noncomputable def next (hp : p.IsHamiltonianCycle) := (hp.dartWithFst b).snd
/-- The previous vertex in the Hamiltonian cycle -/
protected noncomputable def prev (hp : p.IsHamiltonianCycle) := (hp.dartWithSnd b).fst

lemma prev_self_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = hp.prev b ∧ d.snd = b := by
  unfold IsHamiltonianCycle.prev dartWithSnd
  generalize_proofs hd
  have := hd.choose_spec
  set d := hd.choose
  use d
  simpa using this

lemma self_next_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = b ∧ d.snd = hp.next b := by
  unfold IsHamiltonianCycle.next dartWithFst
  generalize_proofs hd
  have := hd.choose_spec
  set d := hd.choose
  use d
  simpa using this

lemma adj_prev_left (hp : p.IsHamiltonianCycle) : G.Adj (hp.prev b) b := by
  obtain ⟨d, _, hd'⟩ := hp.prev_self_in_darts b
  exact hd'.1 ▸ hd'.2 ▸ d.adj

lemma Adj_self_next (hp : p.IsHamiltonianCycle) : G.Adj b (hp.next b) := by
  obtain ⟨d, _, hd'⟩ := hp.self_next_in_darts b
  exact hd'.2 ▸ hd'.1 ▸ d.adj

@[simp] lemma prev_next (hp : p.IsHamiltonianCycle) : hp.prev (hp.next b) = b := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hp.prev_self_in_darts (hp.next b)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hp.self_next_in_darts b
  rw [← hd₁'.1, ← hd₂'.1]
  rw [← hd₂'.2] at hd₁'
  exact hp.1.prev_unique hd₁ hd₂ hd₁'.2

@[simp] lemma next_prev (hp : p.IsHamiltonianCycle) : hp.next (hp.prev b) = b := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hp.self_next_in_darts (hp.prev b)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hp.prev_self_in_darts b
  rw [← hd₁'.2, ← hd₂'.2]
  rw [← hd₂'.1] at hd₁'
  exact hp.1.next_unique hd₁ hd₂ hd₁'.1

lemma rotate_next (hp : p.IsHamiltonianCycle) (b': α) : (hp.rotate b').next b = hp.next b := by
  unfold IsHamiltonianCycle.next dartWithFst
  congr
  ext d
  apply Iff.and
  rw [List.IsRotated.mem_iff (p.rotate_darts _)]
  apply Iff.rfl

lemma next_inj (hp : p.IsHamiltonianCycle) : Function.Injective hp.next := by
  intro v₁ v₂ eq
  apply_fun hp.prev at eq
  simpa using eq

variable {b}

theorem next_ne (hp : p.IsHamiltonianCycle) : hp.next b ≠ b := by
  intro h
  exact G.irrefl (h ▸ hp.Adj_self_next b)

lemma support_getElem_succ (hp : p.IsHamiltonianCycle)
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

theorem IsHamiltonianCycle_iff_support_count
    (hp : p.length ≥ 3) (hp' : ∀ (a : α), List.count a p.support.tail = 1) :
    p.IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine And.intro ?_ hp'
  apply And.intro
  · rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij
    unfold Walk.edges
    have nodup : p.support.tail.Nodup := by
      rw [List.nodup_iff_count_le_one]
      exact fun a => le_of_eq (hp' a)
    rw [List.Nodup, List.pairwise_iff_getElem] at nodup
    have h₁ : i < p.length := by simpa using hi
    have h₂ : j < p.length := by simpa using hj
    have h₃ : i < p.darts.length := by simpa using hi
    have h₄ : j < p.darts.length := by simpa using hj
    have h₅ : i < p.support.tail.length := by simpa using hi
    have h₆ : j < p.support.tail.length := by simpa using hj
    simp only [length_edges] at hi
    simp only [List.getElem_map, ne_eq, dart_edge_eq_iff, not_or]
    apply And.intro
    · have h₇ := p.darts_getElem_snd_eq_support_tail i h₁
      have h₈ := p.darts_getElem_snd_eq_support_tail j h₂
      suffices p.darts[i].snd ≠ p.darts[j].snd by
        contrapose this
        simp at this |-
        congr
      simp only [h₇, h₈]
      exact nodup i j h₅ h₆ hij
    · intro h
      by_cases ij : i + 1 < j
      · apply_fun (·.snd) at h
        simp only [Dart.symm_toProd, Prod.snd_swap] at h
        rw [p.darts_getElem_snd_eq_support_tail i h₁,
          p.darts_getElem_fst_eq_support_tail j (by omega)] at h
        exact nodup i (j - 1) h₅ (by omega) (by omega) h
      · apply_fun (·.fst) at h
        by_cases i0 : i = 0
        · simp only [i0, List.getElem_zero,
            p.head_darts_fst (by apply List.ne_nil_of_length_pos; simp; omega)] at h
          have : p.support.tail[p.length - 1]'(by simp; omega) = a := by
            simp [List.getElem_tail, show p.length - 1 + 1 = p.length by omega,
              support_getElem_eq_getVert]
          simp only [← this, Dart.symm_toProd, Prod.fst_swap,
            p.darts_getElem_snd_eq_support_tail j h₂] at h
          exact nodup j (p.length - 1) h₆ (by simp; omega) (by omega) h.symm
        · simp only [p.darts_getElem_fst_eq_support_tail i (by omega),
            p.darts_getElem_snd_eq_support_tail j h₂, Dart.symm_toProd, Prod.fst_swap] at h
          exact nodup (i - 1) j  (by omega) h₆ (by omega) h
  · apply And.intro
    · intro nil_p
      apply_fun (·.length) at nil_p
      simp only [Walk.length_nil] at nil_p
      omega
    · rw [List.nodup_iff_count_le_one]
      exact fun a => le_of_eq (hp' a)

theorem isHamiltonianCycle_of_tail_toFinset
    [Fintype α] (hp : p.length = Fintype.card α)
    (hα : Fintype.card α ≥ 3) (hp' : p.support.tail.toFinset = Finset.univ) :
    p.IsHamiltonianCycle := by
  apply IsHamiltonianCycle_iff_support_count
  rwa [hp]
  suffices p.support.tail ~ Finset.univ.toList by
    intro a
    rw [List.Perm.count_eq this]
    apply List.count_eq_one_of_mem
    apply Finset.nodup_toList
    simp
  apply List.Perm.symm
  apply List.Subperm.perm_of_length_le
  · rw [List.subperm_ext_iff]
    intro a ha
    rw [List.count_eq_one_of_mem (Finset.nodup_toList _) ha]
    rw [Nat.succ_le, List.count_pos_iff_mem]
    rwa [Finset.mem_toList, ← hp', List.mem_toFinset] at ha
  · simp [hp]

end IsHamiltonianCycle

end Walk

variable [Fintype α]

/-- A hamiltonian graph is a graph that contains a hamiltonian cycle.

By convention, the singleton graph is considered to be hamiltonian. -/
def IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle

lemma IsHamiltonian.mono {H : SimpleGraph α} (hGH : G ≤ H) (hG : G.IsHamiltonian) :
    H.IsHamiltonian :=
  fun hα ↦ let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map <| .ofLE hGH, hp.map _ bijective_id⟩

lemma IsHamiltonian.connected (hG : G.IsHamiltonian) : G.Connected where
  preconnected a b := by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append <| p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.1 fun _ ↦ by simpa using hG <| by simp [@Fintype.card_eq_zero]

theorem IsHamiltonian.complete_graph (hα : Fintype.card α = 1 ∨ Fintype.card α ≥ 3) :
    IsHamiltonian (⊤ : SimpleGraph α) := by
  cases' hα with hα hα
  · simpa [IsHamiltonian] using absurd hα
  · have ne : (⊤ : Finset α).toList ≠ [] := by
      simp [← Finset.card_eq_zero]
      omega
    let p := Walk.cons
      (show (⊤ : SimpleGraph α).Adj
          ((⊤ : Finset α).toList.getLast ne) ((⊤ : Finset α).toList.head ne) by
        simp [List.getLast_eq_getElem]
        rw [← List.getElem_zero (by simp; omega), List.Nodup.getElem_inj_iff]
        omega
        exact Finset.univ.nodup_toList)
      (Walk.fromList (G := ⊤) ne
        (by simpa using List.Pairwise.chain' Finset.univ.nodup_toList))
    suffices p.IsHamiltonianCycle from fun _ => ⟨((⊤ : Finset α).toList.getLast ne), p, this⟩
    apply Walk.IsHamiltonianCycle.isHamiltonianCycle_of_tail_toFinset
    · simp [p, ← Walk.length_support, Walk.fromList_support]
    · exact hα
    · simp [p, Walk.fromList_support]

end SimpleGraph

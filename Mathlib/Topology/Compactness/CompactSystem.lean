/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `isCompactSystem_insert_univ_iff`: A set system is a compact system iff inserting `univ`
  gives a compact system.
* `isCompactSystem_isCompact_isClosed`: The set of closed and compact sets is a compact system.
* `isCompactSystem_isCompact`: In a `T2Space`, the set of compact sets is a compact system.
* `IsCompactSystem.union_isCompactSystem`If `IsCompactSystem S`, the set of finite unions of sets
in `S` is also a compact system.
-/

@[expose] public section

open Set Finset Nat

variable {α : Type*} {S : Set (Set α)} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (S : Set (Set α)) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

lemma of_nonempty_iInter
    (h : ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :
    IsCompactSystem S := by
  intro C hC
  contrapose!
  exact h C hC

lemma nonempty_iInter (hp : IsCompactSystem S) {C : ℕ → Set α} (hC : ∀ i, C i ∈ S)
    (h_nonempty : ∀ n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC

theorem iff_nonempty_iInter (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

lemma iff_nonempty_iInter_of_lt' (S : Set (Set α)) : IsCompactSystem S ↔
    ∀ C : ℕ → Set α, (∀ i, C i ∈ S) →
    (∀ n, (⋂ k : Fin (n + 1), C k).Nonempty) → (⋂ i, C i).Nonempty := by
  rw [iff_nonempty_iInter]
  simp_rw [dissipate_eq_ofFin]

@[simp]
lemma of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- Any subset of a compact system is a compact system. -/
theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S ⊆ T) :
    IsCompactSystem S := fun C hC1 hC2 ↦ hT C (fun i ↦ hST (hC1 i)) hC2

/-- Inserting `∅` into a compact system gives a compact system. -/
lemma insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S) := by
  intro s h' hd
  by_cases g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · push_neg at g
    exact h s (fun i ↦ (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

/-- Inserting `univ` into a compact system gives a compact system. -/
lemma insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S) := by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases h₀ : ∀ n, s n ∉ S
  · simp_all
  push_neg at h₀
  classical
  let n := Nat.find h₀
  let s' := fun i ↦ if s i ∈ S then s i else s n
  have h₁ : ∀ i, s' i ∈ S := by simp [s']; grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! ⟨j, hj⟩
  have h₃ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v := by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

end IsCompactSystem

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ h C hi (fun n ↦ dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' ↦ h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g ↦ h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le_trans (fun x ↦ by simp; grind) g

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma isCompactSystem_insert_empty_iff :
    IsCompactSystem (insert ∅ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_empty⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_univ⟩

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
theorem isCompactSystem_iff_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
      ∀ (C : ℕ → Set α), Directed (· ⊇ ·) C → (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ n, C n = ∅ := by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (∀ n, dissipate C n ∈ S ∨ dissipate C n = ∅) ∧ (⋂ n, dissipate C n = ∅) by
    by_cases! f : ∀ n, dissipate C n ∈ S
    · exact h (dissipate C) directed_dissipate f this.2
    · obtain ⟨n, hn⟩ := f
      exact ⟨n, by simpa [hn] using this.1 n⟩
  refine ⟨fun n ↦ ?_, h2⟩
  by_cases g : (dissipate C n).Nonempty
  · simpa [or_comm] using hpi.insert_empty.dissipate_mem h1 n g
  · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
theorem isCompactSystem_iff_nonempty_iInter_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    ∀ (C : ℕ → Set α), (Directed (· ⊇ ·) C) → (∀ i, C i ∈ S) → (∀ n, (C n).Nonempty) →
      (⋂ i, C i).Nonempty := by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

/-- The set of compact and closed sets is a compact system. -/
theorem isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem {s : Set α | IsCompact s ∧ IsClosed s} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty ↦ ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) h_nonempty ?_ (fun n ↦ isClosed_biInter (fun i _ ↦ (hC_cc i).2))
  · exact Set.antitone_dissipate (by lia)
  · simpa using (hC_cc 0).1

/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] :
    IsCompactSystem {s : Set α | IsCompact s} := by
  convert isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed

section PrefixInduction

-- Should this section be private, or moved to a different file?

/- In this section, we prove a general induction principle, which we need for the construction
`Nat.prefixInduction q step0 step : (k : ℕ) →  (β k)` based on some
`q : (n : ℕ) → (k : (i : Fin n) → (β i)) → Prop`. For
the induction start, `step0 : q 0 _` always holds since `Fin 0` cannot be satisfied, and
`step : (n : ℕ) → (k : (i : Fin n) → β i) → q n k → { a : β n // q (n + 1) (Fin.snoc k a) })`
`(n : ℕ) : β n` constructs the next element satisfying `q (n + 1) _` from a proof of `q n k`
and finding the next element.

In comparison to other induction principles, the proofs of `q n k` are needed in order to find
the next element. -/


/- A version of `Fin.elim0` using dependent types. -/
def Fin.elim0'.{u} {α : ℕ → Sort u} : (i : Fin 0) → (α i)
  | ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

variable {β : ℕ → Type*}
variable (q : ∀ n, (k : (i : Fin n) → (β i)) → Prop)
variable (step0 : q 0 Fin.elim0')
variable (step :
    ∀ n (k : (i : Fin n) → (β i)) (_ : q n k),
    { a : β n // q (n+1) (Fin.snoc k a)})

def Nat.prefixInduction.aux : ∀ (n : Nat), { k : (i : Fin n) → (β i) // q n k }
    | 0 => ⟨Fin.elim0', step0⟩
    | n+1 =>
      let ⟨k, hk⟩ := aux n
      let ⟨a, ha⟩ := step n k hk
      ⟨Fin.snoc k a, ha⟩

theorem Nat.prefixInduction.auxConsistent :
  ∀ n (i : Fin n),
    (Nat.prefixInduction.aux q step0 step (i+1)).1 (Fin.last i) =
    (Nat.prefixInduction.aux q step0 step n).1 i := by
  intro n
  induction n
  next => simp
  next n ih =>
    apply Fin.lastCases
    case last => simp
    case cast =>
      intro i
      simp only [Fin.val_castSucc]
      rw [ih, aux]
      simp

/-- An induction principle showing that `q : (n : ℕ) → (k : (i : Fin n) → (β i)) → Prop` holds
for all `n`. `step0` is satisfied by construction since `Fin 0` is empty.
In the induction `step`, we use that `q n k` holds for showing that `q (n + 1) (Fin.snoc k a)`
holds for some `a : β n`. -/
def Nat.prefixInduction (n : Nat) : β n :=
  (Nat.prefixInduction.aux q step0 step (n+1)).1 (Fin.last n)

theorem Nat.prefixInduction_spec (n : Nat) : q n (Nat.prefixInduction q step0 step ·) := by
  cases n
  · convert step0
  · next n =>
    have hk := (Nat.prefixInduction.aux q step0 step (n+1)).2
    convert hk with i
    apply Nat.prefixInduction.auxConsistent

/- Often, `step` can only be proved by showing an `∃` statement. For this case, we use `step'`. -/
variable (step' : ∀ n (k : (i : Fin n) → (β i)) (_ : q n k), ∃ a, q (n + 1) (Fin.snoc k a))

/-- For `Nat.prefixIndution`, this transforms an exists-statement in the induction step to choosing
an element. -/
noncomputable def step_of : (n : ℕ) → (k : (i : Fin n) → (β i)) → (hn : q n k) →
    { a : β n // q (n + 1) (Fin.snoc k a) } :=
  fun n k hn ↦ ⟨(step' n k hn).choose, (step' n k hn).choose_spec⟩

/-- This version is noncomputable since it relies on an `∃`-statement -/
noncomputable def Nat.prefixInduction' (n : Nat) : β n :=
  (Nat.prefixInduction.aux q step0 (fun n k hn ↦ step_of q step' n k hn) (n+1)).1 (Fin.last n)

theorem Nat.prefixInduction'_spec (n : Nat) : q n (Nat.prefixInduction' q step0 step' ·) := by
  apply prefixInduction_spec

end PrefixInduction

section Union

/- For a reference of `union.isCompactSystem`, see Pfanzagl, Pierlo.
Compact Systems of Sets. Springer, 1966, Lemma 1.4. -/

namespace IsCompactSystem

/-- `q n K` is the joint property that `∀ (k : Fin n), K k ∈ L k` and
`∀ N, (⋂ (j : Fin n), K j) ∩ (⋂ (k < N), ⋃₀ ↑(L (n + k))) ≠ ∅`.` holds. -/
def q (L : ℕ → Finset (Set α))
  : ∀ n, (K : (k : Fin n) → (L k)) → Prop := fun n K ↦
  (∀ N, ((⋂ j, K j) ∩ (⋂ (k < N), ⋃₀ SetLike.coe (L (n + k)))).Nonempty)

lemma q_iff_iInter (L : ℕ → Finset (Set α)) (n : ℕ) (K : (k : Fin n) → (L k)) :
    q L n K ↔ (∀ (N : ℕ), ((⋂ (j : ℕ) (hj : j < n), K ⟨j, hj⟩) ∩ (⋂ (k < N),
    ⋃₀ SetLike.coe (L (n + k)))).Nonempty) := by
  simp only [q]
  refine ⟨fun h N ↦ ?_, fun h N ↦ ?_⟩ <;>
  specialize h N <;>
  rw [Set.inter_nonempty_iff_exists_left] at h ⊢ <;>
  obtain ⟨x, ⟨hx1, hx2⟩⟩ := h <;>
  refine ⟨x, ⟨?_, hx2⟩⟩ <;>
  simp only [mem_iInter] at hx1 ⊢
  · exact fun i hi ↦ hx1 ⟨i, hi⟩
  · exact fun i ↦ hx1 i.val i.prop

lemma q_iff_iInter' (L : ℕ → Finset (Set α)) (n : ℕ) (K : (k : Fin n) → (L k)) (y : L n) :
    q L (n + 1) (Fin.snoc K y) ↔ (∀ (N : ℕ), ((⋂ (j : ℕ) (hj : j < n), K ⟨j, hj⟩) ∩ y.val ∩
    (⋂ (k < N), ⋃₀ SetLike.coe (L (n + k)))).Nonempty) := by
  simp only [q]
  refine ⟨fun h N ↦ ?_, fun h N ↦ ?_⟩
  · specialize h N
    rw [Set.inter_nonempty_iff_exists_left] at h ⊢
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h
    use x
    simp only [mem_iInter, mem_sUnion, SetLike.mem_coe, mem_inter_iff] at hx1 hx2 ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      specialize hx1 ⟨i, le_trans hi (le_succ n)⟩
      simp only [Fin.snoc, hi, ↓reduceDIte, Fin.castLT_mk, Fin.castSucc_mk, cast_eq] at hx1
      exact hx1
    · specialize hx1 ⟨n, Nat.lt_add_one n⟩
      simp only [Fin.snoc, lt_self_iff_false, ↓reduceDIte, Fin.val_last, cast_eq] at hx1
      exact hx1
    · intro i hi
      by_cases h : i = 0
      · specialize hx1 ⟨n, Nat.lt_add_one n⟩
        simp only [Fin.snoc, lt_self_iff_false, ↓reduceDIte, Fin.val_last, cast_eq] at hx1
        simp only [h, add_zero]
        refine ⟨y, y.prop, hx1⟩
      · obtain ⟨j, hj⟩ := exists_add_one_eq.mpr (zero_lt_of_ne_zero h)
        have hj' : j < N := by
          rw [← hj] at hi
          exact lt_of_succ_lt hi
        specialize hx2 j hj'
        rw [add_comm] at hj
        rw [add_assoc, hj] at hx2
        exact hx2
  · specialize h (N + 1)
    rw [Set.inter_nonempty_iff_exists_left] at h ⊢
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h
    use x
    simp only [mem_inter_iff, mem_iInter, mem_sUnion, SetLike.mem_coe] at hx1 hx2 ⊢
    refine ⟨?_, ?_⟩
    · intro i
      simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, Fin.val_last]
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, cast_eq]
        exact hx1.2
      · simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceDIte]
        exact hx1.1 i.val i.prop
    · intro i hi
      specialize hx2 (i + 1) (Nat.add_lt_add_right hi 1)
      rw [add_assoc, add_comm 1 i]
      exact hx2

lemma step0 {L : ℕ → Finset (Set α)}
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ SetLike.coe (L k)).Nonempty) :
    q L 0 (Fin.elim0' (α := fun n ↦ {a : Set α // a ∈ L n})) := by
  intro N
  simp only [iInter_of_empty, zero_add, univ_inter]
  exact hL N

lemma inter_sUnion_eq_empty (s : Set α) (L : Set (Set α)) :
    (∀ a ∈ L, s ∩ a = ∅) ↔ s ∩ ⋃₀ L = ∅ := by
  simp_rw [← disjoint_iff_inter_eq_empty]
  exact Iff.symm disjoint_sUnion_right

lemma step' {L : ℕ → Finset (Set α)}
    : ∀ n (K : (k : Fin n) → L k), (q L n K) → ∃ a, q L (n + 1) (Fin.snoc K a) := by
  intro n K hK
  simp_rw [q_iff_iInter] at hK
  simp_rw [q_iff_iInter'] at ⊢
  by_contra! h
  choose b hb using h
  classical
  let b' := fun x ↦ dite (x ∈ (L n)) (fun c ↦ b ⟨x, c⟩) (fun _ ↦ 0)
  have hs : (SetLike.coe (L n)).Nonempty := by
    specialize hK 1
    rw [Set.nonempty_def] at hK ⊢
    simp only [lt_one_iff, iInter_iInter_eq_left, add_zero, mem_inter_iff, mem_iInter, mem_sUnion,
      Finset.mem_coe] at hK ⊢
    obtain ⟨x, ⟨hx1, ⟨t, ⟨ht1, ht2⟩⟩⟩⟩ := hK
    use t
  obtain ⟨K0Max, ⟨hK0₁, hK0₂⟩⟩ := Finset.exists_max_image (L (Fin.last n)) b' hs
  simp_rw [Set.nonempty_iff_ne_empty] at hK
  apply hK (b' K0Max + 1)
  have h₂ (a : L n) : ⋂ k < b' K0Max, ⋃₀ (L (n + k)) ⊆ ⋂ k, ⋂ (_ : k < b a),
      ⋃₀ SetLike.coe (L (n + k)) := by
    intro x hx
    simp only [mem_iInter, mem_sUnion, SetLike.mem_coe] at hx ⊢
    have f : b' a = b a := by
      simp [b']
    exact fun i hi ↦ hx i (lt_of_lt_of_le hi (f ▸ hK0₂ a.val a.prop))
  have h₃ : ∀ (a : { x // x ∈ L ↑(Fin.last n) }), (⋂ j, ⋂ (hj : j < n), ↑(K ⟨j, hj⟩)) ∩ ↑a ∩
      ⋂ k, ⋂ (_ : k < b' K0Max), ⋃₀ SetLike.coe (L (n + k)) = ∅ := by
    intro a
    rw [← subset_empty_iff, ← hb a]
    apply inter_subset_inter (fun ⦃a⦄ a ↦ a) (h₂ a)
  simp_rw [inter_comm, inter_assoc] at h₃
  simp_rw [← disjoint_iff_inter_eq_empty] at h₃ ⊢
  simp only [Fin.val_last, Subtype.forall] at h₃
  have h₃'' := disjoint_iff_inter_eq_empty.mp (disjoint_sUnion_left.mpr h₃)
  rw [inter_comm] at h₃''
  rw [inter_assoc, ← disjoint_iff_inter_eq_empty] at h₃''
  apply disjoint_of_subset (fun ⦃a⦄ a ↦ a) _ h₃''
  simp only [subset_inter_iff, subset_iInter_iff]
  refine ⟨fun i hi x hx ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [mem_iInter, mem_sUnion, SetLike.mem_coe] at hx ⊢
    obtain ⟨t, ht⟩ := hx i (lt_trans hi (Nat.lt_add_one _))
    use t
  · simp only [mem_iInter, mem_sUnion, SetLike.mem_coe] at hx ⊢
    obtain ⟨t, ht⟩ := hx 0 (zero_lt_succ _)
    simp only [add_zero] at ht
    use t

/-- For `L : ℕ → Finset (Set α)` such that `L n ⊆ K` and
`h : ∀ N, ⋂ k < N, ⋃₀ L k ≠ ∅`, `mem_of_union h n` is some `K : ℕ → Set α` such that `K n ∈ L n`
for all `n` (this is `prop₀`) and `∀ N, ⋂ (j < n, K j) ∩ ⋂ (k < N), (⋃₀ L (n + k)) ≠ ∅`
(this is `prop₁`.) -/
noncomputable def mem_of_union (L : ℕ → Finset (Set α))
  (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ SetLike.coe (L k)).Nonempty) : (k : ℕ) → L k :=
  Nat.prefixInduction' (q L) (step0 hL) (step')

theorem mem_of_union.spec (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ SetLike.coe (L k)).Nonempty) (n : ℕ) :
    (∀ N, ((⋂ (j : Fin n),
      (mem_of_union L hL) j) ∩ (⋂ (k < N), ⋃₀ SetLike.coe (L (n + k)))).Nonempty) :=
  Nat.prefixInduction'_spec (β := fun n ↦ {a // a ∈ L n}) (q L) (step0 hL) (step') n

lemma sInter_memOfUnion_nonempty (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ SetLike.coe (L k)).Nonempty) (n : ℕ) :
    (⋂ (j : Fin n), (mem_of_union L hL j).val).Nonempty := by
  have h := mem_of_union.spec L hL n 0
  simp only [not_lt_zero, iInter_of_empty, iInter_univ, inter_univ] at h
  exact h

lemma sInter_memOfUnion_isSubset (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k < N, ⋃₀ SetLike.coe (L k)).Nonempty) :
    (⋂ j, (mem_of_union L hL j)) ⊆ ⋂ k, (⋃₀ SetLike.coe (L k)) := by
  exact iInter_mono <| fun n ↦
  subset_sUnion_of_subset (↑(L n)) (mem_of_union L hL n).val (fun ⦃a⦄ a ↦ a)
    (mem_of_union L hL n).prop

/-- Finite unions of sets in a compact system. -/
def union (S : Set (Set α)) : Set (Set α) :=
  (sUnion '' ({ L : Set (Set α) | L.Finite ∧ (L ⊆ S)}))

lemma union.mem_iff (s : Set α) : s ∈ union S ↔ ∃ L : Finset (Set α), s = ⋃₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_setOf_eq] at hL
    let L' := (hL.1.1).toFinset
    use L'
    rw [← hL.2, Finite.coe_toFinset]
    refine ⟨rfl, fun K hK ↦ ?_⟩
    apply hL.1.2 hK
  · obtain ⟨L, hL⟩ := h
    use L
    simp only [mem_setOf_eq, Finset.finite_toSet, true_and]
    refine ⟨hL.2, hL.1.symm⟩

/- If `IsCompactSystem S`, the set of finite unions of sets in `S` is also a compact system. -/
theorem union.isCompactSystem (S : Set (Set α)) (hS : IsCompactSystem S) :
    IsCompactSystem (union S) := by
  simp_rw [isCompactSystem_iff_nonempty_iInter_of_lt, mem_iff]
  intro C hi
  choose L' hL' using hi
  simp_rw [hL']
  intro hL
  exact Nonempty.mono (sInter_memOfUnion_isSubset L' hL)
    <| (IsCompactSystem.iff_nonempty_iInter_of_lt' S).mp hS
    (fun k ↦ (mem_of_union L' hL k).val) (fun i ↦ (hL' i).2 <| (mem_of_union L' hL i).prop)
    (fun n ↦ sInter_memOfUnion_nonempty L' hL (n + 1))

end IsCompactSystem

end Union

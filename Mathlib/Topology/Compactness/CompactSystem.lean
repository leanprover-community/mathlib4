/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Dissipate
import Mathlib.Logic.IsEmpty
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Compact systems.

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `IsCompactSystemiff_isCompactSystem_of_or_univ`: A set system is a compact
system iff inserting `univ` gives a compact system.
* `IsClosedCompact.isCompactSystem`: The set of closed and compact sets is a compact system.
* `IsClosedCompact.isCompactSystem_of_T2Space`: In a `T2Space α`, the set of compact sets
  is a compact system in a `T2Space`.
* `IsCompactSystem.closedCompactSquareCylinders`: Closed and compact square cylinders form a
  compact system.
* `IsCompactSystem.closedCompactSquareCylinders`: Closed and compact square cylinders form a
  compact system.
-/

open Set Nat MeasureTheory

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (p : Set α → Prop) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, p (C i)) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

/-- In a compact system, given a countable family with empty intersection, we choose a finite
subfamily with empty intersection. -/
noncomputable
def finite_of_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) : ℕ :=
  Nat.find (hp C hC hC_empty)

open Classical in
lemma dissipate_eq_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) :
    dissipate C (hp.finite_of_empty hC hC_empty) = ∅ := by
  apply Nat.find_spec (hp C hC hC_empty)

theorem iff_nonempty_iInter (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) := by
  refine ⟨fun h C hC hn ↦ ?_, fun h C hC ↦ ?_⟩ <;> have h2 := not_imp_not.mpr <| h C hC
  · push_neg at h2
    exact h2 hn
  · push_neg at h2
    exact h2

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma iff_nonempty_iInter_of_lt (p : Set α → Prop) : IsCompactSystem p ↔
    ∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ ?_, fun h C hi h' ↦ ?_⟩
  · apply h C hi
    exact fun n ↦ dissipate_eq ▸ (h' (n + 1))
  · apply h C hi
    intro n
    simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
    intro g
    apply h' n
    simp_rw [← subset_empty_iff, dissipate] at g ⊢
    apply le_trans _ g
    intro x
    rw [mem_iInter₂, mem_iInter₂]
    exact fun h i hi ↦ h i hi.le

/-- Any subset of a compact system is a compact system. -/
theorem mono {C D : (Set α) → Prop} (hD : IsCompactSystem D) (hCD : ∀ s, C s → D s) :
  IsCompactSystem C := fun s hC hs ↦ hD s (fun i ↦ hCD (s i) (hC i)) hs

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma iff_isCompactSystem_of_or_empty : IsCompactSystem p ↔
    IsCompactSystem (fun s ↦ (p s ∨ (s = ∅))) := by
  refine ⟨fun h s h' hd ↦ ?_, fun h ↦ mono h (fun s ↦ fun a ↦ Or.symm (Or.inr a))⟩
  by_cases g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact le_trans (dissipate_subset (by rfl)) g.choose_spec.le
  · push_neg at g
    have hj (i : _) : p (s i) := by
      rcases h' i with a | b
      · exact a
      · exfalso
        revert g i
        simp_rw [← Set.not_nonempty_iff_eq_empty]
        simp_rw [imp_false, not_not]
        exact fun h i ↦ h i
    exact h s hj hd

lemma of_IsEmpty (h : IsEmpty α) (p : Set α → Prop) : IsCompactSystem p :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma iff_isCompactSystem_of_or_univ : IsCompactSystem p ↔
    IsCompactSystem (fun s ↦ (p s ∨ s = univ)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ mono h (fun s ↦ fun a ↦ Or.symm (Or.inr a))⟩
  wlog ht : Nonempty α
  · rw [not_nonempty_iff] at ht
    apply of_IsEmpty ht
  · rw [iff_nonempty_iInter] at h ⊢
    intro s h' hd
    classical
    by_cases h₀ : ∀ n, ¬p (s n)
    · simp only [h₀, false_or] at h'
      simp_rw [h', iInter_univ, Set.univ_nonempty]
    · push_neg at h₀
      let n := Nat.find h₀
      let s' := fun i ↦ if p (s i) then s i else s n
      have h₁ : ∀ i, p (s' i) := by
        intro i
        by_cases h₁ : p (s i)
        · simp only [h₁, ↓reduceIte, s']
        · simp only [h₁, ↓reduceIte, Nat.find_spec h₀, s', n]
      have h₃ : ∀ i, (p (s i) → s' i = s i) := fun i h ↦ if_pos h
      have h₄ : ∀ i, (¬p (s i) → s' i = s n) := fun i h ↦ if_neg h
      have h₂ : ⋂ i, s i = ⋂ i, s' i := by
        simp only [s'] at *
        ext x
        simp only [mem_iInter]
        refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
        · by_cases h' : p (s i) <;> simp only [h', ↓reduceIte, h, n]
        · specialize h' i
          specialize h i
          rcases h' with a | b
          · simp only [a, ↓reduceIte] at h
            exact h
          · simp only [b, Set.mem_univ]
      apply h₂ ▸ h s' h₁
      by_contra! a
      obtain ⟨j, hj⟩ := a
      have h₂ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v:= by
        ext x
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> simp only [dissipate_def, mem_iInter] at h ⊢ <;>
          intro i hi
        · by_cases h₅ : p (s i)
          · exact (h₃ i h₅) ▸ h i hi
          · exact (h₄ i h₅) ▸ h n hv
        · by_cases h₅ : p (s i)
          · exact (h₃ i h₅) ▸ h i hi
          · have h₆ : s i = univ := by
              specialize h' i
              simp only [h₅, false_or] at h'
              exact h'
            simp only [h₆, Set.mem_univ]
      have h₇ : dissipate s' (max j n) = ∅ := by
        rw [← subset_empty_iff] at hj ⊢
        exact le_trans (antitone_dissipate (Nat.le_max_left j n)) hj
      specialize h₂ (max j n) (Nat.le_max_right j n)
      specialize hd (max j n)
      rw [h₂, Set.nonempty_iff_ne_empty, h₇] at hd
      exact hd rfl

theorem iff_directed (hpi : IsPiSystem p) :
    IsCompactSystem p ↔
    ∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
      ⋂ i, C i = ∅ → ∃ (n : ℕ), C n = ∅ := by
  rw [iff_isCompactSystem_of_or_empty]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [exists_dissipate_eq_empty_iff_of_directed C hdi]
    apply h C
    exact fun i ↦ Or.inl (hi i)
  · have hpi' : IsPiSystem (fun s ↦ p s ∨ s = ∅) := by
      intro a ha b hb hab
      rcases ha with ha₁ | ha₂
      · rcases hb with hb₁ | hb₂
        · left
          exact hpi a ha₁ b hb₁ hab
        · right
          exact hb₂ ▸ (Set.inter_empty a)
      · simp only [ha₂, Set.empty_inter]
        right
        rfl
    rw [← biInter_le_eq_iInter] at h2
    obtain h' := h (dissipate C) directed_dissipate
    have h₀ : (∀ (n : ℕ), p (dissipate C n) ∨ dissipate C n = ∅) → ⋂ n, dissipate C n = ∅ →
      ∃ n, dissipate C n = ∅ := by
      intro h₀ h₁
      by_cases f : ∀ n, p (dissipate C n)
      · apply h' f h₁
      · push_neg at f
        obtain ⟨n, hn⟩ := f
        use n
        specialize h₀ n
        simp_all only [false_or]
    obtain h'' := IsPiSystem.dissipate_mem hpi' h1
    have h₁ :  ∀ (n : ℕ), p (dissipate C n) ∨ dissipate C n = ∅ := by
      intro n
      by_cases g : (dissipate C n).Nonempty
      · exact h'' n g
      · right
        exact Set.not_nonempty_iff_eq_empty.mp g
    apply h₀ h₁ h2

theorem iff_directed' (hpi : IsPiSystem p) :
    IsCompactSystem p ↔
    ∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
    (∀ (n : ℕ), (C n).Nonempty) → (⋂ i, C i).Nonempty  := by
  rw [IsCompactSystem.iff_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

/-- Any subset of a compact system is a compact system. -/
theorem of_supset {C D : (Set α) → Prop} (hD : IsCompactSystem D) (hCD : ∀ s, C s → D s) :
  IsCompactSystem C := fun s hC hs ↦ hD s (fun i ↦ hCD (s i) (hC i)) hs


section ClosedCompact

variable (α : Type*) [TopologicalSpace α]

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isClosedCompactOrUnivs :
    IsCompactSystem (fun s : Set α ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)) := by
  let p := fun (s : Set α) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)
  have h2 : ∀ (s t : Set α), p s → p t → p (s ∩ t) := by
    intro s t hs ht
    by_cases hs' : s = univ
    · rw [hs', univ_inter]
      exact ht
    · by_cases ht' : t = univ
      · rw [ht', inter_comm, univ_inter]
        exact hs
      · exact Or.inl <| ⟨IsCompact.inter_right (Or.resolve_right hs hs').1
        (Or.resolve_right ht ht').2, IsClosed.inter (Or.resolve_right hs hs').2
          (Or.resolve_right ht ht').2⟩
  rw [IsCompactSystem.iff_directed' h2]
  intro s hs h1 h2
  let s' := fun (i : { j : ℕ | s j ≠ univ}) ↦ s i
  have hs' : Directed (fun x1 x2 ↦ x1 ⊇ x2) s' := by
    intro a b
    obtain ⟨z, hz1, hz2⟩ := hs a.val b.val
    have hz : s z ≠ univ := fun h ↦ a.prop <| eq_univ_of_subset hz1 h
    use ⟨z, hz⟩
  have htcl : ∀ (i : { j : ℕ | s j ≠ univ}), IsClosed (s i) :=
    fun i ↦ (h1 i).2
  have htco : ∀ (i : { j : ℕ | s j ≠ univ}), IsCompact (s i) :=
    fun i ↦ (h1 i).1
  haveI f : Nonempty α := by
    apply Exists.nonempty _
    · exact fun x ↦ x ∈ s 0
    · exact h2 0
  by_cases h : Nonempty ↑{j | s j ≠ Set.univ}
  · have g :  (⋂ i, s' i).Nonempty → (⋂ i, s i).Nonempty := by
      rw [Set.nonempty_iInter, Set.nonempty_iInter]
      rintro ⟨x, hx⟩
      use x
      intro i
      by_cases g : s i ≠ univ
      · exact hx ⟨i, g⟩
      · simp only [ne_eq, not_not] at g
        rw [g]
        simp only [Set.mem_univ]
    apply g <| IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s' hs'
      (fun j ↦ h2 j) htco htcl
  · simp only [ne_eq, coe_setOf, nonempty_subtype, not_exists, not_not, s'] at h
    simp only [nonempty_iInter, s', h]
    simp only [Set.mem_univ, implies_true, exists_const, s']

/-- The set of compact and closed sets is a compact system. -/
theorem isClosedCompacts :
    IsCompactSystem (fun s : Set α ↦ IsCompact s ∧ IsClosed s) :=
  IsCompactSystem.of_supset (isClosedCompactOrUnivs α) (fun _ hs ↦ Or.inl hs)

theorem isCompacts (h : ∀ {s : Set α}, IsCompact s → IsClosed s) :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := by
  have h : (fun s : Set α ↦ IsCompact s) = (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
    ext s
    refine ⟨fun h' ↦ ⟨h', h h'⟩, fun h' ↦ h'.1⟩
  exact h ▸ (isClosedCompacts α)

/-- In a `T2Space` The set of compact sets is a compact system. -/
theorem _of_isCompact_of_T2Space [T2Space α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := (isCompacts α) (fun hs ↦ hs.isClosed)

end ClosedCompact

section Union

example (s t : Set α) (hst : s ⊆ t) (ht : Finite t) : Finite s := by
  exact Finite.Set.subset t hst

lemma l1 (p : ℕ → Prop) (hp : ∀ n, p (n+1) → p n) (hi : Infinite (p⁻¹' {True})) (n : ℕ) : p n := by
  have hp' (n : ℕ): ¬(p n) → ¬(p (n+1)) := by
    exact fun a b ↦ a (hp n b)
  by_contra h
  have hp'' (m : ℕ) : ¬(p (n + m)) := by
    induction m with
    | zero => exact (add_zero n) ▸ h
    | succ m hm => exact hp' (n+m) hm
  rw [← not_finite_iff_infinite] at hi
  apply hi
  have hf : (p ⁻¹' {True}) ⊆ {k | k ≤ n} := by
    intro x hx
    simp only [preimage_singleton_true, mem_setOf_eq] at hx
    refine mem_setOf.mpr ?_
    by_contra h
    simp only [not_le] at h
    have h' := hp'' (x - n)
    rw [add_sub_of_le h.le] at h'
    exact h' hx
  apply Finite.Set.subset {k | k ≤ n} hf

-- theorem fin (p : α → Prop) (s : Set α) (hp : p ⋃₀ s)

lemma l2 [Fintype α] (p : α → ℕ → Prop) (h : ∀ a, Finite { n | p a n }) : ∃ n, ∀ a, ¬(p a n) := by
  by_contra! h₁
  have h' : Finite (⋃ a, {n | p a n}) := by
    exact Finite.Set.finite_iUnion (fun (a : α) ↦ {n | p a n})
  obtain ⟨k, hk⟩ := Finite.exists_not_mem h'
  obtain ⟨a, ha⟩ := h₁ k
  apply hk
  simp only [mem_iUnion]
  use a
  exact ha

lemma l2a [Fintype α] (q : α → ℕ → Prop) (h₁ : ∀ (n : ℕ), ∃ (K : α), q K n) :
    ∃ (K : α), Infinite ((q K)⁻¹' {True}) := by
  by_contra! h
  simp only [preimage_singleton_true, not_infinite_iff_finite] at h
  have h' : Finite (⋃ K, { a | q K a }) := by
    apply Finite.Set.finite_iUnion fun i ↦ {a | q i a}
  have h₁' : ⋃ K, { a | q K a } = univ:= by
    rw [← Set.univ_subset_iff]
    intro n hn
    simp only [mem_iUnion, mem_setOf_eq]
    exact h₁ n
  rw [h₁'] at h'
  revert h'
  simp only [imp_false, not_finite_iff_infinite]
  exact infinite_coe_iff.mpr infinite_univ


lemma l3 [Fintype α] (q : α → ℕ → Prop) (h₁ : ∀ (n : ℕ), ∃ (K : α), q K n)
    (h₂ : ∀ (K : α) (n : ℕ), (q K (n + 1) → q K n)) : ∃ (K : α), ∀ (n : ℕ), q K n := by
  have h₃ : ∃ (K : α), Infinite ((q K)⁻¹' {True}) := l2a q h₁
  obtain ⟨K, hK⟩ := h₃
  use K
  exact l1 (q K) (h₂ K) hK

example (K : ℕ → Set α) (s : Set α) : (∀ n, (K n) ∩ s = ∅) ↔ ⋃ n, (K n) ∩ s = ∅ := by
  exact Iff.symm iUnion_eq_empty

example (K : ℕ → Set α) (s : Set α) : ⋃ n, (K n) ∩ s = (⋃ n, (K n)) ∩ s := by
  exact Eq.symm (iUnion_inter s K)

example (s t : Set α) : t ⊆ s → s ∩ t = t := by
  exact inter_eq_self_of_subset_right

example (K : ℕ → Set α) : ∀ m, ⋂ n, K n ⊆ K m := by
  apply iInter_subset

example (n : ℕ) : 0 ≤ n := by exact Nat.zero_le n

example (K : ℕ → Set α) (n : ℕ) : ⋂ (k ≤ n), K k ⊆ K 0 := by
  refine biInter_subset_of_mem (Nat.zero_le n)

example (s : Set (Set α)) : ⋃ (x : s), x = ⋃₀ s := by
  exact Eq.symm sUnion_eq_iUnion

example (n : ℕ) (s : Set α) (K : ℕ → Set α) :
    s ∩ ⋂ k, ⋂ (_ : k ≤ n + 1 ), K n ⊆ s ∩ ⋂ k, ⋂ (_ : k ≤ n), K n := by
  refine inter_subset_inter_right s ?_
  apply antitone_dissipate (le_succ n)

example (s : Set α) : s = ∅ ↔ s ⊆ ∅ := by
  exact Iff.symm subset_empty_iff

example : 0 ≤ 0 := by exact Nat.zero_le 0

example (s : ℕ → Set α) : ⋂ (j : Fin 0),  s j = univ := by
  refine iInter_eq_univ.mpr (fun ⟨i, hi⟩  ↦ ?_)
  exfalso
  exact not_succ_le_zero i hi


variable {p : Set α → Prop} (hp : IsCompactSystem p) {L : ℕ → Finset (Set α)}
  (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
  (hc : ∀ (n : ℕ), ⋂ (k : Fin (n + 1)), (⋃₀ (L k).toSet) ≠ ∅)

-- variable (p : {n : ℕ} → ((k : Fin (n + 1)) → (β k)) → Prop)

noncomputable def r {n : ℕ} (K : (k : Fin (n + 1)) → (L k)) :=
  ∀ N, ⋂ (k : Fin (n + 1)), (K k) ∩ ⋂ (k : Fin N), (⋃₀ (L (n + 1 + k)).toSet) ≠ ∅

-- variable   (h0 : ∃ x : (k : Fin 1) → (β k), p x)
-- h0 -> (get_element_zero hL hc)

lemma nonempty (k : ℕ) (hc : ∀ (N : ℕ), ⋂ (k : Fin (N + 1)), (⋃₀ (L k).toSet) ≠ ∅) :
    (L k).Nonempty := by
  by_contra! h
  simp only [Finset.not_nonempty_iff_eq_empty] at h
  have hg : ⋃₀ (L k).toSet = ∅ := by
    rw [h]
    simp only [Finset.coe_empty, sUnion_empty]
  apply (hc k)
  apply iInter_eq_empty_iff.mpr
  exact fun x ↦ ⟨k, by simp [h]⟩

example (s : Set α) (hs : s ⊆ ∅) :  s = ∅ := by
  exact subset_eq_empty hs rfl

example (x : α) (s : Set α) (hx : x ∈ s) (hs : s = ∅) : False := by
  revert hs
  change s ≠ ∅
  exact ne_of_mem_of_not_mem' hx fun a ↦ a


example (s : Set α) : (s ≠ ∅) ↔ ∃ x, x ∈ s := by
  rw [← nonempty_iff_ne_empty, nonempty_def]

lemma get_element_zero (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (N : ℕ), ⋂ (k : Fin (N + 1)), (⋃₀ (L k).toSet) ≠ ∅) :
      ∃ (K : (k : Fin 1) → (L k)), r K := by
  have h1 : ∀ k : Fin 1, L k = L 0 := by
    intro k
    rw [Fin.val_eq_zero]
  simp [r]
  have g : ∀ (K : (L 0)), (r (fun (k : Fin 1) ↦ (h1 k) ▸ K)) ↔
    (∀ N, (K : Set α) ∩ ⋂ (k : Fin N), (⋃₀ (L (0 + 1 + k)).toSet) ≠ ∅) := by
      intro K
      simp [r]
      refine ⟨fun h N ↦ ?_, fun h N ↦ ?_⟩ <;>
      specialize h N <;> change _ ≠ ∅ at h ⊢ <;>
      rw [← nonempty_iff_ne_empty, nonempty_def] at h ⊢ <;>
      obtain ⟨x, hx⟩ := h <;> use x <;>
      simp only [mem_inter_iff, mem_iInter, mem_sUnion, Finset.mem_coe] at hx ⊢
      · exact hx 0
      · refine fun i ↦ ⟨(Fin.fin_one_eq_zero i) ▸ hx.1, hx.2⟩
  have d : ∃ (K : (L 0)), r (fun (k : Fin 1) ↦ (h1 k) ▸ K) := by
    simp_rw [g]
    by_contra! h
    simp only [zero_add, Subtype.forall] at h
    choose! b ha using h
    classical
    obtain ⟨aMax, ⟨ha1, ha2⟩⟩ := Finset.exists_max_image (L 0) b (nonempty 0 hc)
    have h' : ∀ a ∈ L 0, a ∩ ⋂ (k : Fin ((b aMax))), ⋃₀ ↑(L (1 + ↑k)) = ∅ := by
      intro a' h'
      refine subset_eq_empty (inter_subset_inter (fun ⦃a⦄ a ↦ a)
        (iInter_mono' (fun j ↦ ?_))) (ha a' h')
      use ⟨j.val, le_trans j.prop (ha2 a' h')⟩
    apply hc (b aMax)
    rw [Set.iInter_eq_empty_iff]
    intro x
    by_cases h : x ∈ ⋃₀ (L 0)
    · simp only [mem_sUnion, Finset.mem_coe] at h
      obtain ⟨t, ⟨ht1, ht2⟩⟩ := h
      specialize h' t ht1
      rw [← not_forall, ← mem_iInter]
      have d : x ∉ ⋂ (k : Fin (b aMax)), ⋃₀ ↑(L (1 + ↑k)) := by
        intro e
        obtain v : x ∈ t ∩ ⋂ (k : Fin (b aMax)), ⋃₀ ↑(L (1 + ↑k)) := by
          exact (mem_inter ht2 e)
        revert h'
        change _ ≠ ∅
        exact ne_of_mem_of_not_mem' v fun a ↦ a
      intro hd
      apply d
      simp only [mem_iInter, mem_sUnion, Finset.mem_coe] at hd ⊢
      intro i
      obtain ⟨t, ⟨ht₁, ht₂⟩⟩ := hd (i + 1)
      refine ⟨t, ⟨?_, ht₂⟩⟩
      rw [add_comm]
      have r : (((i : Fin (b aMax)) + 1 : Fin ((b aMax) + 1)) : ℕ) =
          ((i : Fin (b aMax)) + 1: ℕ) := by
        simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.val_succ]
      exact r ▸ ht₁
    · exact ⟨0, h⟩
  obtain ⟨K, hK⟩ := d
  use (fun (k : Fin 1) ↦ (h1 k) ▸ K)
  exact hK

lemma element_0_has_r (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (N : ℕ), ⋂ (k : Fin (N + 1)), (⋃₀ (L k).toSet) ≠ ∅) (K : (k : Fin 1) → (L k))
    (hK : K = (get_element_zero hL hc).choose) : r K := by
  exact hK ▸ (get_element_zero hL hc).choose_spec

def join {n : ℕ} (K' : (k : Fin (n + 1)) → (L k)) (K : L (n + 1)) :
    (k : Fin (n + 2)) → (L k) := by
  let K'' (k : Fin (n + 2)) (hk : ¬ k.val < n + 1) : L k := by
    simp only [not_lt] at hk
    have h : L k = L (n + 1) := by
      congr
      exact Nat.eq_of_le_of_lt_succ hk k.prop
    exact h ▸ K
  exact fun k ↦ dite (k.val < n + 1) (fun c ↦ K' ⟨k.val, c⟩) (fun c ↦ K'' k c)


-- (h : ∀ {n : ℕ} (x : (k : Fin (n + 1)) → (β k)), p x → ∃ y : (β (n + 1)), p (joi x y))

-- h → (get_element_succ hL hd hc)

example (s : ℕ → (Set α)) (b : Set α) : ⋂ k, (s k) ∩ b = (⋂ k, (s k)) ∩ b := by
  exact Eq.symm (iInter_inter b s)

lemma get_element_succ (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (n : ℕ), ⋂ (k : Fin (n + 1)), (⋃₀ (L k).toSet) ≠ ∅) : ∀
    (n : ℕ) (K' : (k : Fin (n + 1)) → (L k)), r K' →
      ∃ (K : (L (n + 1))), r (join K' K) := by
  intro n K' hK'
  have d : ∃ (K : (L (n + 1))), r (join K' K) := by
    simp [r]
    by_contra! h
    choose! b ha using h
    classical
    obtain ⟨aMax, ⟨ha1, ha2⟩⟩ := Finset.exists_max_image (L (n + 1)) b (nonempty (n + 1) hc)
    have h' : ∀ (a : Set α) (b_1 : a ∈ L (n + 1)), ⋂ k, ↑(join K' ⟨a, b_1⟩ k) ∩
        ⋂ (k : Fin (b aMax)), ⋃₀ (L (n + 1 + 1 + ↑k) : Set (Set α)) = ∅ := by
      intro a' h'
      refine subset_eq_empty ?_ (ha a' h')
      rw [← iInter_inter, ← iInter_inter]
      apply (inter_subset_inter (fun ⦃a⦄ a ↦ a)  (iInter_mono' (fun j ↦ ?_)))
      use ⟨j.val, le_trans j.prop (ha2 a' h')⟩
    apply hc (b aMax)
    rw [Set.iInter_eq_empty_iff]
    intro x
    by_cases h : x ∈ ⋃₀ (L (n + 1))
    · simp only [mem_sUnion, Finset.mem_coe] at h
      obtain ⟨t, ⟨ht1, ht2⟩⟩ := h
      specialize h' t ht1
      rw [← not_forall, ← mem_iInter]
      have d : x ∉ ⋂ (k : Fin (b aMax)), ⋃₀ ↑(L (1 + ↑k)) := by
        intro e
        obtain v := (mem_inter ht2 e)
        revert h'
        change _ ≠ ∅
        sorry
        -- exact ne_of_mem_of_not_mem' v fun a ↦ a
      intro hd
      apply d
      simp only [mem_iInter, mem_sUnion, Finset.mem_coe] at hd ⊢
      intro i
      obtain ⟨t, ⟨ht₁, ht₂⟩⟩ := hd (i + 1)
      refine ⟨t, ⟨?_, ht₂⟩⟩
      rw [add_comm]
      have r : (((i : Fin (b aMax)) + 1 : Fin ((b aMax) + 1)) : ℕ) =
          ((i : Fin (b aMax)) + 1: ℕ) := by
        simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.val_succ]
      exact r ▸ ht₁
    · use n + 1
      have d : n + 1 = ((((n : ℕ) : Fin (b aMax + 1)) + 1 : Fin (b aMax + 1)) : ℕ) := by
        norm_cast
        sorry
      rw [d] at h
      exact h


  obtain ⟨K, hK⟩ := d
  use K



noncomputable def main : (n : ℕ) → ((K' : (k : Fin (n + 1)) → (L k)) ×' (r K'))
  | 0 => ⟨(get_element_zero hL hc).choose, (get_element_zero hL hc).choose_spec⟩
  | n + 1 => by
      let g := ((get_element_succ hL hc) n (main n).1 (main n).2)
      exact ⟨join (main n).1 g.choose, g.choose_spec⟩

noncomputable def main' : (j : ℕ) → (L j) := by
  have hj (j : ℕ) : j = ((j : Fin (j + 1)) : ℕ) := by
    simp only [Fin.natCast_eq_last, Fin.val_last]
  exact fun j ↦ (hj j).symm ▸ (main hL hc j).1 j

lemma has_r (n : ℕ) : r (main hL hc n).1 := by
  exact (main hL hc n).2

lemma has_r' (n : ℕ) : r (main' hL hc n).1 := by
  exact (main hL hc n).2



theorem main' (p : Set α → Prop) (hp : IsCompactSystem p) (L : ℕ → Finset (Set α))
    (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (n : ℕ), ⋂ (k : Fin (n + 1)), (⋃₀ (L k).toSet) ≠ ∅) :
    ∃ (K : (j : ℕ) → (L j)), (∀ n N, ⋂ (j : Fin (n + 1)), (K j) ∩ ⋂ (k < N),
      ⋃₀ (L (n + 1 + k)).toSet ≠ ∅) := by
  use (main' hL hc n).1

  exact has_r hL hc
  sorry

def ack : Nat → Nat → Nat
  | 0,      n      => n + 1
  | m + 1, 0      => ack m 1
  | m + 1, n + 1  => ack m (ack (m + 1) n)


def myMax (a b : Nat) : Nat :=
  if a < b then myMax b a else a









  have hq (K : (L 0)) (n : ℕ) : q K n := by
    specialize hc 0
    simp? at hc
    sorry
  have h'' (K : L 0) := Finite.exists_infinite_fiber (fun n ↦ q K n)
  have h''' : ∃ (K : L 0), Infinite ((fun n ↦ q K n) ⁻¹' {True}) := by
    by_contra! h
    simp only [preimage_singleton_true, coe_setOf, not_infinite_iff_finite, Subtype.forall] at h



    -- apply hc 0
    simp only [nonpos_iff_eq_zero, iInter_iInter_eq_left, sUnion_eq_empty, Finset.mem_coe]

    sorry

  have h : ∃ (K : L 0), ∀ n, q K n:= by
    by_contra h'
    push_neg at h'

      sorry

    simp_rw [q] at h'
  -- Finite.exists_infinite_fiber
    sorry
  sorry
theorem main (p : Set α → Prop) (hp : IsCompactSystem p) (L : ℕ → Finset (Set α))
    (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (n : ℕ), ⋂ (k ≤ n), (⋃₀ (L k).toSet) ≠ ∅) :
    ∃ (K : (n : ℕ) → (L n)), (∀ N k, ⋂ (j : ℕ) (hj : j ≤ N), (K j) ∩ ⋂ (j ≤ k),
      ⋃₀ (L (N + j + 1)).toSet ≠ ∅) := by
  -- `q K n` is true, if `K ∩ ⋂ (k ≤ n), ⋃₀ (L k) ≠ ∅`
  let q : (L 0) → ℕ → Prop := fun (K : (L 0)) n ↦ (K : Set α) ∩ ⋂ (k ≤ n), (⋃₀ (L k).toSet) ≠ ∅

  have hq (n : ℕ) : ∃ (K : (L 0)), q K n := by
    by_contra! h
    push_neg at h
    rw [← iUnion_eq_empty] at h
    have f : ⋃ (i : { x // x ∈ L 0 }), ↑i ∩ ⋂ k, ⋂ (_ : k ≤ n), ⋃₀ ↑(L k) = (⋃ (i : { x // x ∈ L 0 }), ↑i) ∩ ⋂ k, ⋂ (_ : k ≤ n), ⋃₀ (L k).toSet := by
      rw [iUnion_inter]
    rw [f] at h
    have g : (⋃ (i : { x // x ∈ L 0 }), ↑i) ∩ ⋂ k, ⋂ (_ : k ≤ n), ⋃₀ (L k).toSet = ⋂ k, ⋂ (_ : k ≤ n), ⋃₀ (L k).toSet := by
      apply inter_eq_self_of_subset_right
      have f : ⋃ (i : { x // x ∈ (L 0) }), ↑i = ⋃₀ (L 0).toSet := by
        rw [biUnion_eq_iUnion]
        simp only [Finset.coe_sort_coe]
        sorry
      rw [f]
      refine biInter_subset_of_mem (Nat.zero_le n)
    rw [g] at h
    apply (hc n) h


    sorry


    sorry
  have h'' (K : L 0) := Finite.exists_infinite_fiber (fun n ↦ q K n)
  have h''' : ∃ (K : L 0), Infinite ((fun n ↦ q K n) ⁻¹' {True}) := by
    by_contra! h
    simp only [preimage_singleton_true, coe_setOf, not_infinite_iff_finite, Subtype.forall] at h




  let q' : (n : ℕ) → ((j : ℕ) → (hj : j ≤ n) → (L j)) → ℕ → Prop :=
    fun n K N ↦ ⋂ (j : ℕ) (hj : j ≤ n), (K j hj : Set α) ∩ ⋂ (k ≤ N), (⋃₀ (L (n + k + 1)).toSet) ≠ ∅
  have hq'' : q' = fun n K N ↦ ⋂ (j : ℕ) (hj : j ≤ n), (K j hj : Set α) ∩ ⋂ (k ≤ N),
      (⋃₀ (L (n + k + 1)).toSet) ≠ ∅ := by
    rfl
  have hq' (n : ℕ) (K : ((j : ℕ) → (hj : j ≤ n) → (L j))) (N : ℕ) : (q' n K N) ↔
      (⋂ (j : ℕ) (hj : j ≤ n), (K j hj : Set α) ∩ ⋂ (k ≤ N), (⋃₀ (L (n + k + 1)).toSet) ≠ ∅) := by
    rfl
  simp_rw [← hq']

  have h₀ (n : ℕ) : ∃ (K : ((j : ℕ) → (hj : j ≤ n) → (L j))), ∀ N, q' N (fun j hj ↦ K j) k := by sorry



  sorry





    sorry

  rfl



  have hq (K : (L 0)) (n : ℕ) : q K n := by
    specialize hc 0
    simp? at hc
    sorry
  have h'' (K : L 0) := Finite.exists_infinite_fiber (fun n ↦ q K n)
  have h''' : ∃ (K : L 0), Infinite ((fun n ↦ q K n) ⁻¹' {True}) := by
    by_contra! h
    simp only [preimage_singleton_true, coe_setOf, not_infinite_iff_finite, Subtype.forall] at h



    -- apply hc 0
    simp only [nonpos_iff_eq_zero, iInter_iInter_eq_left, sUnion_eq_empty, Finset.mem_coe]

    sorry

  have h : ∃ (K : L 0), ∀ n, q K n:= by
    by_contra h'
    push_neg at h'

      sorry

    simp_rw [q] at h'
  -- Finite.exists_infinite_fiber
    sorry
  sorry

open Classical in
example (x : α) (H : Finset (Set α)) : x ∉ ⋃₀ ↑H ↔ ∀ h ∈ H, x ∉ h := by
  simp only [mem_sUnion, Finset.mem_coe, not_exists, not_and]

theorem union (h : IsCompactSystem p) : IsCompactSystem (fun s ↦ ∃ (D : Finset (Set (α))),
    (∀ d ∈ D, p d) ∧ s = ⋃₀ (D : Set (Set α))) := by
  intro q hq h_empty
  simp only at hq
  choose f hf1 hf2 using hq
  simp_rw [Dissipate, hf2] at h_empty ⊢
  -- simp_rw [sUnion_eq_iUnion, iInter_iUnion_distr] at h_empty
  simp_rw [iInter_eq_empty_iff, mem_sUnion, Finset.mem_coe, not_exists, not_and] at h_empty ⊢
  by_contra h
  revert h_empty
  simp only [imp_false]
  push_neg at h ⊢

  simp only [nonempty_iInter, mem_sUnion, Finset.mem_coe] at h ⊢
  simp_rw [Dissipate, nonempty_iInter] at h



  apply exists_mem_of_nonempty






  sorry

end Union

end IsCompactSystem

section pi

variable {ι : Type*}  {α : ι → Type*}

theorem iInter_pi_empty_iff {β : Type*} (s : β → Set ι) (t : β → (i : ι) → Set (α i)) :
   ( ⋂ b, ((s b).pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β) (_: i ∈ s b), (t b i) = ∅):= by
  rw [iInter_eq_empty_iff, not_iff_not.symm]
  push_neg
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have ⟨x, hx⟩ := h
    simp only [nonempty_iInter]
    intro i
    refine ⟨x i, fun j ↦ ?_⟩
    rw [mem_iInter]
    intro hi
    simp_rw [mem_pi] at hx
    exact hx j i hi
  · simp only [nonempty_iInter, mem_iInter] at h
    choose x hx using h
    use x
    simp_rw [mem_pi]
    intro i
    intro j hj
    exact hx j i hj

theorem iInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) :
   ( ⋂ b, (univ.pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β), (t b i) = ∅):= by
  rw [iInter_pi_empty_iff]
  simp only [mem_univ, iInter_true]

theorem biInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) (p : β → Prop):
   ( ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) = ∅) ↔
      (∃ i : ι, ⋂ (b : β), ⋂ (_ : p b), (t b i) = ∅) := by
  have h :  ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) =
      ⋂ (b : { (b' : β) | p b' }), (univ.pi (t b.val)) := by
    exact biInter_eq_iInter p fun x h ↦ univ.pi (t x)
  have h' (i : ι) :  ⋂ (b : β), ⋂ (_ : p b), t b i =  ⋂ (b : { (b' : β) | p b' }), t b.val i := by
    exact biInter_eq_iInter p fun x h ↦ t x i
  simp_rw [h, h', iInter_univ_pi_empty_iff]

theorem IsCompactSystem.pi (C : (i : ι) → Set (Set (α i))) (hC : ∀ i, IsCompactSystem (C i)) :
    IsCompactSystem (univ.pi '' univ.pi C) := by
  intro S hS h_empty
  change ∀ i, S i ∈ univ.pi '' univ.pi C at hS
  simp only [mem_image, mem_pi, mem_univ, forall_const] at hS
  choose x hx1 hx2 using hS
  simp_rw [← hx2] at h_empty ⊢
  simp_rw [iInter_univ_pi_empty_iff x] at h_empty
  obtain ⟨i, hi⟩ := h_empty
  let y := (fun b ↦ x b i)
  have hy (b : ℕ) : y b ∈ C i := by
    simp only [y]
    exact hx1 b i
  have ⟨n, hn⟩ := (hC i) y hy hi
  use n
  simp_rw [Dissipate, ← hx2] at hn ⊢
  rw [biInter_univ_pi_empty_iff x]
  use i

end pi

section ClosedCompactSquareCylinders

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, TopologicalSpace (α i)]

variable (α)
/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both,
closed and compact, for all `i ∈ s`. -/
def closedCompactSquareCylinders : Set (Set (Π i, α i)) :=
  ⋃ (s) (t) (_ : ∀ i ∈ s, IsClosed (t i)) (_ : ∀ i ∈ s, IsCompact (t i)), {squareCylinder s t}

variable {α}
@[simp]
theorem mem_closedCompactSquareCylinders (S : Set (Π i, α i)) :
    S ∈ closedCompactSquareCylinders α
      ↔ ∃ (s t : _) (_ : ∀ i ∈ s, IsClosed (t i)) (_ : ∀ i ∈ s, IsCompact (t i)),
        S = squareCylinder s t := by
  simp_rw [closedCompactSquareCylinders, mem_iUnion, mem_singleton_iff]

variable {S : Set (Π i, α i)}

/-- Given a closed compact cylinder, choose a finset of variables such that it only depends on
these variables. -/
noncomputable def closedCompactSquareCylinders.finset (hS : S ∈ closedCompactSquareCylinders α) :
    Finset ι :=
  ((mem_closedCompactSquareCylinders S).mp hS).choose

/-- Given a closed compact square cylinder `S`, choose a dependent function `(i : ι) → Set (α i)`
of which it is a lift. -/
def closedCompactSquareCylinders.func (hS : S ∈ closedCompactSquareCylinders α) :
    (i : ι) → Set (α i) :=
  ((mem_closedCompactSquareCylinders S).mp hS).choose_spec.choose

theorem closedCompactSquareCylinders.isClosed (hS : S ∈ closedCompactSquareCylinders α) :
    ∀ i ∈ closedCompactSquareCylinders.finset hS,
      IsClosed (closedCompactSquareCylinders.func hS i) :=
  ((mem_closedCompactSquareCylinders S).mp hS).choose_spec.choose_spec.choose

theorem closedCompactSquareCylinders.isCompact (hS : S ∈ closedCompactSquareCylinders α) :
    ∀ i ∈ closedCompactSquareCylinders.finset hS,
      IsCompact (closedCompactSquareCylinders.func hS i) :=
  ((mem_closedCompactSquareCylinders S).mp hS).choose_spec.choose_spec.choose_spec.choose

theorem closedCompactSquareCylinders.eq_squareCylinder (hS : S ∈ closedCompactSquareCylinders α) :
    S = squareCylinder (closedCompactSquareCylinders.finset hS)
      (closedCompactSquareCylinders.func hS) :=
  ((mem_closedCompactSquareCylinders S).mp hS).choose_spec.choose_spec.choose_spec.choose_spec

theorem squareCylinder_mem_closedCompactSquareCylinders (s : Finset ι) (t : (i : ι) → Set (α i))
    (hS_closed : ∀ i ∈ s, IsClosed (t i)) (hS_compact : ∀ i ∈ s, IsCompact (t i)) :
    squareCylinder s t ∈ closedCompactSquareCylinders α := by
  rw [mem_closedCompactSquareCylinders]
  exact ⟨s, t, hS_closed, hS_compact, rfl⟩

/-
theorem mem_cylinder_of_mem_closedCompactSquareCylinders [∀ i, MeasurableSpace (α i)]
    [∀ i, SecondCountableTopology (α i)] [∀ i, OpensMeasurableSpace (α i)]
    (hS : S ∈ closedCompactSquareCylinders α) :
    S ∈ measurableCylinders α := by
  rw [mem_measurableSquareCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht
-/

theorem IsCompactSystem.CompactClosedOrUniv_pi :
  IsCompactSystem (univ.pi '' univ.pi
    (fun (i : ι) ↦ (fun (s : Set (α i)) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)))) := by
  apply IsCompactSystem.pi
    (fun (i : ι) ↦ (fun (s : Set (α i)) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)))
      <| fun i ↦ IsCompactSystem.isClosedCompactOrUnivs (α i)

/-- In `closedCompactSquareCylinders α`, the set of dependent variables is a finset,
  but not necessarily in `univ.pi '' univ.pi _`, where `_` are closed compact set, or `univ`. -/
theorem closedCompactSquareCylinders_supset (S : _) :
    S ∈ closedCompactSquareCylinders α → S ∈ (univ.pi '' univ.pi
    (fun (i : ι) ↦ (fun (s : Set (α i)) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ))))  := by
  classical
  intro hS
  simp_rw [mem_closedCompactSquareCylinders, squareCylinder] at hS
  simp only [mem_image, mem_pi, mem_univ, forall_const]
  obtain ⟨s, t, h_cl, h_co, h_pi⟩ := hS
  let t' := fun (i : ι) ↦ if (i ∈ s) then (t i) else univ
  refine ⟨t', ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, t']
      exact Or.inl ⟨h_co i hi, h_cl i hi⟩
    · simp only [hi, ↓reduceIte, t']
      apply Or.inr rfl
  · change (pi univ fun i => if i ∈ (s : Set ι) then t i else univ) = S
    rw [h_pi, univ_pi_ite s t]

/-- Closed and compact square cylinders form a compact system. -/
theorem IsCompactSystem.closedCompactSquareCylinders :
    IsCompactSystem (closedCompactSquareCylinders α) :=
  IsCompactSystem.of_supset IsCompactSystem.CompactClosedOrUniv_pi
    closedCompactSquareCylinders_supset

end ClosedCompactSquareCylinders


variable {β : (n : ℕ) → Type*}

variable (p : {n : ℕ} → ((k : Fin (n + 1)) → (β k)) → Prop)

def joi {n : ℕ} (x : (k : Fin (n + 1)) → (β k)) (y : β (n + 1)) : (k : Fin (n + 2)) → (β k) := by
  let z (k : Fin (n + 2)) (hk : ¬ k.val < n + 1) : β k := by
    simp only [not_lt] at hk
    have h : β k = β (n + 1) := by
      congr
      exact Nat.eq_of_le_of_lt_succ hk k.prop
    exact h ▸ y
  exact fun k ↦ dite (k.val < n + 1) (fun c ↦ x ⟨k.val, c⟩) (z k)

variable   (h0 : ∃ x : (k : Fin 1) → (β k), p x)
  (h : ∀ (n : ℕ) (x : (k : Fin (n + 1)) → (β k)), p x → ∃ y : (β (n + 1)),
    p (joi x y))


noncomputable def m : (n : ℕ) → ((x : (k : Fin (n + 1)) → (β k)) ×' (p x))
  | 0 => ⟨h0.choose, h0.choose_spec⟩
  | n + 1 => by
      let g := (h n (m n).1 (m n).2)
      exact ⟨joi (m n).1 g.choose, g.choose_spec⟩

example (n : ℕ) : p (m p h0 h n).1 := by
  exact (m p h0 h n).2

/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber, Joachim Breitner
-/
import Mathlib.Data.Set.Dissipate
import Mathlib.Logic.IsEmpty
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems.

This file defines compact systems of sets. These are set systems `p : Set α → Prop` with the
following property: If `C : ℕ → Set α` is such that `∀ n, p (C n)` and `⋂ n, C n = ∅`, then
there is some `N : ℕ` with `⋂ n < N, C n = ∅`.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `IsCompactSystem.iff_isCompactSystem_of_or_univ`: A set system is a compact
system iff inserting `univ` gives a compact system.
* `IsClosedCompact.isCompactSystem`: The set of closed and compact sets is a compact system.
* `IsClosedCompact.isCompactSystem_of_T2Space`: In a `T2Space α`, the set of compact sets
  is a compact system in a `T2Space`.
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

open Classical in
/-- In a compact system, given a countable family with `⋂ i, C i = ∅`, we choose the smallest `n`
with `⋂ (i ≤ n), C i = ∅`. -/
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

lemma k (s : ℕ → Set α) (n : ℕ) : ⋂ (j < n), s j = ⋂ (j : Fin n), s j := by
  ext x
  simp only [mem_iInter]
  refine ⟨fun h i ↦ h i.val i.prop, fun h i hi ↦ h ⟨i, hi⟩⟩

lemma iff_nonempty_iInter_of_lt' (p : Set α → Prop) : IsCompactSystem p ↔
    ∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ n, (⋂ k : Fin n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  rw [iff_nonempty_iInter_of_lt]
  simp_rw [← k]

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

section IsCompactIsClosed

variable {α : Type*} [TopologicalSpace α]

/-- The set of compact and closed sets is a compact system. -/
theorem of_isCompact_isClosed :
    IsCompactSystem (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
  let p := fun (s : Set α) ↦ IsCompact s ∧ IsClosed s
  have h2 : IsPiSystem p := by
    intro s hs t ht _
    refine ⟨IsCompact.inter_left ht.1 hs.2, IsClosed.inter hs.2 ht.2⟩
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
  · simp only [ne_eq, coe_setOf, nonempty_subtype, not_exists, not_not] at h
    simp [h]

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem of_isCompact_isClosed_or_univ :
    IsCompactSystem (fun s : Set α ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)) := by
  rw [← iff_isCompactSystem_of_or_univ]
  exact of_isCompact_isClosed

/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem of_isCompact [T2Space α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := by
  have h : (fun s : Set α ↦ IsCompact s) = (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
    ext s
    refine ⟨fun h' ↦ ⟨h', h'.isClosed⟩, fun h ↦ h.1⟩
  exact h ▸ (of_isCompact_isClosed)

end IsCompactIsClosed

end IsCompactSystem

section PrefixInduction

/-- A version of `Fin.elim` using even more dependent types. -/
def Fin.elim0'.{u} {α : ℕ → Sort u} : (i : Fin 0) → (α i)
  | ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

variable {β : ℕ → Type*}
variable (q : ∀ n, (k : (i : Fin n) → (β i)) → Prop)
variable (step0 : q 0 Fin.elim0')
variable (step :
    ∀ n (k : (i : Fin n) → (β i)) (_ : q n k),
    { a : β n // q (n+1) (Fin.snoc k a)})

/-- In this section, we prove a general induction principle, which we need for the construction
`Nat.prefixInduction q step0 step : (k : ℕ) →  (β k)` based on some
`q : (n : ℕ) → (k : (i : Fin n) → (β i)) → Prop`. For
the inducation start, `step0 : q 0 _` always holds since `Fin 0` cannot be satisfied, and
`step : (n : ℕ) → (k : (i : Fin n) → β i) → q n k → { a : β n // q (n + 1) (Fin.snoc k a) })`
`(n : ℕ) : β n` constructs the next element satisfying `q (n + 1) _` from a proof of `q n k`
and finding the next element.

In comparisong to other induction principles, the proofs of `q n k` are needed in order to find
the next element. -/

/- An auxiliary definition for `Nat.prefixInduction`. -/
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
      simp only [Fin.coe_castSucc]
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

/-- An induction principle showing that `q : (n : ℕ) → (k : (i : Fin n) → (β i)) → Prop` holds
for all `n`. `step0` is satisfied by construction since `Fin 0` is empty.
In the induction `step`, we use that `q n k` holds for showing that `q (n + 1) (Fin.snoc k a)`
holds for some `a : β n`. This version is noncomputable since it relies on an `∃`-statement -/
noncomputable def Nat.prefixInduction' (n : Nat) : β n :=
  (Nat.prefixInduction.aux q step0 (fun n k hn ↦ step_of q step' n k hn) (n+1)).1 (Fin.last n)

theorem Nat.prefixInduction'_spec (n : Nat) : q n (Nat.prefixInduction' q step0 step' ·) := by
  apply prefixInduction_spec

end PrefixInduction

namespace IsCompactSystem

section Union

/-- `q n K` is the joint property that `∀ (k : Fin n), K k ∈ L k` and
`∀ N, (⋂ (j : Fin n), K j) ∩ (⋂ (k < N), ⋃₀ (L (n + k)).toSet) ≠ ∅`.` holds. -/
def q (L : ℕ → Finset (Set α))
  : ∀ n, (K : (k : Fin n) → (L k)) → Prop := fun n K ↦
  (∀ N, ((⋂ j, K j) ∩ (⋂ (k < N), ⋃₀ (L (n + k)).toSet)).Nonempty)

lemma q_iff_iInter (L : ℕ → Finset (Set α)) (n : ℕ) (K : (k : Fin n) → (L k)) :
    q L n K ↔ (∀ (N : ℕ), ((⋂ (j : ℕ) (hj : j < n), K ⟨j, hj⟩) ∩ (⋂ (k < N),
    ⋃₀ (L (n + k)).toSet)).Nonempty) := by
  simp [q]
  refine ⟨fun h N ↦ ?_, fun h N ↦ ?_⟩ <;>
  specialize h N <;>
  rw [Set.inter_nonempty_iff_exists_left] at h ⊢ <;>
  obtain ⟨x, ⟨hx1, hx2⟩⟩ := h <;>
  refine ⟨x, ⟨?_, hx2⟩⟩ <;>
  simp only [mem_iInter] at hx1 ⊢
  · exact fun i hi ↦ hx1 ⟨i, hi⟩
  · exact fun i ↦ hx1 i.val i.prop

example (i : ℕ) (hi : i ≠ 0) : ∃ j, j + 1 = i := by
  exact exists_add_one_eq.mpr (zero_lt_of_ne_zero hi)

lemma q_iff_iInter' (L : ℕ → Finset (Set α)) (n : ℕ) (K : (k : Fin n) → (L k)) (y : L n) :
    q L (n + 1) (Fin.snoc K y) ↔ (∀ (N : ℕ), ((⋂ (j : ℕ) (hj : j < n), K ⟨j, hj⟩) ∩ y.val ∩
    (⋂ (k < N), ⋃₀ (L (n + k)).toSet)).Nonempty) := by
  simp [q]
  refine ⟨fun h N ↦ ?_, fun h N ↦ ?_⟩
  · specialize h N
    rw [Set.inter_nonempty_iff_exists_left] at h ⊢
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h
    use x
    simp at hx1 hx2 ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      specialize hx1 ⟨i, le_trans hi (le_succ n)⟩
      simp [Fin.snoc, hi] at hx1
      exact hx1
    · specialize hx1 ⟨n, Nat.lt_add_one n⟩
      simp [Fin.snoc] at hx1
      exact hx1
    · intro i hi
      by_cases h : i = 0
      · specialize hx1 ⟨n, Nat.lt_add_one n⟩
        simp [Fin.snoc] at hx1
        simp [h]
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
    simp at hx1 hx2 ⊢
    refine ⟨?_, ?_⟩
    · intro i
      simp [Fin.snoc]
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, cast_eq]
        exact hx1.2
      · simp only [Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.castSucc_ne_last,
        not_false_eq_true, Fin.castLT_eq_castPred, Fin.castPred_castSucc]
        exact hx1.1 i.val i.prop
    · intro i hi
      specialize hx2 (i + 1) (Nat.add_lt_add_right hi 1)
      rw [add_assoc, add_comm 1 i]
      exact hx2

lemma step0 {L : ℕ → Finset (Set α)} (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ (L k).toSet).Nonempty) :
    q L 0 (Fin.elim0' (α := fun n ↦ {a : Set α // a ∈ L n})) := by
  intro N
  simp only [iInter_of_empty, zero_add, univ_inter]
  exact hL N

lemma inter_sUnion_eq_empty (s : Set α) (L : Set (Set α)) :
    (∀ a ∈ L, s ∩ a = ∅) ↔ s ∩ ⋃₀ L = ∅ := by
  simp_rw [← disjoint_iff_inter_eq_empty]
  rw [disjoint_sUnion_right]

lemma step' {L : ℕ → Finset (Set α)}
    : ∀ n (K : (k : Fin n) → L k), (q L n K) → ∃ a, q L (n + 1) (Fin.snoc K a) := by
  intro n K hK
  simp_rw [q_iff_iInter] at hK
  simp_rw [q_iff_iInter'] at ⊢
  by_contra! h
  choose b hb using h
  classical
  let b' := fun x ↦ dite (x ∈ (L n)) (fun c ↦ b ⟨x, c⟩) (fun _ ↦ 0)
  have hs : (L n).toSet.Nonempty := by
    specialize hK 1
    rw [nonempty_def] at hK ⊢
    simp only [lt_one_iff, iInter_iInter_eq_left, add_zero, mem_inter_iff, mem_iInter, mem_sUnion,
      Finset.mem_coe] at hK ⊢
    obtain ⟨x, ⟨hx1, ⟨t, ⟨ht1, ht2⟩⟩⟩⟩ := hK
    use t
  obtain ⟨K0Max, ⟨hK0₁, hK0₂⟩⟩ := Finset.exists_max_image (L (Fin.last n)) b' hs
  simp_rw [nonempty_iff_ne_empty] at hK
  apply hK (b' K0Max + 1)
  have h₂ (a : L n) : ⋂ k < b' K0Max, ⋃₀ (L (n + k)) ⊆ ⋂ k, ⋂ (_ : k < b a),
      ⋃₀ (L (n + k)).toSet := by
    intro x hx
    simp at hx ⊢
    have f : b' a = b a := by
      simp [b']
    exact fun i hi ↦ hx i (lt_of_lt_of_le hi (f ▸ hK0₂ a.val a.prop))
  have h₃ : ∀ (a : { x // x ∈ L ↑(Fin.last n) }), (⋂ j, ⋂ (hj : j < n), ↑(K ⟨j, hj⟩)) ∩ ↑a ∩
      ⋂ k, ⋂ (_ : k < b' K0Max), ⋃₀ (L (n + k)).toSet = ∅ := by
    intro a
    rw [← subset_empty_iff, ← hb a]
    apply inter_subset_inter (fun ⦃a⦄ a ↦ a) (h₂ a)
  simp_rw [inter_comm, inter_assoc] at h₃
  simp_rw [← disjoint_iff_inter_eq_empty] at h₃ ⊢
  simp at h₃
  have h₃' := disjoint_sUnion_left.mpr h₃
  rw [disjoint_iff_inter_eq_empty, inter_comm, inter_assoc, ← disjoint_iff_inter_eq_empty] at h₃'
  apply disjoint_of_subset (fun ⦃a⦄ a ↦ a) _ h₃'
  simp only [subset_inter_iff, subset_iInter_iff]
  refine ⟨fun i hi x hx ↦ ?_, fun x hx ↦ ?_⟩
  · simp at hx ⊢
    obtain ⟨t, ht⟩ := hx i (lt_trans hi (Nat.lt_add_one _))
    use t
  · simp at hx ⊢
    obtain ⟨t, ht⟩ := hx 0 (zero_lt_succ _)
    simp at ht
    use t
    exact ht

/-- For `L : ℕ → Finset (Set α)` such that `∀ K ∈ L n, p K` and
`h : ∀ N, ⋂ k < N, ⋃₀ L k ≠ ∅`, `mem_of_union h n` is some `K : ℕ → Set α` such that `K n ∈ L n`
for all `n` (this is `prop₀`) and `∀ N, ⋂ (j < n, K j) ∩ ⋂ (k < N), (⋃₀ L (n + k)) ≠ ∅`
(this is `prop₁`.) -/
noncomputable def mem_of_union (L : ℕ → Finset (Set α))
  (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ (L k).toSet).Nonempty) : (k : ℕ) → L k :=
  Nat.prefixInduction' (q L) (step0 hL) (step')

theorem mem_of_union.spec (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ (L k).toSet).Nonempty) (n : ℕ) :
    (∀ N, ((⋂ (j : Fin n), (mem_of_union L hL) j) ∩ (⋂ (k < N), ⋃₀ (L (n + k)).toSet)).Nonempty) :=
  Nat.prefixInduction'_spec (β := fun n ↦ {a // a ∈ L n}) (q L) (step0 hL) (step') n

lemma l1 (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ (L k).toSet).Nonempty) (k : ℕ) :
      (mem_of_union L hL k).val ∈ (L k).toSet := by
  exact (mem_of_union L hL k).prop

lemma sInter_memOfUnion_nonempty (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k, ⋂ (_ : k < N), ⋃₀ (L k).toSet).Nonempty) (n : ℕ) :
    (⋂ (j : Fin n), (mem_of_union L hL j).val).Nonempty := by
  have h := mem_of_union.spec L hL n 0
  simp only [not_lt_zero, iInter_of_empty, iInter_univ, inter_univ] at h
  exact h

lemma sInter_memOfUnion_isSubset (L : ℕ → Finset (Set α))
    (hL : ∀ N, (⋂ k < N, ⋃₀ (L k).toSet).Nonempty) :
    (⋂ j, (mem_of_union L hL j)) ⊆ ⋂ k, (⋃₀ (L k).toSet) := by
  exact iInter_mono <| fun n ↦
  subset_sUnion_of_subset (↑(L n)) (mem_of_union L hL n).val (fun ⦃a⦄ a ↦ a) (l1 L hL n)

/-- Finite unions of sets in a compact system. -/
def union (p : Set α → Prop) : Set α → Prop :=
  (sUnion '' ({ L : Set (Set α) | L.Finite ∧ ∀ K ∈ L, p K}))

lemma union.mem_iff (s : Set α) : union p s ↔ ∃ L : Finset (Set α), s = ⋃₀ L ∧ ∀ K ∈ L, p K := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_setOf_eq] at hL
    let L' := (hL.1.1).toFinset
    use L'
    rw [← hL.2, Finite.coe_toFinset]
    refine ⟨rfl, fun K hK ↦ ?_⟩
    rw [Finite.mem_toFinset] at hK
    apply hL.1.2 K hK
  · obtain ⟨L, hL⟩ := h
    use L
    simp only [mem_setOf_eq, Finset.finite_toSet, Finset.mem_coe, true_and]
    refine ⟨hL.2, hL.1.symm⟩

theorem union.isCompactSystem (p : Set α → Prop) (hp : IsCompactSystem p) :
    IsCompactSystem (union p) := by
  rw [iff_nonempty_iInter_of_lt]
  intro C hi
  simp_rw [mem_iff] at hi
  choose L' hL' using hi
  simp_rw [hL']
  intro hL
  have h₁ := sInter_memOfUnion_nonempty L' hL
  have h₂ : (∀ (i : ℕ), p ↑(mem_of_union L' hL i)) :=
    fun i ↦ (hL' i).2 (mem_of_union L' hL i).val (mem_of_union L' hL i).prop
  have h₃ := (iff_nonempty_iInter_of_lt' p).mp hp (fun k ↦ (mem_of_union L' hL k).val) h₂ h₁
  have h₄ : ⋂ i, (mem_of_union L' hL) i ⊆ ⋂ i, ⋃₀ (L' i).toSet := sInter_memOfUnion_isSubset L' hL
  exact Nonempty.mono h₄ h₃

end Union

section pi

variable {ι : Type*} {α : ι → Type*}

/- In a product space, the intersection of square cylinders is empty iff there is a coordinate `i`
such that the projections to `i` have empty intersection. -/
theorem iInter_pi_empty_iff {β : Type*} (s : β → Set ι) (t : β → (i : ι) → Set (α i)) :
   (⋂ b, ((s b).pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β) (_: i ∈ s b), (t b i) = ∅):= by
  rw [iInter_eq_empty_iff, not_iff_not.symm]
  push_neg
  simp only [nonempty_iInter, mem_iInter]
  refine ⟨fun ⟨x, hx⟩ i ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨x i, fun j hi ↦ hx j i hi⟩
  · choose x hx using h
    refine ⟨x, fun i j hj ↦ hx j i hj⟩

theorem iInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) :
   ( ⋂ b, (univ.pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β), (t b i) = ∅):= by
  rw [iInter_pi_empty_iff]
  simp only [mem_univ, iInter_true]

theorem biInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) (p : β → Prop) :
   ( ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) = ∅) ↔
      (∃ i : ι, ⋂ (b : β), ⋂ (_ : p b), (t b i) = ∅) := by
  have h :  ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) =
      ⋂ (b : { (b' : β) | p b' }), (univ.pi (t b.val)) := by
    exact biInter_eq_iInter p fun x h ↦ univ.pi (t x)
  have h' (i : ι) :  ⋂ (b : β), ⋂ (_ : p b), t b i =  ⋂ (b : { (b' : β) | p b' }), t b.val i := by
    exact biInter_eq_iInter p fun x h ↦ t x i
  simp_rw [h, h', iInter_univ_pi_empty_iff]

theorem pi (C : (i : ι) → Set (Set (α i))) (hC : ∀ i, IsCompactSystem (C i)) :
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
  simp_rw [dissipate, ← hx2] at hn ⊢
  rw [biInter_univ_pi_empty_iff x]
  use i

end pi

end IsCompactSystem

section ClosedCompactSquareCylinders

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, TopologicalSpace (α i)]

variable (α)
/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both,
closed and compact, for all `i ∈ s`. -/
def MeasureTheory.compactClosedSquareCylinders : Set (Set (Π i, α i)) :=
  MeasureTheory.squareCylinders (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t })

/-- Products of compact and closed sets form a compact system. -/
theorem IsCompactSystem.compactClosedPi :
    IsCompactSystem (univ.pi '' univ.pi (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t })) :=
  IsCompactSystem.pi _ (fun _ ↦ IsCompactSystem.of_isCompact_isClosed)
/-- Products of compact and closed sets form a compact system. -/

theorem IsCompactSystem.compactClosedOrUnivPi :
    IsCompactSystem (univ.pi '' univ.pi (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t }
    ∪ { univ })) :=
  IsCompactSystem.pi _ (fun _ ↦ IsCompactSystem.of_isCompact_isClosed_or_univ)

/-- Compact and closed square cylinders are a compact system. -/
theorem isCompactSystem.compactClosedSquareCylinders :
    IsCompactSystem (compactClosedSquareCylinders α) :=
  IsCompactSystem.mono (IsCompactSystem.compactClosedOrUnivPi _)
    (squareCylinders_subset_of_or_univ _)

end ClosedCompactSquareCylinders

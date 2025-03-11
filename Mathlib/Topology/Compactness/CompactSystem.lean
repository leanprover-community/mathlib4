/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Dissipate
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

theorem isCompactSystem_subset (C D : Set (Set α)) (hC : IsCompactSystem C) (h : D ⊆ C) :
  IsCompactSystem D := fun s hD hs ↦ hC s (fun i ↦ h (hD i)) hs

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

end ClosedCompact

section ClosedCompactSquareCylinders

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, TopologicalSpace (α i)]

variable (α)
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

/-- Note that in `closedCompactSquareCylinders α`, the set of dependent variables is a finset,
  but not necessarily in `univ.pi '' univ.pi C`. -/
theorem closedCompactSquareCylinders_supset (C : (i : ι) → Set (Set (α i)))
  (hC : ∀ (i : ι), C i = (fun s : Set (α i) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ))) :
    closedCompactSquareCylinders α ⊆ univ.pi '' univ.pi C := by
  classical
  intro S hS
  simp_rw [mem_closedCompactSquareCylinders, squareCylinder] at hS
  simp only [mem_image, mem_pi, mem_univ, forall_const]
  obtain ⟨s, t, h_cl, h_co, h_pi⟩ := hS
  let t' := fun (i : ι) ↦ if (i ∈ s) then (t i) else univ
  refine ⟨t', ?_, ?_⟩
  · simp_rw [hC]
    intro i
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, t']
      apply Or.inl
      exact ⟨h_co i hi, h_cl i hi⟩
    · simp only [hi, ↓reduceIte, t']
      apply Or.inr rfl
  · change (pi univ fun i => if i ∈ (s : Set ι) then t i else univ) = S
    rw [h_pi, univ_pi_ite s t]

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

section pi

example (P Q : Prop) : (P ↔ Q) ↔ (¬ P ↔ ¬ Q) := by exact Iff.symm not_iff_not


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

theorem isCompactSystem_pi (C : (i : ι) → Set (Set (α i))) (hC : ∀ i, IsCompactSystem (C i)) :
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

theorem isCompactSystem_CompactClosedOrUniv (C : (i : ι) → Set (Set (α i)))
  (hC : ∀ (i : ι), C i = (fun s : Set (α i) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ))) :
     IsCompactSystem (univ.pi '' univ.pi C) := by
  intro S hS h_empty
  change ∀ i, S i ∈ univ.pi '' univ.pi C at hS
  simp only [mem_image, mem_pi, mem_univ, forall_const] at hS
  choose x hx1 hx2 using hS
  simp_rw [← hx2] at h_empty ⊢
  simp_rw [iInter_univ_pi_empty_iff x] at h_empty
  obtain ⟨i, hi⟩ := h_empty

  sorry

end pi

variable [∀ i, Nonempty (α i)]






theorem isCompactSystem_closedCompactSquareCylinders [∀ i, Nonempty (α i)]:
    IsCompactSystem (closedCompactSquareCylinders α) := by

  intro S hS h
  have h' : ∀ i, S i ∈ closedCompactSquareCylinders α := by exact fun i ↦ hS i
  simp_rw [mem_closedCompactSquareCylinders] at h'
  choose s t h_cl h_co hS using h'
  simp_rw [Dissipate, hS, squareCylinder] at h ⊢
  simp_rw [pi_eq_empty_iff'] at h





  sorry


end ClosedCompactSquareCylinders

section ClosedCompactCylinders


variable {ι : Type*} {α : ι → Type*}

variable [∀ i, TopologicalSpace (α i)]

variable (α)

/-- The set of all cylinders based on closed compact sets. Note that such a set is closed, but
not compact in general (for instance, the whole space is always a closed compact cylinder). -/
def closedCompactCylinders : Set (Set (Π i, α i)) :=
  ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

theorem empty_mem_closedCompactCylinders : ∅ ∈ closedCompactCylinders α := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

variable {α} {t : Set (Π i, α i)}

@[simp]
theorem mem_closedCompactCylinders (t : Set (Π i, α i)) :
    t ∈ closedCompactCylinders α
      ↔ ∃ (s S : _) (_ : IsClosed S) (_ : IsCompact S), t = cylinder s S := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]

/-- Given a closed compact cylinder, choose a finset of variables such that it only depends on
these variables. -/
noncomputable def closedCompactCylinders.finset (ht : t ∈ closedCompactCylinders α) :
    Finset ι :=
  ((mem_closedCompactCylinders t).mp ht).choose

/-- Given a closed compact cylinder, choose a set depending on finitely many variables of which it
is a lift. -/
def closedCompactCylinders.set (ht : t ∈ closedCompactCylinders α) :
    Set (∀ i : closedCompactCylinders.finset ht, α i) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

theorem closedCompactCylinders.isClosed (ht : t ∈ closedCompactCylinders α) :
    IsClosed (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose

theorem closedCompactCylinders.isCompact (ht : t ∈ closedCompactCylinders α) :
    IsCompact (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose_spec.choose

theorem closedCompactCylinders.eq_cylinder (ht : t ∈ closedCompactCylinders α) :
    t = cylinder (closedCompactCylinders.finset ht) (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose_spec.choose_spec

theorem cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (∀ i : s, α i))
    (hS_closed : IsClosed S) (hS_compact : IsCompact S) :
    cylinder s S ∈ closedCompactCylinders α := by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

theorem mem_cylinder_of_mem_closedCompactCylinders [∀ i, MeasurableSpace (α i)]
    [∀ i, SecondCountableTopology (α i)] [∀ i, OpensMeasurableSpace (α i)]
    (ht : t ∈ closedCompactCylinders α) :
    t ∈ measurableCylinders α := by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

/-! We prove that the `closedCompactCylinders` are a compact system. -/

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ℕ → Set (Π i, α i)}

local notation "Js" => closedCompactCylinders.finset
local notation "As" => closedCompactCylinders.set

section AllProj

/-- All indices in `ι` that are constrained by the condition `∀ n, s n ∈ closedCompactCylinders α`.
That is, the union of all indices in the bases of the cylinders. -/
def allProj (hs : ∀ n, s n ∈ closedCompactCylinders α) : Set ι := ⋃ n, Js (hs n)

theorem subset_allProj (hs : ∀ n, s n ∈ closedCompactCylinders α) (n : ℕ) :
    ↑(Js (hs n)) ⊆ allProj hs :=
  subset_iUnion (fun i ↦ (Js (hs i) : Set ι)) n

theorem exists_nat_proj (hs : ∀ n, s n ∈ closedCompactCylinders α) (i : ι) (hi : i ∈ allProj hs) :
    ∃ n, i ∈ Js (hs n) := by
  simpa only [allProj, mem_iUnion, Finset.mem_coe] using hi

open Classical in
/-- The smallest `n` such that `i ∈ Js (hs n)`. That is, the first `n` such that `i` belongs to the
finset defining the cylinder for `s n`. -/
noncomputable def indexProj (hs : ∀ n, s n ∈ closedCompactCylinders α) (i : allProj hs) : ℕ :=
  Nat.find (exists_nat_proj hs i i.2)

open Classical in
theorem mem_indexProj (hs : ∀ n, s n ∈ closedCompactCylinders α) (i : allProj hs) :
    (i : ι) ∈ Js (hs (indexProj hs i)) :=
  Nat.find_spec (exists_nat_proj hs i i.2)

open Classical in
theorem indexProj_le (hs : ∀ n, s n ∈ closedCompactCylinders α) (n : ℕ) (i : Js (hs n)) :
    indexProj hs ⟨i, subset_allProj hs n i.2⟩ ≤ n :=
  Nat.find_le i.2

lemma surjective_proj_allProj [∀ i, Nonempty (α i)] (hs : ∀ n, s n ∈ closedCompactCylinders α) :
    Function.Surjective (fun (f : (Π i, α i)) (i : allProj hs) ↦ f (i : ι)) := by
  intro y
  let x := (inferInstance : Nonempty (Π i, α i)).some
  classical
  refine ⟨fun i ↦ if hi : i ∈ allProj hs then y ⟨i, hi⟩ else x i, ?_⟩
  ext i
  simp only [Subtype.coe_prop, dite_true]

end AllProj

section projCylinder

/-- Given a countable family of closed cylinders, consider one of them as depending only on
the countably many coordinates that appear in all of them. -/
def projCylinder (hs : ∀ n, s n ∈ closedCompactCylinders α) (n : ℕ) :
    Set (∀ i : allProj hs, α i) :=
  (fun (f : ∀ i : allProj hs, α i) (i : Js (hs n)) ↦ f ⟨i, subset_allProj hs _ i.2⟩) ⁻¹' (As (hs n))

lemma mem_projCylinder (hs : ∀ n, s n ∈ closedCompactCylinders α) (n : ℕ)
    (x : ∀ i : allProj hs, α i) :
    x ∈ projCylinder hs n ↔ (fun (i : Js (hs n)) ↦ x ⟨i, subset_allProj hs _ i.2⟩) ∈ As (hs n) := by
  simp only [projCylinder, Set.mem_preimage]

theorem preimage_projCylinder (hs : ∀ n, s n ∈ closedCompactCylinders α) (n : ℕ) :
    (fun (f : ∀ i, α i) (i : allProj hs) ↦ f i) ⁻¹' (projCylinder hs n) = s n := by
  conv_rhs => rw [closedCompactCylinders.eq_cylinder (hs n)]
  rfl

lemma nonempty_projCylinder (hs : ∀ n, s n ∈ closedCompactCylinders α)
    (n : ℕ) (hs_nonempty : (s n).Nonempty) :
    (projCylinder hs n).Nonempty := by
  rw [← preimage_projCylinder hs n] at hs_nonempty
  exact nonempty_of_nonempty_preimage hs_nonempty

lemma nonempty_projCylinder_iff [∀ i, Nonempty (α i)]
    (hs : ∀ n, s n ∈ closedCompactCylinders α) (n : ℕ) :
    (projCylinder hs n).Nonempty ↔ (s n).Nonempty := by
  refine ⟨fun h ↦ ?_, nonempty_projCylinder hs n⟩
  obtain ⟨x, hx⟩ := h
  rw [mem_projCylinder] at hx
  rw [closedCompactCylinders.eq_cylinder (hs n), MeasureTheory.cylinder]
  refine Set.Nonempty.preimage ?_ ?_
  · exact ⟨_, hx⟩
  · intro y
    let x := (inferInstance : Nonempty (∀ i, α i)).some
    classical
    refine ⟨fun i ↦ if hi : i ∈ Js (hs n) then y ⟨i, hi⟩ else x i, ?_⟩
    ext i
    simp only [Finset.restrict_def, Finset.coe_mem, dite_true]

theorem isClosed_projCylinder
    (hs : ∀ n, s n ∈ closedCompactCylinders α) (hs_closed : ∀ n, IsClosed (As (hs n))) (n : ℕ) :
    IsClosed (projCylinder hs n) :=
  (hs_closed n).preimage (by exact continuous_pi (fun i ↦ continuous_apply _))

end projCylinder

section piCylinderSet

open Classical in
/-- Given countably many closed compact cylinders, the product set which, in each relevant
coordinate, is the projection of the first cylinder for which this coordinate is relevant. -/
def piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α) :
    Set (∀ i : allProj hs, α i) :=
  {x : ∀ i : allProj hs, α i |
    ∀ i, x i ∈ (fun a : ∀ j : Js (hs (indexProj hs i)), α j ↦ a ⟨i, mem_indexProj hs i⟩) ''
      (As (hs (indexProj hs i)))}

lemma mem_piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α)
    (x : ∀ i : allProj hs, α i) :
    x ∈ piCylinderSet hs ↔
    ∀ i, x i ∈ (fun a : ∀ j : Js (hs (indexProj hs i)), α j ↦ a ⟨i, mem_indexProj hs i⟩) ''
      (As (hs (indexProj hs i))) := by
  simp only [piCylinderSet, mem_image, Subtype.forall, mem_setOf_eq]

theorem isCompact_piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α) :
    IsCompact (piCylinderSet hs) :=
  isCompact_pi_infinite fun _ ↦
    (closedCompactCylinders.isCompact (hs _)).image (continuous_apply _)

theorem piCylinderSet_eq_pi_univ (hs : ∀ n, s n ∈ closedCompactCylinders α) :
    piCylinderSet hs =
      pi univ fun i ↦
        (fun a : ∀ j : Js (hs (indexProj hs i)), α j ↦ a ⟨i, mem_indexProj hs i⟩) ''
          (As (hs (indexProj hs i))) := by
  ext; simp only [piCylinderSet, mem_univ_pi]; rfl

theorem isClosed_piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α) :
    IsClosed (piCylinderSet hs) := by
  rw [piCylinderSet_eq_pi_univ]
  sorry
  --exact isClosed_set_pi fun i _ ↦ IsClosed.isClosed_image_restrict_singleton _
  --  (closedCompactCylinders.isCompact (hs _)) (closedCompactCylinders.isClosed (hs _))

theorem nonempty_piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α)
    (hs_nonempty : ∀ i, (s i).Nonempty) :
    (piCylinderSet hs).Nonempty := by
  have hs_nonempty' i : (As (hs i)).Nonempty := by
    specialize hs_nonempty i
    rw [closedCompactCylinders.eq_cylinder (hs i)] at hs_nonempty
    exact nonempty_of_nonempty_preimage hs_nonempty
  let b i := (hs_nonempty' (indexProj hs i)).some
  have hb_mem i : b i ∈ As (hs (indexProj hs i)) := (hs_nonempty' (indexProj hs i)).choose_spec
  let a : ∀ i : allProj hs, α i := fun i ↦ b i ⟨i, mem_indexProj hs i⟩
  refine ⟨a, ?_⟩
  simp only [piCylinderSet, mem_image, SetCoe.forall, mem_setOf_eq]
  exact fun j hj ↦ ⟨b ⟨j, hj⟩, hb_mem _, rfl⟩

end piCylinderSet

theorem iInter_subset_piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α) :
    (⋂ n, projCylinder hs n) ⊆ piCylinderSet hs := by
  intro x hx
  rw [mem_iInter] at hx
  rw [mem_piCylinderSet]
  intro i
  specialize hx (indexProj hs i)
  rw [mem_projCylinder] at hx
  exact ⟨fun i : Js (hs (indexProj hs i)) ↦ x ⟨i, subset_allProj hs _ i.2⟩, hx, rfl⟩

theorem nonempty_iInter_projCylinder_inter_piCylinderSet (hs : ∀ n, s n ∈ closedCompactCylinders α)
    (hs_nonempty : ∀ i, (s i).Nonempty)
    (h_nonempty : ∀ n, (⋂ i ≤ n, projCylinder hs i).Nonempty) (n : ℕ) :
    ((⋂ i ≤ n, projCylinder hs i) ∩ piCylinderSet hs).Nonempty := by
  obtain ⟨x, hx⟩ := nonempty_piCylinderSet hs hs_nonempty
  obtain ⟨y, hy⟩ := h_nonempty n
  let z := fun i : allProj hs ↦ if indexProj hs i ≤ n then y i else x i
  refine ⟨z, mem_inter ?_ ?_⟩
  · simp only [mem_iInter, mem_projCylinder]
    intro i hi
    have : (fun j : Js (hs i) ↦
          ite (indexProj hs ⟨j, subset_allProj hs i j.2⟩ ≤ n) (y ⟨j, subset_allProj hs i j.2⟩)
            (x ⟨j, subset_allProj hs i j.2⟩)) =
        fun j : Js (hs i) ↦ y ⟨j, subset_allProj hs i j.2⟩ := by
      ext j
      rw [if_pos]
      refine le_trans (le_of_eq ?_) ((indexProj_le hs i j).trans hi)
      congr
    rw [this]
    have hyi : y ∈ projCylinder hs i := by
      suffices ⋂ j ≤ n, projCylinder hs j ⊆ projCylinder hs i by exact this hy
      exact biInter_subset_of_mem hi
    rwa [mem_projCylinder] at hyi
  · rw [mem_piCylinderSet]
    intro i
    by_cases hi_le : indexProj hs i ≤ n
    · let m := indexProj hs i
      have hy' : y ∈ projCylinder hs m := by
        suffices ⋂ j ≤ n, projCylinder hs j ⊆ projCylinder hs m by exact this hy
        exact biInter_subset_of_mem hi_le
      rw [mem_projCylinder] at hy'
      refine ⟨fun j ↦ y ⟨j, subset_allProj hs _ j.2⟩, hy', ?_⟩
      simp_rw [z, if_pos hi_le]
    · rw [mem_piCylinderSet] at hx
      specialize hx i
      obtain ⟨x', hx'_mem, hx'_eq⟩ := hx
      refine ⟨x', hx'_mem, ?_⟩
      simp_rw [z, if_neg hi_le]
      exact hx'_eq

theorem nonempty_iInter_projCylinder (hs : ∀ n, s n ∈ closedCompactCylinders α)
    (hs_nonempty : ∀ i, (s i).Nonempty)
    (h_nonempty : ∀ n, (⋂ i ≤ n, projCylinder hs i).Nonempty) :
    (⋂ i, projCylinder hs i).Nonempty := by
  suffices ((⋂ i, projCylinder hs i) ∩ piCylinderSet hs).Nonempty by
    rwa [inter_eq_left.mpr (iInter_subset_piCylinderSet hs)] at this
  have : (⋂ n, projCylinder hs n) = (⋂ n, ⋂ i ≤ n, projCylinder hs i) := by
    ext x
    simp only [mem_iInter]
    exact ⟨fun h i j _ ↦ h j, fun h i ↦ h i i le_rfl⟩
  rw [this, iInter_inter]
  have h_closed : ∀ n, IsClosed (⋂ i ≤ n, projCylinder hs i) :=
    fun n ↦ isClosed_biInter (fun i _ ↦ isClosed_projCylinder hs
      (fun n ↦ (closedCompactCylinders.isClosed (hs n))) i)
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n ↦ (⋂ i ≤ n, projCylinder hs i) ∩ piCylinderSet hs) ?_ ?_ ?_ ?_
  · refine fun i ↦ inter_subset_inter ?_ subset_rfl
    simp_rw [Set.biInter_le_succ]
    exact inter_subset_left
  · exact fun n ↦ nonempty_iInter_projCylinder_inter_piCylinderSet hs hs_nonempty h_nonempty n
  · exact (isCompact_piCylinderSet hs).inter_left (h_closed _)
  · exact fun n ↦ IsClosed.inter (h_closed n) (isClosed_piCylinderSet hs)

lemma exists_finset_iInter_projCylinder_eq_empty [∀ i, Nonempty (α i)]
    (hs : ∀ n, s n ∈ closedCompactCylinders α) (h : ⋂ n, projCylinder hs n = ∅) :
    ∃ t : Finset ℕ, (⋂ i ∈ t, projCylinder hs i) = ∅ := by
  by_contra! h_nonempty
  refine absurd h (Set.Nonempty.ne_empty ?_)
  refine nonempty_iInter_projCylinder hs (fun i ↦ ?_) (fun n ↦ ?_)
  · specialize h_nonempty {i}
    simp only [Finset.mem_singleton, iInter_iInter_eq_left, ne_eq] at h_nonempty
    rwa [nonempty_projCylinder_iff] at h_nonempty
  · specialize h_nonempty (Finset.range (n + 1))
    simp only [Finset.mem_range, ne_eq, Nat.lt_succ_iff] at h_nonempty
    exact h_nonempty

/-- The `closedCompactCylinders` are a compact system. -/
theorem isCompactSystem_closedCompactCylinders : IsCompactSystem (closedCompactCylinders α) := by
  intro s hs h
  by_cases hα : ∀ i, Nonempty (α i)
  swap; · exact ⟨∅, by simpa [not_nonempty_iff] using hα⟩
  have h' : ⋂ n, projCylinder hs n = ∅ := by
    simp_rw [← preimage_projCylinder hs, ← preimage_iInter] at h
    have h_surj : Function.Surjective (fun (f : (∀ i, α i)) (i : allProj hs) ↦ f (i : ι)) :=
      surjective_proj_allProj hs
    rwa [← not_nonempty_iff_eq_empty, ← Function.Surjective.nonempty_preimage h_surj,
      not_nonempty_iff_eq_empty]
  obtain ⟨t, ht⟩ := exists_finset_iInter_projCylinder_eq_empty hs h'
  refine ⟨t, ?_⟩
  simp_rw [← preimage_projCylinder hs, ← preimage_iInter₂, ht, preimage_empty]

end ClosedCompactCylinders

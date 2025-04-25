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

variable {p : Set α → Prop} (hp : IsCompactSystem p) (L : ℕ → Finset (Set α))
  (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n : Set (Set α))), p d)

-- variable (p : {n : ℕ} → ((k : Fin (n + 1)) → (β k)) → Prop)

noncomputable def r (n : ℕ) (K : ℕ → Set α) : Prop :=
  ∀ N, ⋂ (j < n), (K j) ∩ ⋂ (k < N), (⋃₀ (L (n + k)).toSet) ≠ ∅

-- h0 -> (get_element_zero hL hc)
-- (h0 : ∃ x : (ℕ → α), x 0 ∈ β 0 ∧ p 0 x)

lemma nonempty (k : ℕ) (hc : ∀ N, ⋂ k < N, ⋃₀ (L k : Set (Set α)) ≠ ∅) : (L k).Nonempty := by
  specialize hc (k + 1)
  by_contra! h
  simp only [Finset.not_nonempty_iff_eq_empty] at h
  apply hc
  apply iInter_eq_empty_iff.mpr fun x ↦ ⟨k, ?_⟩
  simp only [lt_add_iff_pos_right, lt_one_iff, pos_of_gt, iInter_true]
  have hg : ⋃₀ (L k : Set (Set α)) = ∅ := by
    rw [h]
    simp only [Finset.coe_empty, sUnion_empty]
  exact of_eq_false (congrFun hg x)

private lemma inter_sUnion_sUnion (m n : ℕ) : (⋂ k < m, (⋃₀ L k)) ∩ ⋂ (k < n), ⋃₀ L (m + k) =
    ⋂ (k < m + n), ⋃₀ (L k).toSet := by
  ext x
  rw [mem_inter_iff, mem_iInter₂, mem_iInter₂, mem_iInter₂]
  refine ⟨fun h i hi ↦ ?_, fun h ↦ ?_⟩
  · by_cases h' : i < m
    · exact h.1 i h'
    · have hj : ∃ j, j < n ∧ i = m + j := by
        use i - m
        refine ⟨Nat.sub_lt_left_of_lt_add (not_lt.mp h') hi, Eq.symm (add_sub_of_le (not_lt.mp h'))⟩
      obtain ⟨j, hj₁, hj₂⟩ := hj
      rw [hj₂]
      exact h.2 j hj₁
  · refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · have h' (j m n : ℕ) (hj : j < m) : j < m + n := by
        exact Nat.lt_add_right n hj
      exact h i (h' i m n hi)
    · have h' (j m n : ℕ) : j < n → ((m + j) < m + n) :=  by
        exact fun a ↦ Nat.add_lt_add_left a m
      exact h (m + i) (h' i m n hi)


-- (h0 : ∃ x : (ℕ → α), p 0 x)

def q : ℕ → (ℕ → Set α) → Prop := fun n K ↦ (∀ k < n, K k ∈ L k) ∧ (r L n K)

variable [Nonempty α]

lemma get_element_zero : ∃ (K : ℕ → Set α), q L 0 K := by
  simp [q, r]


--  (h : ∀ (n : ℕ) (x : (ℕ → α)) (hx : p n x), ∃ y, p (n + 1) (Function.update x n y))

-- p n x ↔ (∀ k < n, K k ∈ β k) ∧ (r n K)

lemma get_element_succ' (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d) (n : ℕ)
  (K : ℕ → Set α) (hK : q L n K) : ∃ y, q L (n + 1) (Function.update K n y) := by
  simp_rw [q, r] at hK ⊢
  by_contra! h
  choose b hb using h
  have hn (a : Set α) (ha : a ∈ L n) : (∀ k < n + 1, Function.update K n a k ∈ L k) := by
    sorry
  classical
  let b' : Set α → ℕ := fun y ↦ dite (y ∈ L n) (fun h ↦ b y (hn y h)) (fun _ ↦ 0)
  have hc : ∀ N, ⋂ k < N, ⋃₀ (L k : Set (Set α)) ≠ ∅ := by sorry
  obtain ⟨K0Max, ⟨hK0₁, hK0₂⟩⟩ := Finset.exists_max_image (L n) b' (nonempty L n hc)
  apply hc (b' K0Max + 1 + 1)

  have h' : ∀ a ∈ L n, ⋂ (k < n), ⋃₀ ↑(L k) ∩ a ∩ ⋂ (k < b' K0Max + 1), ⋃₀ ↑(L (n + k)) = ∅ := by
    sorry







  sorry

noncomputable def m' : (n : ℕ) → ((K : ℕ → Set α) ×' (q L n K))
  | 0 => ⟨(get_element_zero L).choose, (get_element_zero L).choose_spec⟩
  | n + 1 => by
    have g := (get_element_succ' L hL) n (m' n).1 (m' n).2
    refine ⟨Function.update (m' n).1 n g.choose, g.choose_spec⟩




lemma get_element_zero' (hL : ∀ n d (hd : d ∈ (L n : Set (Set α))), p d)
    (hc : ∀ N, ⋂ k < N, ⋃₀ ((L k) : Set (Set α)) ≠ ∅) :
      ∃ (K : ℕ → Set α) (hK : ∀ k < 1, K k ∈ L k), r L 1 K := by
  have hKfun {K : Set α} (hK' : K ∈ L 0) (k : ℕ) (hk : k < 1) : (fun _ ↦ K) k ∈ L k :=
    (lt_one_iff.mp hk) ▸ hK'
  simp_rw [r]
  have d : ∃ (K : Set α) (hK' : K ∈ L 0), r L 1 (fun _ ↦ K) := by
    simp_rw [r]
    by_contra! h
    choose! b ha using h
    obtain ⟨K0Max, ⟨hK0₁, hK0₂⟩⟩ := Finset.exists_max_image (L 0) b (nonempty L 0 hc)
    apply hc (b K0Max + 1 + 1)
    -- refine Set.iInter_eq_empty_iff.mpr fun x ↦ ?_
    have h' : ∀ a ∈ L 0, a ∩ ⋂ k < 1, ⋂ (k < b K0Max + 1), ⋃₀ ↑(L (1 + k)) = ∅ := by
      intro a' h'
      have f := (ha a' h')
      simp only [lt_one_iff, iInter_iInter_eq_left] at f
      refine subset_eq_empty (inter_subset_inter (fun ⦃a⦄ a ↦ a)  (iInter_mono' (fun j ↦ ?_))) f
      use 0
      intro k
      simp only [lt_one_iff, pos_of_gt, iInter_true, mem_iInter, mem_sUnion, Finset.mem_coe]
      intro hk hj
      exact hk j (le_trans hj (le_trans (hK0₂ a' h') (le_succ (b K0Max))))
    simp only [lt_one_iff, iInter_iInter_eq_left] at h'
    have h'' : ∀ (a : L 0), a.val ∩ ⋂ k, ⋂ (_ : k < b K0Max + 1), ⋃₀ (L (1 + k) : Set (Set α)) = ∅ := by
      rw [Subtype.forall]
      simp only
      exact h'
    rw [← iUnion_eq_empty] at h''
    have h''' : (⋃ a : L 0, a.val) ∩ (⋂ k, ⋂ (_ : k < b K0Max + 1), ⋃₀ (L (1 + k) : Set (Set α))) = ∅ := by
      rw [iUnion_inter]
      exact h''
    have h'''': ⋃₀ L 0 ∩ ⋂ k, ⋂ (_ : k < b K0Max + 1), ⋃₀ (L (1 + k) : Set (Set α)) = ∅ := by
      rw [sUnion_eq_iUnion]
      exact h'''
    rw [l] at h''''
    exact h''''
  obtain ⟨K, ⟨hK₁, hK₂⟩⟩ := d
  refine ⟨fun _ ↦ K, hKfun hK₁, hK₂⟩



lemma get_element_succ (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (n : ℕ), ⋂ (k : Fin (n + 1)), (⋃₀ (L k).toSet) ≠ ∅) : ∀
    (n : ℕ) (K' : (k : Fin (n + 1)) → (L k)), r K' →
      ∃ (K : (L (n + 1))), r (join K' K) := by
  intro n K' hK'
  simp only [r, ne_eq, Subtype.exists]
  by_contra! h
  choose! b ha using h
  classical
  obtain ⟨aMax, ⟨ha1, ha2⟩⟩ := Finset.exists_max_image (L (n + 1)) b (nonempty (n + 1) hc)
  have h' : ∀ (a : L (n + 1)), ⋂ k, ↑(join K' a k) ∩
      ⋂ (k : Fin (b aMax)), ⋃₀ (L (n + 1 + 1 + ↑k) : Set (Set α)) = ∅ := by
    intro a'
    refine subset_eq_empty ?_ (ha a'.val a'.prop)
    rw [← iInter_inter, ← iInter_inter]
    apply (inter_subset_inter (fun ⦃a⦄ a ↦ a)  (iInter_mono' (fun j ↦ ?_)))
    use ⟨j.val, le_trans j.prop (ha2 a'.val a'.prop)⟩
  simp only [r] at hK'
  apply hK' (b aMax + 1)
  rw [← iUnion_eq_empty] at h'
  rw [iUnion_join] at h'
  rw [← h']
  refine iInter_congr fun i ↦ ?_
  rw [inter_assoc]
  refine congrArg (Inter.inter _)  ?_
  rw [l4]
  simp only [Fin.val_zero, add_zero, Fin.coe_eq_castSucc]
  apply congrArg (Inter.inter _)
  refine iInter_congr fun i ↦ ?_
  ext x
  simp only [Fin.coeSucc_eq_succ, Fin.val_succ, mem_sUnion, Finset.mem_coe]
  refine ⟨fun ⟨t, ⟨ht1, ht2⟩⟩ ↦ ⟨t, ⟨?_, ht2⟩⟩, fun ⟨t, ⟨ht1, ht2⟩⟩ ↦ ⟨t, ⟨?_, ht2⟩⟩⟩
  · rw [add_assoc]
    nth_rewrite 3 [add_comm]
    exact ht1
  · rw [add_assoc] at ht1
    nth_rewrite 3 [add_comm] at ht1
    exact ht1



theorem main' (p : Set α → Prop) (hp : IsCompactSystem p) (L : ℕ → Finset (Set α))
    (hL : ∀ (n : ℕ) (d : Set α) (hd : d ∈ (L n).toSet), p d)
    (hc : ∀ (n : ℕ), ⋂ (k : Fin (n + 1)), (⋃₀ (L k).toSet) ≠ ∅) :
    ∃ (K : (j : ℕ) → (L j)), (∀ n N, ⋂ (j : Fin (n + 1)), (K j) ∩ ⋂ (k < N),
      ⋃₀ (L (n + 1 + k)).toSet ≠ ∅) := by
  sorry


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





variable {β : (n : ℕ) → (Set α)} (p : ℕ → (ℕ → α) → Prop)

variable (h0 : ∃ x : (ℕ → α), p 0 x)
  (h : ∀ (n : ℕ) (x : (ℕ → α)) (hx₁ : ∀ k < n, x k ∈ β k) (hx₂  : p n x) ,
    ∃ y ∈ β n, p (n + 1) (Function.update x n y))

noncomputable def m' : (n : ℕ) → ((x : ℕ → α) ×' (∀ k < n, x k ∈ β k) ∧ (p n x))
  | 0 => ⟨h0.choose, ⟨by simp, h0.choose_spec⟩⟩
  | n + 1 => by
    have g : ∃ y ∈ β n, p (n + 1) (Function.update (m' n).fst n y) := (h n (m' n).1 (m' n).2.1 (m' n).2.2)
    obtain ⟨y, hy⟩ := g
    have g' : Function.update (m' n).1 n g.choose n ∈ β n := by
      simp only [ne_eq, left_eq_add, one_ne_zero, not_false_eq_true, Function.update_of_ne]

      simp only [Function.update_self]
      exact g.choose_spec.1
    exact ⟨Function.update (m' n).1 (n + 1) g.choose, fun g' ↦ g.choose_spec.2⟩

lemma e (n : ℕ) : (((m' p h0 h n).1 n) ∈ β n) ∧ (p n (m' p h0 h n).1) := by
  exact (m' p h0 h n).2

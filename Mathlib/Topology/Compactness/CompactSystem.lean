/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Dissipate
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Separation.Hausdorff
/-!
# Compact systems.

This files defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.
* `IsCompactSystem.union`: The set system of finite unions of another set system.
## Main results

* `IsClosedCompact.isCompactSystem`: The set of closed and compact sets is a compact system.
* `IsClosedCompact.isCompactSystem_of_T2Space`: In a `T2Space α`, the set of compact sets
  is a compact system in a `T2Space`.
* `IsCompactSystem.union.isCompactSystem`: If `IsCompactSystem p`, the set of finite unions
  of `K : Set α` with `p K` is a compact system.
* `IsCompactSystem.closedCompactSquareCylinders`: Closed and compact square cylinders form a
  compact system in a product space.
-/

open Set Nat MeasureTheory

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (p : Set α → Prop) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, p (C i)) → ⋂ i, C i = ∅ → ∃ (n : ℕ), Dissipate C n = ∅

end definition

namespace IsCompactSystem

/-- In a compact system, given a countable family with empty intersection, we choose a finite
subfamily with empty intersection. -/
noncomputable
def max_of_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) : ℕ :=
  (hp C hC hC_empty).choose

lemma iInter_eq_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) :
    Dissipate C (hp.max_of_empty hC hC_empty) = ∅ :=
  (hp C hC hC_empty).choose_spec

theorem iff_of_nempty (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (Dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) := by
  refine ⟨fun h C hC hn ↦ ?_, fun h C hC ↦ ?_⟩ <;> have h2 := not_imp_not.mpr <| h C hC
  · push_neg at h2
    exact h2 hn
  · push_neg at h2
    exact h2

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma iff_of_not_empty (p : Set α → Prop) : IsCompactSystem p ↔
    ∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ n, ⋂ k < n, C k ≠ ∅) → ⋂ i, C i ≠ ∅ := by
  simp_rw [← Set.nonempty_iff_ne_empty, iff_of_nempty]
  refine ⟨fun h C hi h'↦ ?_, fun h C hi h' ↦ ?_⟩
  · apply h C hi
    exact fun n ↦ dissipate_eq ▸ (h' (n + 1))
  · apply h C hi
    intro n
    simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
    intro g
    apply h' n
    simp_rw [← subset_empty_iff, Dissipate] at g ⊢
    apply le_trans _ g
    intro x
    rw [mem_iInter₂, mem_iInter₂]
    exact fun h i hi ↦ h i hi.le

theorem iff_directed (hpi : ∀ (s t : Set α), p s → p t → p (s ∩ t)) :
    (IsCompactSystem p) ↔
    (∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
      ⋂ i, C i = ∅ → ∃ (n : ℕ), C n = ∅) := by
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [dissipate_exists_empty_iff_of_directed C hdi]
    exact h C hi
  · rw [← biInter_le_eq_iInter] at h2
    exact h (Dissipate C) dissipate_directed (dissipate_of_piSystem hpi h1) h2

theorem iff_directed' (hpi : ∀ (s t : Set α), p s → p t → p (s ∩ t)) :
    (IsCompactSystem p) ↔
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
    fun i ↦ (Or.resolve_right (h1 i.val) i.prop).2
  have htco : ∀ (i : { j : ℕ | s j ≠ univ}), IsCompact (s i) :=
    fun i ↦ (Or.resolve_right (h1 i.val) i.prop).1
  haveI f : Nonempty α := by
    apply nonempty_of_exists _
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
      · simp only [ne_eq, not_not, s'] at g
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

lemma l2 {ι : Type*} (s t : Set α) (u : Set ι) (L : (i : ι) → (hi : i ∈ u) → Set α)
  (h : s ⊆ ⋃ (n : ι) (hn : n ∈ u), L n hn) (h' : ∀ (n : ι) (hn : n ∈ u), t ∩ (L n hn) = ∅) :
    t ∩ s = ∅ := by
  have j : ⋃ (n : ι) (hn : n ∈ u), t ∩ (L n hn) = ∅ := by
    simp_rw [iUnion_eq_empty]
    exact h'
  simp_rw [← subset_empty_iff] at h' j ⊢
  have j' : ⋃ (n : u), t ∩ L n.val n.prop = ⋃ n, ⋃ (hn : n ∈ u), t ∩ L n hn := by
    exact iUnion_coe_set u fun i ↦ t ∩ L (↑i) (Subtype.prop i)
  rw [← j', ← inter_iUnion, iUnion_coe_set] at j
  have gf := inter_subset_inter (t₁ := t) (fun ⦃a_1⦄ a ↦ a) h
  apply le_trans gf j

variable {p : Set α → Prop} (hp : IsCompactSystem p) (L : ℕ → Finset (Set α))
  (hL : ∀ (n : ℕ) (d : Set α) (_ : d ∈ (L n : Set (Set α))), p d)

-- variable (p : {n : ℕ} → ((k : Fin (n + 1)) → (β k)) → Prop)

/-- `r n K` is the property which must hold for compact systems:
`∀ N, (⋂ (j < n), (K j)) ∩ (⋂ (k < N), (⋃₀ (L (n + k)).toSet)) ≠ ∅`. -/
noncomputable def r (n : ℕ) (K : ℕ → Set α) : Prop :=
  ∀ N, (⋂ (j < n), (K j)) ∩ (⋂ (k < N), (⋃₀ (L (n + k)).toSet)) ≠ ∅

-- h0 -> (get_element_zero hL hc)
-- (h0 : ∃ x : (ℕ → α), x 0 ∈ β 0 ∧ p 0 x)

lemma nonempty' (n : ℕ) (K : ℕ → Set α)
    (hc : ∀ N, (⋂ (k < n), K k) ∩ (⋂ k < N, ⋃₀ (L (n + k))) ≠ ∅) : (L n).Nonempty := by
  specialize hc 1
  by_contra! h
  simp only [Finset.not_nonempty_iff_eq_empty] at h
  apply hc
  simp [h]

lemma nonempty (k : ℕ) (hc : ∀ N, ⋂ k < N, ⋃₀ (L k : Set (Set α)) ≠ ∅) : (L k).Nonempty := by
  specialize hc (k + 1)
  by_contra! h
  simp only [Finset.not_nonempty_iff_eq_empty] at h
  apply hc
  apply iInter_eq_empty_iff.mpr fun x ↦ ⟨k, ?_⟩
  -- simp only [Nat.lt_add_one, iInter_true, mem_sUnion, Finset.mem_coe, not_exists, not_and]
  simp only [Nat.lt_add_one, iInter_true, Finset.mem_coe, not_exists, not_and]
  have hg : ⋃₀ (L k : Set (Set α)) = ∅ := by
    rw [h]
    simp only [Finset.coe_empty, sUnion_empty]
  exact of_eq_false (congrFun hg x)

/-- `q n K` is the joint property that `(∀ k < n, K k ∈ L k)` and `r n K)` holds. -/
def q : ℕ → (ℕ → Set α) → Prop := fun n K ↦ (∀ k < n, K k ∈ L k) ∧ (r L n K)

lemma get_element_zero (h : ∀ N, ⋂ k, ⋂ (_ : k < N), ⋃₀ (L k).toSet ≠ ∅) :
    ∃ (K : ℕ → Set α), q L 0 K := by
  simp [q, r, h]

lemma get_element_succ' (n : ℕ)
  (K : ℕ → Set α) (hK : q L n K) : ∃ y, q L (n + 1) (Function.update K n y) := by
  simp_rw [q, r] at hK ⊢
  by_contra! h
  choose b hb using h
  have hn : ∀ y ∈ L n, ∀ k < n + 1, Function.update K n y k ∈ L k := by
    intro y hy k hk
    by_cases d : n = k
    · rw [d]
      simp only [Function.update_self]
      exact d ▸ hy
    · have d' : k < n := by
        by_contra h
        apply d
        simp only [not_lt] at h
        apply Eq.symm
        exact Nat.eq_of_le_of_lt_succ h hk
      simp only [ne_eq, d'.ne, not_false_eq_true, Function.update_of_ne]
      exact hK.1 k d'
  classical
  let b' := fun y ↦ dite (y ∈ L n) (fun hy ↦ (b y (hn y hy))) (fun _ ↦ 0)
  have hb' := fun y hy ↦ hb y (hn y hy)
  have hb'' (y : Set α) (hy : y ∈ L n) : b y (hn y hy) = b' y  := by
    simp [b', hy]
  obtain ⟨K0Max, ⟨hK0₁, hK0₂⟩⟩ := Finset.exists_max_image (L n) b' (nonempty' L n K hK.2)
  apply hK.2 (b' K0Max + 1)
  have h₁ (y s : Set α): (⋂ j, ⋂ (_ : j < n + 1), Function.update K n y j) ∩ s =
      (⋂ j, ⋂ (_ : j < n), K j) ∩ y ∩ s := by
    apply congrFun (congrArg Inter.inter _) s
    ext x
    refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩ <;> simp only [mem_iInter, mem_inter_iff] at h ⊢
    · intro i hi
      have h' := h i (le_trans hi (le_succ n))
      simp only [ne_eq, hi.ne, not_false_eq_true, Function.update_of_ne] at h'
      exact h'
    · have h'' := h n (Nat.lt_add_one n)
      simp only [Function.update_self] at h''
      exact h''
    · intro i hi
      by_cases h₁ : i < n
      · simp only [ne_eq, h₁.ne, not_false_eq_true, Function.update_of_ne]
        exact h.1 i h₁
      · simp only [not_lt] at h₁
        have h₂ := Nat.eq_of_le_of_lt_succ h₁ hi
        rw [h₂]
        simp only [Function.update_self]
        exact h.2
  simp_rw [h₁] at hb'

  have h₂ : ⋂ k < b' K0Max + 1, ⋃₀ (L (n + k)).toSet ⊆
    ⋃ (y : Set α) (hy : y ∈ L n), y ∩ ⋂ (k < b y (hn y hy)), ⋃₀ (L (n + 1 + k)).toSet := by
    obtain ⟨y, hy⟩ := nonempty' L n K hK.2
    intro x hx
    simp only [mem_iInter, mem_sUnion, Finset.mem_coe, mem_iUnion, mem_inter_iff,
      exists_and_left] at hx ⊢
    obtain ⟨i, hi⟩ := hx 0 (zero_lt_succ (b' K0Max))
    rw [add_zero] at hi
    use i, hi.2, hi.1
    intro k hk
    have hk' : 1 + k < b' K0Max + 1:= by
      rw [add_comm]
      simp only [Nat.add_lt_add_iff_right]
      apply lt_of_lt_of_le hk
      rw [hb'']
      apply hK0₂ i hi.1
      exact hi.1
    obtain ⟨t, ht⟩ := hx (1 + k) hk'
    rw [← add_assoc] at ht
    use t, ht.1, ht.2
  simp_rw [inter_assoc] at hb'
  apply l2 (s := ⋂ k < b' K0Max + 1, ⋃₀ (L (n + k)).toSet) (t := (⋂ j < n, K j)) (u := L n)
    (L := fun (y : Set α) (hy : y ∈ L n) ↦ (y ∩ ⋂ k, ⋂ (hk : k < b y (hn y hy)),
      ⋃₀ (L (n + 1 + k)).toSet)) h₂ hb'

/-- `mem_of_union_aux h n` is the product of some `K : ℕ → Set α)` and `q n K`.
Constructing `(mem_of_union_aux h n).1` works inductively. When constructing
`(mem_of_union_aux h (n + 1)).1`, we update `(mem_of_union_aux h n).1` only at position `n`. -/
noncomputable def mem_of_union_aux (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) :
    (n : ℕ) → ((K : ℕ → Set α) ×' (q L n K))
  | 0 => ⟨(get_element_zero L h).choose, (get_element_zero L h).choose_spec⟩
  | n + 1 => by
    have g := (get_element_succ' L) n (mem_of_union_aux h n).1 (mem_of_union_aux h n).2
    exact ⟨Function.update (mem_of_union_aux h n).1 n g.choose, g.choose_spec⟩

namespace mem_of_union

lemma constantEventually (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n k : ℕ) (hkn : k < n) :
    (mem_of_union_aux L h n).1 k = (mem_of_union_aux L h (n + 1)).1 k := by
  simp [mem_of_union_aux, hkn.ne]

lemma constantEventually' (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n k : ℕ) (hkn : k < n) :
    (mem_of_union_aux L h n).1 k = (mem_of_union_aux L h (k + 1)).1 k := by
  induction n with
  | zero =>
    cases hkn
  | succ n hn =>
    by_cases h' : k < n
    · rw [← hn h']
      exact (constantEventually L h n k h').symm
    · have hkn' : k = n := by
        exact Nat.eq_of_lt_succ_of_not_lt hkn h'
      rw [hkn']

lemma constantEventually'' (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (m n k : ℕ)
  (hkn : k < n) (hkm : k < m) : (mem_of_union_aux L h n).1 k
      = (mem_of_union_aux L h m).1 k := by
  rw [constantEventually' L h n k hkn, constantEventually' L h m k hkm]

end mem_of_union

/-- For `L : ℕ → Finset (Set α)` such that `∀ K ∈ L n, p K` and
`h : ∀ N, ⋂ k < N, ⋃₀ L k ≠ ∅`, `mem_of_union h n` is some `K : ℕ → Set α` such that `K n ∈ L n`
for all `n` (this is `prop₀`) and `∀ N, ⋂ (j < n, K j) ∩ ⋂ (k < N), (⋃₀ L (n + k)) ≠ ∅`
(this is `prop₁`.) -/
noncomputable def mem_of_union (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) :=
  fun n ↦ (mem_of_union_aux L h (n + 1)).1 n

namespace mem_of_union

lemma prop₀ (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n : ℕ) : mem_of_union L h n ∈ L n := by
  exact (mem_of_union_aux L h (n + 1)).2.1 n (Nat.lt_add_one n)

lemma isSubset (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n N : ℕ) :
    (⋂ j < n, mem_of_union L h j) ∩ ⋂ (k < N), (⋃₀ L (n + k)) ⊆
      ⋂ (k < n + N), (⋃₀ (L k).toSet) := by
  have h' : ⋂ (k < n + N), (⋃₀ (L k).toSet) =
    (⋂ (k < n), (⋃₀ (L k).toSet)) ∩ ⋂ (k <  N), (⋃₀ (L (n + k)).toSet) := by
    ext x
    simp only [mem_iInter, mem_sUnion, Finset.mem_coe, mem_inter_iff]
    refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩, fun h i hi ↦ ?_⟩
    · refine h i (lt_of_lt_of_le hi (Nat.le_add_right n N))
    · refine h (n + i) (Nat.add_lt_add_left hi n)
    · by_cases hin : i < n
      · exact h.1 i hin
      · have h₁ : i - n < N := Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hin) hi
        have h₂ : n + (i - n) = i := by
          exact add_sub_of_le <| Nat.le_of_not_lt hin
        exact h₂ ▸ h.2 (i - n) h₁
  rw [h']
  apply inter_subset_inter _ fun ⦃a⦄ a ↦ a
  have h'' (j : ℕ) (hj : j < n) : mem_of_union L h j ⊆ ⋃₀ (L j).toSet := by
    exact subset_sUnion_of_mem <| prop₀ L h j
  exact iInter₂_mono h''

lemma isSubsetN0 (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) :
    (⋂ j, mem_of_union L h j) ⊆
      ⋂ k, (⋃₀ (L k).toSet) := by
  exact iInter_mono <| fun n ↦
  subset_sUnion_of_subset (↑(L n)) (mem_of_union L h n) (fun ⦃a⦄ a ↦ a) (prop₀ L h n)

lemma has_p (hL : ∀ (n : ℕ) (d : Set α) (_ : d ∈ (L n : Set (Set α))), p d)
    (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n : ℕ) : p (mem_of_union L h n) := by
  exact hL n (mem_of_union L h n) (prop₀ L h n)

lemma prop₁ (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n : ℕ) :
    ∀ N, (⋂ (j < n), (mem_of_union L h j)) ∩ (⋂ (k < N), (⋃₀ (L (n + k)).toSet)) ≠ ∅ := by
  have h' : r L n (mem_of_union_aux L h n).fst := (mem_of_union_aux L h n).2.2
  simp only [r] at h'
  simp only [mem_of_union]
  intro N
  specialize h' N
  conv at h' =>
    lhs
    enter [1,1]
    intro j
    enter[1]
    intro hj
    rw [constantEventually' L h n j hj]
  exact h'

lemma prop₁N0 (h : ∀ N, ⋂ k < N, ⋃₀ (L k).toSet ≠ ∅) (n : ℕ) :
    (⋂ (j < n), (mem_of_union L h j)) ≠ ∅ := by
  have h' : (⋂ (k < 0), (⋃₀ (L (n + k)).toSet)) = univ := by
    simp
  have d (s : Set α) : s = s ∩ univ := by exact left_eq_inter.mpr fun ⦃a⦄ a ↦ trivial
  rw [d (⋂ j, ⋂ (_ : j < n), mem_of_union L h j)]
  rw [← h']
  exact prop₁ L h n 0

end mem_of_union

/-- Finite unions of sets in a compact system. -/
def union (p : Set α → Prop) : Set α → Prop :=
  (sUnion '' ({ L : Set (Set α) | L.Finite ∧ ∀ K ∈ L, p K}))

namespace union

lemma mem_iff (s : Set α) : union p s ↔ ∃ L : Finset (Set α), s = ⋃₀ L ∧ ∀ K ∈ L, p K := by
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

theorem isCompactSystem (p : Set α → Prop)(hp : IsCompactSystem p) : IsCompactSystem (union p) := by
  have hp' := (IsCompactSystem.iff_of_not_empty p).mp hp
  rw [IsCompactSystem.iff_of_not_empty]
  intro C hi
  simp_rw [mem_iff] at hi
  choose L' hL' using hi
  have hL'1 := fun n ↦ (hL' n).1
  have hL'2 := fun n ↦ (hL' n).2
  simp_rw [hL'1]
  intro hL
  let K := mem_of_union L' hL
  have h₁ : ⋂ i, K i ⊆ ⋂ i, ⋃₀ (L' i).toSet := by
    apply mem_of_union.isSubsetN0 L'
  have h₂ : ⋂ i, K i ≠ ∅ := by
    apply hp' _
    · apply mem_of_union.has_p
      exact hL'2
    · apply mem_of_union.prop₁N0
  rw [← nonempty_iff_ne_empty] at h₂ ⊢
  exact Nonempty.mono h₁ h₂

end union

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

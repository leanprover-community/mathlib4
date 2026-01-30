/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.OuterMeasure.Induced
public import Mathlib.Tactic.FinCases

/-!
# Additive Contents

An additive content `m` on a set of sets `C` is a set function with value 0 at the empty set which
is finitely additive on `C`. That means that for any finset `I` of pairwise disjoint sets in `C`
such that `⋃₀ I ∈ C`, `m (⋃₀ I) = ∑ s ∈ I, m s`.

Mathlib also has a definition of contents over compact sets: see `MeasureTheory.Content`.
A `Content` is in particular an `AddContent` on the set of compact sets.

## Main definitions

* `MeasureTheory.AddContent G C`: additive contents over the set of sets `C` taking values in the
  additive monoid `G`.
* `MeasureTheory.AddContent.IsSigmaSubadditive`: an `AddContent` with values in `ℝ≥0∞` is
  σ-subadditive if `m (⋃ i, f i) ≤ ∑' i, m (f i)` for any sequence of sets `f` in `C`
  such that `⋃ i, f i ∈ C`.

## Main statements

Let `m` be an `AddContent C` with values in `ℝ≥0∞`. If `C` is a set semi-ring (`IsSetSemiring C`)
we have the properties

* `MeasureTheory.sum_addContent_le_of_subset`: if `I` is a finset of pairwise disjoint sets in `C`
  and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`.
* `MeasureTheory.addContent_mono`: if `s ⊆ t` for two sets in `C`, then `m s ≤ m t`.
* `MeasureTheory.addContent_sUnion_le_sum`: an `AddContent C` on a `SetSemiring C` is
  sub-additive.
* `MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le`: if an
  `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive.
* `MeasureTheory.addContent_union'`: if `s, t ∈ C` are disjoint and `s ∪ t ∈ C`,
  then `m (s ∪ t) = m s + m t`.
  If `C` is a set ring (`IsSetRing`), then `addContent_union` gives the same conclusion without the
  hypothesis `s ∪ t ∈ C` (since it is a consequence of `IsSetRing C`).

If `C` is a set ring (`MeasureTheory.IsSetRing C`), we have

* `MeasureTheory.addContent_union_le`: for `s, t ∈ C`, `m (s ∪ t) ≤ m s + m t`
* `MeasureTheory.addContent_le_diff`: for `s, t ∈ C`, `m s - m t ≤ m (s \ t)`
* `IsSetRing.addContent_of_union`: a function on a ring of sets which is additive on pairs of
  disjoint sets defines an additive content
* `addContent_iUnion_eq_sum_of_tendsto_zero`: if an additive content is continuous at `∅`, then
  its value on a countable disjoint union is the sum of the values
* `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum`: if an `AddContent` is
  σ-additive on a set ring, then it is σ-subadditive.

We define a specific example of `AddContent`, called `AddContent.onIoc`, on the semiring of sets
made of open-closed intervals, mapping `(a, b]` to `f b - f a`.
-/

@[expose] public section

open Set Finset Function Filter

open scoped ENNReal Topology Function

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}
{G : Type*} [AddCommMonoid G]

variable (G) in
/-- An additive content is a set function with value 0 at the empty set which is finitely additive
on a given set of sets. -/
structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α → G
  empty' : toFun ∅ = 0
  sUnion' (I : Finset (Set α)) (_h_ss : ↑I ⊆ C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I ∈ C) :
    toFun (⋃₀ I) = ∑ u ∈ I, toFun u

instance : Inhabited (AddContent G C) :=
  ⟨{toFun := fun _ => 0
    empty' := by simp
    sUnion' := by simp }⟩

instance : FunLike (AddContent G C) (Set α) G where
  coe m s := m.toFun s
  coe_injective' m m' _ := by
    cases m
    cases m'
    congr

variable {m m' : AddContent G C}

@[ext] protected lemma AddContent.ext (h : ∀ s, m s = m' s) : m = m' :=
  DFunLike.ext _ _ h

@[simp] lemma addContent_empty : m ∅ = 0 := m.empty'

lemma addContent_sUnion (h_ss : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u ∈ I, m u :=
  m.sUnion' I h_ss h_dis h_mem

lemma addContent_biUnion {ι : Type*} {a : Finset ι} {f : ι → Set α} (hf : ∀ i ∈ a, f i ∈ C)
    (h_dis : PairwiseDisjoint ↑a f) (h_mem : ⋃ i ∈ a, f i ∈ C) :
    m (⋃ i ∈ a, f i) = ∑ i ∈ a, m (f i) := by
  classical
  have A : ⋃ i ∈ a, f i = ⋃₀ (a.image f) := by simp
  rw [A, addContent_sUnion]; rotate_left
  · grind
  · simpa using h_dis.image
  · rwa [← A]
  rw [sum_image_of_pairwise_eq_zero]
  refine h_dis.imp ?_
  grind [Set.bot_eq_empty (α := α), addContent_empty]

lemma addContent_iUnion {ι : Type*} [Fintype ι] {f : ι → Set α} (hf : ∀ i, f i ∈ C)
    (h_dis : Pairwise (Disjoint on f)) (h_mem : ⋃ i, f i ∈ C) :
    m (⋃ i, f i) = ∑ i, m (f i) := by
  convert addContent_biUnion (a := Finset.univ) (f := f) (m := m) ?_ ?_ ?_ using 1
  · simp
  · simpa
  · simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using h_dis
  · simpa

lemma addContent_union' (hs : s ∈ C) (ht : t ∈ C) (hst : s ∪ t ∈ C) (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t := by
  have A : s ∪ t = ⋃ i, ![s, t] i := by ext; simp
  convert addContent_iUnion (f := ![s, t]) (m := m) (fun i ↦ ?_) (fun i j hij ↦ ?_) ?_ using 2
  · simp [Fin.univ_castSuccEmb, add_comm]
  · fin_cases i <;> simpa
  · fin_cases i <;> fin_cases j <;> grind
  · rwa [← A]

/-- An additive content with values in `ℝ≥0∞` is said to be sigma-sub-additive if for any sequence
of sets `f` in `C` such that `⋃ i, f i ∈ C`, we have `m (⋃ i, f i) ≤ ∑' i, m (f i)`. -/
def AddContent.IsSigmaSubadditive (m : AddContent ℝ≥0∞ C) : Prop :=
  ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C), m (⋃ i, f i) ≤ ∑' i, m (f i)

section IsSetSemiring

lemma addContent_eq_add_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    m s = ∑ i ∈ I, m i + ∑ i ∈ hC.disjointOfDiffUnion hs hI, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]
  rw [addContent_sUnion]
  · rw [sum_union]
    exact hC.disjoint_disjointOfDiffUnion hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.disjointOfDiffUnion_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_disjointOfDiffUnion hs hI h_dis
  · rwa [hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]

/-- For an `m : addContent C` on a `SetSemiring C` and `s t : Set α` with `s ⊆ t`, we can write
`m t = m s + ∑ i in hC.disjointOfDiff ht hs, m i`. -/
theorem eq_add_disjointOfDiff_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) :
    m t = m s + ∑ i ∈ hC.disjointOfDiff ht hs, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_insert_disjointOfDiff ht hs hst]
  rw [← coe_insert, addContent_sUnion]
  · rw [sum_insert]
    exact hC.notMem_disjointOfDiff ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.subset_disjointOfDiff ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_disjointOfDiff ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_disjointOfDiff ht hs hst]

/-- If a set can be written in two different ways as a disjoint union of elements of a semi-ring
of sets `C`, then the sums of the values of `m : addContent C` along the two decompositions give
the same result.
In other words, `m` can be canonically extended to finite unions of elements of `C`. -/
theorem sum_addContent_eq_of_sUnion_eq (hC : IsSetSemiring C) (J J' : Finset (Set α))
    (hJ : ↑J ⊆ C) (hJdisj : PairwiseDisjoint (J : Set (Set α)) id)
    (hJ' : ↑J' ⊆ C) (hJ'disj : PairwiseDisjoint (J' : Set (Set α)) id)
    (h : ⋃₀ (J : Set (Set α)) = ⋃₀ J') :
    ∑ s ∈ J, m s = ∑ t ∈ J', m t := by
  calc ∑ s ∈ J, m s
  _ = ∑ s ∈ J, (∑ t ∈ J', m (s ∩ t)) := by
    apply Finset.sum_congr rfl (fun s hs ↦ ?_)
    have : s = ⋃ t ∈ J', s ∩ t := by
      simp_rw [← Finset.set_biUnion_coe, ← inter_iUnion, left_eq_inter, ← sUnion_eq_biUnion, ← h]
      exact subset_sUnion_of_mem hs
    nth_rewrite 1 [this]
    apply addContent_biUnion
    · exact fun t ht ↦ hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJ'disj.mono fun _ ↦ by simp
    · rw [← this]
      exact hJ hs
  _ = ∑ t ∈ J', (∑ s ∈ J, m (s ∩ t)) := sum_comm
  _ = ∑ t ∈ J', m t := by
    apply Finset.sum_congr rfl (fun t ht ↦ ?_)
    have : t = ⋃ s ∈ J, s ∩ t := by
      simp_rw [← Finset.set_biUnion_coe, ← iUnion_inter, right_eq_inter, ← sUnion_eq_biUnion, h]
      exact subset_sUnion_of_mem ht
    nth_rewrite 2 [this]
    apply (addContent_biUnion _ _ _).symm
    · exact fun s hs ↦ hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJdisj.mono fun _ ↦ by simp
    · rw [← this]
      exact hJ' ht

open scoped Classical in
/-- Extend a content over `C` to the finite unions of elements of `C` by additivity.
Use instead `AddContent.supClosure` which is the same function bundled as an `AddContent`. -/
private noncomputable def AddContent.supClosureFun (m : AddContent G C) (s : Set α) : G :=
  if h : ∃ (J : Finset (Set α)), ↑J ⊆ C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J
    then ∑ s ∈ h.choose, m s
  else 0

private lemma AddContent.supClosureFun_apply (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finset (Set α)}
    (hJ : ↑J ⊆ C) (h'J : PairwiseDisjoint (J : Set (Set α)) id) (hs : s = ⋃₀ ↑J) :
    m.supClosureFun s = ∑ s ∈ J, m s := by
  have h : ∃ (J : Finset (Set α)), ↑J ⊆ C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J :=
    ⟨J, hJ, h'J, hs⟩
  simp only [supClosureFun, h, ↓reduceDIte]
  apply sum_addContent_eq_of_sUnion_eq hC _ _ h.choose_spec.1 h.choose_spec.2.1 hJ h'J
  rw [← hs]
  exact h.choose_spec.2.2.symm

private lemma AddContent.supClosureFun_apply_of_mem (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} (hs : s ∈ C) :
    m.supClosureFun s = m s := by
  have : m.supClosureFun s = ∑ t ∈ {s}, m t :=
    m.supClosureFun_apply hC (by simp [hs]) (by simp) (by simp)
  simp [this]

/-- Extend a content over `C` to the finite unions of elements of `C` by additivity. -/
@[no_expose] noncomputable def AddContent.supClosure (m : AddContent G C) (hC : IsSetSemiring C) :
    AddContent G (supClosure C) where
  toFun := m.supClosureFun
  empty' := by rw [m.supClosureFun_apply_of_mem hC hC.empty_mem, addContent_empty]
  sUnion' I hI h'I hh'I := by
    classical
    have A (s) (hs : s ∈ I) : ∃ (J : Finset (Set α)),
        ↑J ⊆ C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J := by
      obtain ⟨P, PC⟩ : ∃ (P : Finpartition s), ↑P.parts ⊆ C := by
        have := hI hs
        rwa [hC.mem_supClosure_iff] at this
      refine ⟨P.parts, PC, P.disjoint, ?_⟩
      convert P.sup_parts.symm
      simp [sUnion_eq_biUnion]
    choose! J hJC hJdisj hJs using A
    have H {a i} (hi : i ∈ I) (ha : a ∈ J i) : a ⊆ i := by
      rw [hJs i hi]
      exact subset_sUnion_of_mem ha
    let K : Finset (Set α) := Finset.biUnion I J
    have : ⋃₀ ↑I = ⋃₀ (↑K : Set (Set α)) := by
      simp [K, sUnion_eq_biUnion] at hJs ⊢; grind
    rw [this, m.supClosureFun_apply hC (J := K) (by simpa [K] using hJC) _ rfl]; swap
    · simp only [K, coe_biUnion]
      refine (h'I.mono_on ?_).biUnion hJdisj
      simp
      grind
    simp only [K]
    rw [sum_biUnion_of_pairwise_eq_zero]; swap
    · intro i hi j hj hij k hk
      simp only [Finset.mem_inter] at hk
      have : Disjoint k k := by
        have : Disjoint i j := h'I hi hj hij
        exact this.mono (H hi hk.1) (H hj hk.2)
      simp only [disjoint_self, Set.bot_eq_empty] at this
      simp [this]
    apply Finset.sum_congr rfl (fun i hi ↦ Eq.symm ?_)
    exact m.supClosureFun_apply hC (hJC i hi) (hJdisj i hi) (hJs i hi)

lemma AddContent.supClosure_apply (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finset (Set α)}
    (hJ : ↑J ⊆ C) (h'J : PairwiseDisjoint (J : Set (Set α)) id) (hs : s = ⋃₀ ↑J) :
    m.supClosure hC s = ∑ s ∈ J, m s :=
  m.supClosureFun_apply hC hJ h'J hs

lemma AddContent.supClosure_apply_finpartition (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finpartition s} (hJ : ↑J.parts ⊆ C) :
    m.supClosure hC s = ∑ s ∈ J.parts, m s := by
  rw [m.supClosure_apply _ hJ J.disjoint]
  nth_rewrite 1 [← J.sup_parts, Finset.sup_set_eq_biUnion, sUnion_eq_biUnion]
  rfl

lemma AddContent.supClosure_apply_of_mem (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} (hs : s ∈ C) :
    m.supClosure hC s = m s :=
  m.supClosureFun_apply_of_mem hC hs

variable [PartialOrder G] [CanonicallyOrderedAdd G]

/-- For an `m : addContent C` on a `SetSemiring C`, if `I` is a `Finset` of pairwise disjoint
  sets in `C` and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`. -/
lemma sum_addContent_le_of_subset (hC : IsSetSemiring C)
    (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (ht : t ∈ C) (hJt : ∀ s ∈ I, s ⊆ t) :
    ∑ u ∈ I, m u ≤ m t := by
  classical
  rw [addContent_eq_add_disjointOfDiffUnion_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

/-- An `addContent C` on a `SetSemiring C` is monotone. -/
lemma addContent_mono (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    (hst : s ⊆ t) :
    m s ≤ m t := by
  have h := sum_addContent_le_of_subset (m := m) hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp [hst]

/-- An `addContent C` on a `SetSemiring C` is sub-additive. -/
lemma addContent_sUnion_le_sum {m : AddContent G C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u ∈ J, m u := by
  classical
  have h1 : (disjiUnion J (hC.disjointOfUnion h_ss)
      (hC.pairwiseDisjoint_disjointOfUnion h_ss) : Set (Set α)) ⊆ C := by
    simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe, iUnion_subset_iff]
    exact fun _ x ↦ hC.disjointOfUnion_subset h_ss x
  have h2 : PairwiseDisjoint (disjiUnion J (hC.disjointOfUnion h_ss)
      ((hC.pairwiseDisjoint_disjointOfUnion h_ss)) : Set (Set α)) id := by
    simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe]
    exact hC.pairwiseDisjoint_biUnion_disjointOfUnion h_ss
  have h3 : ⋃₀ J = ⋃₀ ((disjiUnion J (hC.disjointOfUnion h_ss)
      (hC.pairwiseDisjoint_disjointOfUnion h_ss)) : Set (Set α)) := by
    simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe]
    exact (Exists.choose_spec (hC.disjointOfUnion_props h_ss)).2.2.2.2.2
  rw [h3, addContent_sUnion h1 h2, sum_disjiUnion]
  · gcongr with x hx
    refine sum_addContent_le_of_subset hC (hC.disjointOfUnion_subset h_ss hx)
      (hC.pairwiseDisjoint_disjointOfUnion_of_mem h_ss hx) (h_ss hx)
      (fun _ s ↦ hC.subset_of_mem_disjointOfUnion h_ss hx s)
  · simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe] at *
    exact h3.symm ▸ h_mem

lemma addContent_le_sum_of_subset_sUnion {m : AddContent G C} (hC : IsSetSemiring C)
    {J : Finset (Set α)} (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u ∈ J, m u := by
  -- we can't apply `addContent_mono` and `addContent_sUnion_le_sum` because `⋃₀ ↑J` might not
  -- be in `C`
  classical
  let Jt := J.image (fun u ↦ t ∩ u)
  have ht_eq : t = ⋃₀ Jt := by
    rw [coe_image, sUnion_image, ← inter_iUnion₂, inter_eq_self_of_subset_left]
    rwa [← sUnion_eq_biUnion]
  rw [ht_eq]
  refine (addContent_sUnion_le_sum hC Jt ?_ ?_).trans ?_
  · intro s
    simp only [Jt, coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp]
    rintro u hu rfl
    exact hC.inter_mem _ ht _ (h_ss hu)
  · rwa [← ht_eq]
  · refine (Finset.sum_image_le_of_nonneg fun _ _ ↦ zero_le _).trans (sum_le_sum fun u hu ↦ ?_)
    exact addContent_mono hC (hC.inter_mem _ ht _ (h_ss hu)) (h_ss hu) inter_subset_right

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddContent ℝ≥0∞ C}
    (hC : IsSetSemiring C)
    -- TODO: `m_subadd` is in fact equivalent to `m.IsSigmaSubadditive`.
    (m_subadd : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : ⋃ i, f i ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine ENNReal.summable.tsum_le_of_sum_le fun I ↦ ?_
  classical
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ ↦ subset_iUnion _ i

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive {m : AddContent ℝ≥0∞ C}
    (hC : IsSetSemiring C) (m_subadd : m.IsSigmaSubadditive)
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) :=
  addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le hC
    (fun _ hf hf_Union _ ↦ m_subadd hf hf_Union) f hf hf_Union hf_disj

end IsSetSemiring

section OnIoc

variable [LinearOrder α] {G : Type*} [AddCommGroup G]

open scoped Classical in
/-- The function associating to an interval `Ioc u v` the difference `f v - f u`.
Use instead `AddContent.ofIoc` which upgrades this function to an additive content. -/
noncomputable def AddContent.onIocAux (f : α → G) (s : Set α) : G :=
  if h : ∃ (p : α × α), p.1 ≤ p.2 ∧ s = Set.Ioc p.1 p.2
    then f h.choose.2 - f h.choose.1 else 0

lemma AddContent.onIocAux_apply {f : α → G} {u v : α} (h : u ≤ v) :
    AddContent.onIocAux f (Ioc u v) = f v - f u := by
  have h' : ∃ (p : α × α), p.1 ≤ p.2 ∧ Ioc u v = Ioc p.1 p.2 := ⟨(u, v), h, rfl⟩
  simp only [onIocAux, h', ↓reduceDIte]
  set u' := h'.choose.1
  set v' := h'.choose.2
  have hu'v' : u' ≤ v' ∧ Ioc u v = Ioc u' v' := h'.choose_spec
  rcases h.eq_or_lt with rfl | huv
  · grind [Set.Ioc_eq_empty_iff]
  rw [Ioc_eq_Ioc_iff (Or.inl huv)] at hu'v'
  grind

lemma AddContent.onIocAux_empty (f : α → G) :
    AddContent.onIocAux f ∅ = 0 := by
  classical
  rw [onIocAux, dite_eq_right_iff]
  grind [Set.Ioc_eq_empty_iff]

/-- The additive content on the set of open-closed intervals, associating to an interval `Ioc u v`
the difference `f v - f u`. -/
noncomputable def AddContent.onIoc (f : α → G) :
    AddContent G {s : Set α | ∃ u v, u ≤ v ∧ s = Set.Ioc u v} where
  toFun := AddContent.onIocAux f
  empty' := AddContent.onIocAux_empty f
  sUnion' := by
    classical
    /- Consider a finite union of open-closed intervals whose union is again an open-closed
    interval `(u, v]`. We have to show that the sum of `f b - f a` over the intervals gives
    `f v - f u`. Informally, `(u, v]` is an ordered
    union `(a₀, a₁] ∪ (a₁, a₂] ∪ ... ∪ (a_{n-1}, aₙ]` and there is a telescoping sum.
    For the formal argument, we argue by induction on the number of intervals, and remove the
    right-most one (i.e., the one that contains `v`) to reduce to one interval less. Denoting
    this right-most interval by `(u', v]`, then the union of the other intervals
    is exactly `(u, u']`. From this and the induction assumption, the conclusion follows. -/
    intro I hI h'I h''I
    induction hn : Finset.card I generalizing I with
    | zero =>
      have : I = ∅ := by grind
      simp [this, onIocAux_empty f]
    | succ n ih =>
      rcases h''I with ⟨u, v, huv, h'uv⟩
      -- If the interval `(u, v]` is empty, i.e., `u = v`, then the result is easy.
      rcases huv.eq_or_lt with rfl | huv
      · have : onIocAux f (Set.Ioc u u) = ∑ u ∈ I, 0 := by simp [onIocAux_empty f]
        rw [h'uv, this]
        apply Finset.sum_congr rfl fun i hi ↦ ?_
        have : i = ∅ := by grind [sUnion_eq_empty]
        grind [onIocAux_empty]
      -- otherwise, `v` is in `(u, v]`, therefore it belongs to some interval `(u', v']`
      -- featuring in the union.
      have : v ∈ ⋃₀ ↑I := by simp [h'uv, huv]
      obtain ⟨t, tI, ht⟩ : ∃ t ∈ I, v ∈ t := by simpa using this
      rcases hI tI with ⟨u', v', hu'v', rfl⟩
      -- we have `u ≤ u'` and `v' = v` since `(u', v']` is part of the union, and therefore
      -- contained in `(u, v]`.
      have ⟨_, uu'⟩ : v' ≤ v ∧ u ≤ u' := (Ioc_subset_Ioc_iff (by grind)).1 (by grind)
      obtain rfl : v = v' := by grind
      rw [h'uv, onIocAux_apply huv.le]
      -- let us remove the right-most interval `(u', v]` from the union, and let `I'` be the
      -- remaining set of intervals.
      let I' := I.erase (Set.Ioc u' v)
      have I'I : I' ⊆ I := erase_subset (Set.Ioc u' v) I
      have I_eq_insert : I = insert (Set.Ioc u' v) I' := by simp [I', tI]
      -- the intervals in `I'` cover exactly `(u, u']`.
      have UI' : ⋃₀ ↑I' = Ioc u u' := by
        have : (Ioc u' v ∪ ⋃₀ ↑I') \ Ioc u' v = ⋃₀ ↑I' := by
          refine Disjoint.sup_sdiff_cancel_left ?_
          simp only [coe_erase, disjoint_sUnion_right, mem_diff, mem_singleton_iff, and_imp, I']
          intro u hu hu'
          exact (h'I hu tI hu').symm
        simp only [I_eq_insert, coe_insert, sUnion_insert] at h'uv
        grind
      -- by the inductive assumption, the sum over `I'` is exactly `f u' - f u`.
      have IH : onIocAux f (⋃₀ ↑I') = ∑ u ∈ I', onIocAux f u :=
        ih _ (Subset.trans I'I hI) (h'I.subset I'I) (by grind) (by grind)
      -- the conclusion follows.
      rw [I_eq_insert, sum_insert, ← IH, UI', onIocAux_apply hu'v', onIocAux_apply uu']
      · simp
      · simp [I']

lemma AddContent.onIoc_apply {f : α → G} {u v : α} (h : u ≤ v) :
    AddContent.onIoc f (Ioc u v) = f v - f u :=
  AddContent.onIocAux_apply h

end OnIoc

section AddContentExtend

/-- An additive content obtained from another one on the same semiring of sets by setting the value
of each set not in the semiring at `∞`. -/
protected noncomputable
def AddContent.extend (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) : AddContent ℝ≥0∞ C where
  toFun := extend (fun x (_ : x ∈ C) ↦ m x)
  empty' := by rw [extend_eq, addContent_empty]; exact hC.empty_mem
  sUnion' I h_ss h_dis h_mem := by
    rw [extend_eq]
    swap; · exact h_mem
    rw [addContent_sUnion h_ss h_dis h_mem]
    refine Finset.sum_congr rfl (fun s hs ↦ ?_)
    rw [extend_eq]
    exact h_ss hs

protected theorem AddContent.extend_eq_extend (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) :
    m.extend hC = extend (fun x (_ : x ∈ C) ↦ m x) := rfl

protected theorem AddContent.extend_eq (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) (hs : s ∈ C) :
    m.extend hC s = m s := by
  rwa [m.extend_eq_extend, extend_eq]

protected theorem AddContent.extend_eq_top
    (hC : IsSetSemiring C) (m : AddContent ℝ≥0∞ C) (hs : s ∉ C) :
    m.extend hC s = ∞ := by
  rwa [m.extend_eq_extend, extend_eq_top]

end AddContentExtend

section IsSetRing

lemma addContent_union (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C)
    (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t :=
  addContent_union' hs ht (hC.union_mem hs ht) h_dis

lemma addContent_biUnion_eq {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    {S : Finset ι} (hs : ∀ n ∈ S, s n ∈ C) (hS : (S : Set ι).PairwiseDisjoint s) :
    m (⋃ i ∈ S, s i) = ∑ i ∈ S, m (s i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simp only [Finset.coe_insert, Set.pairwiseDisjoint_insert] at hS
    rw [← h hs.2 hS.1]
    refine addContent_union hC hs.1 (hC.biUnion_mem S hs.2) ?_
    rw [disjoint_iUnion₂_right]
    exact fun j hjS ↦ hS.2 j hjS (ne_of_mem_of_not_mem hjS hiS).symm

lemma addContent_accumulate (m : AddContent G C) (hC : IsSetRing C)
    {s : ℕ → Set α} (hs_disj : Pairwise (Disjoint on s)) (hsC : ∀ i, s i ∈ C) (n : ℕ) :
      m (Set.accumulate s n) = ∑ i ∈ Finset.range (n + 1), m (s i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, ← hn, Set.accumulate_succ, addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

/-- A function which is additive on disjoint elements in a ring of sets `C` defines an
additive content on `C`. -/
def IsSetRing.addContent_of_union (m : Set α → G) (hC : IsSetRing C) (m_empty : m ∅ = 0)
    (m_add : ∀ {s t : Set α} (_hs : s ∈ C) (_ht : t ∈ C), Disjoint s t → m (s ∪ t) = m s + m t) :
    AddContent G C where
  toFun := m
  empty' := m_empty
  sUnion' I h_ss h_dis h_mem := by
    classical
    induction I using Finset.induction with
    | empty => simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
    | insert s I hsI h =>
      rw [Finset.coe_insert] at *
      rw [Set.insert_subset_iff] at h_ss
      rw [Set.pairwiseDisjoint_insert_of_notMem] at h_dis
      swap; · exact hsI
      have h_sUnion_mem : ⋃₀ ↑I ∈ C := by
        rw [Set.sUnion_eq_biUnion]
        apply hC.biUnion_mem
        intro n hn
        exact h_ss.2 hn
      rw [Set.sUnion_insert, m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2),
        Finset.sum_insert hsI, h h_ss.2 h_dis.1]
      rwa [Set.sUnion_insert] at h_mem

variable [PartialOrder G] [CanonicallyOrderedAdd G]

lemma addContent_union_le (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m (s ∪ t) ≤ m s + m t := by
  rw [← union_diff_self, addContent_union hC hs (hC.diff_mem ht hs)]
  · exact add_le_add le_rfl
      (addContent_mono hC.isSetSemiring (hC.diff_mem ht hs) ht diff_subset)
  · rw [Set.disjoint_iff_inter_eq_empty, inter_diff_self]

lemma addContent_biUnion_le {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    {S : Finset ι} (hs : ∀ n ∈ S, s n ∈ C) :
    m (⋃ i ∈ S, s i) ≤ ∑ i ∈ S, m (s i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (addContent_union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)

lemma le_addContent_diff (m : AddContent ℝ≥0∞ C) (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m s - m t ≤ m (s \ t) := by
  conv_lhs => rw [← inter_union_diff s t]
  rw [addContent_union hC (hC.inter_mem hs ht) (hC.diff_mem hs ht) disjoint_inf_sdiff, add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le
    (addContent_mono hC.isSetSemiring (hC.inter_mem hs ht) ht inter_subset_right), add_zero]

lemma addContent_diff_of_ne_top (m : AddContent ℝ≥0∞ C) (hC : IsSetRing C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    {s t : Set α} (hs : s ∈ C) (ht : t ∈ C) (hts : t ⊆ s) :
    m (s \ t) = m s - m t := by
  have h_union : m (t ∪ s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.diff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_diff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union, ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

/-- In a ring of sets, continuity of an additive content at `∅` implies σ-additivity.
This is not true in general in semirings, or without the hypothesis that `m` is finite. See the
examples 7 and 8 in Halmos' book Measure Theory (1974), page 40. -/
theorem addContent_iUnion_eq_sum_of_tendsto_zero (hC : IsSetRing C) (m : AddContent ℝ≥0∞ C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    (hm_tendsto : ∀ ⦃s : ℕ → Set α⦄ (_ : ∀ n, s n ∈ C),
      Antitone s → (⋂ n, s n) = ∅ → Tendsto (fun n ↦ m (s n)) atTop (𝓝 0))
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hUf : (⋃ i, f i) ∈ C)
    (h_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (set.accumulate f n)`
  let s : ℕ → Set α := fun n ↦ (⋃ i, f i) \ Set.accumulate f n
  have hCs n : s n ∈ C := hC.diff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n ↦ m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_diff] at hxj ⊢
      exact ⟨hxj.1, fun hxi ↦ hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.diff_eq]
      rw [Set.iInter_inter_distrib, Set.iInter_const, ← Set.compl_iUnion, Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i ∈ Finset.range (n + 1), m (f i) := by
    rw [addContent_diff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _), addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum fun i ↦ m (f i))
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  rwa [ENNReal.tendsto_const_sub_nhds_zero_iff (hm_ne_top _ hUf) (fun n ↦ ?_)] at h_tendsto
  rw [← addContent_accumulate m hC h_disj hf]
  exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
    (Set.accumulate_subset_iUnion _)

/-- If an additive content is σ-additive on a set ring, then the content of a monotone sequence of
sets tends to the content of the union. -/
theorem tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
    {m : AddContent ℝ≥0∞ C} (hC : IsSetRing C)
    (m_iUnion : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    ⦃f : ℕ → Set α⦄ (hf_mono : Monotone f) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C) :
    Tendsto (fun n ↦ m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  rw [← iUnion_disjointed, m_iUnion _ (hC.disjointed_mem hf) (by rwa [iUnion_disjointed])
      (disjoint_disjointed f)]
  have h n : m (f n) = ∑ i ∈ range (n + 1), m (disjointed f i) := by
    nth_rw 1 [← addContent_accumulate _ hC (disjoint_disjointed f) (hC.disjointed_mem hf),
    ← hf_mono.partialSups_eq, ← partialSups_disjointed, partialSups_eq_biSup, accumulate]
    rfl
  simp_rw [h]
  refine (tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i ∈ range k, m (disjointed f i))) 1).2 ?_
  exact ENNReal.tendsto_nat_tsum _

/-- If an additive content is σ-additive on a set ring, then it is σ-subadditive. -/
theorem isSigmaSubadditive_of_addContent_iUnion_eq_tsum {m : AddContent ℝ≥0∞ C} (hC : IsSetRing C)
    (m_iUnion : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i)) :
    m.IsSigmaSubadditive := by
  intro f hf hf_Union
  have h_tendsto : Tendsto (fun n ↦ m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion, ← iSup_partialSups_eq]
    refine tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum hC m_iUnion
      (partialSups_monotone f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' : Tendsto (fun n ↦ ∑ i ∈ range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i ∈ range k, m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun _ ↦ ?_
  rw [partialSups_eq_biUnion_range]
  exact addContent_biUnion_le hC (fun _ _ ↦ hf _)

end IsSetRing

end MeasureTheory

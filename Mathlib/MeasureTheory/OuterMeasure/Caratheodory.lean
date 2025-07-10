/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.OuterMeasure.OfFunction
import Mathlib.MeasureTheory.PiSystem

/-!
# The Caratheodory σ-algebra of an outer measure

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `MeasureTheory.OuterMeasure.caratheodory` is the Carathéodory-measurable space
  of an outer measure.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

Carathéodory-measurable, Carathéodory's criterion

-/

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section CaratheodoryMeasurable

universe u

variable {α : Type u} (m : OuterMeasure α)

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable {s s₁ s₂ : Set α}

/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
def IsCaratheodory (s : Set α) : Prop :=
  ∀ t, m t = m (t ∩ s) + m (t \ s)

theorem isCaratheodory_iff_le' {s : Set α} :
    IsCaratheodory m s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  forall_congr' fun _ => le_antisymm_iff.trans <| and_iff_right <| measure_le_inter_add_diff _ _ _

@[simp]
theorem isCaratheodory_empty : IsCaratheodory m ∅ := by simp [IsCaratheodory, diff_empty]

theorem isCaratheodory_compl : IsCaratheodory m s₁ → IsCaratheodory m s₁ᶜ := by
  simp [IsCaratheodory, diff_eq, add_comm]

@[simp]
theorem isCaratheodory_compl_iff : IsCaratheodory m sᶜ ↔ IsCaratheodory m s :=
  ⟨fun h => by simpa using isCaratheodory_compl m h, isCaratheodory_compl m⟩

theorem isCaratheodory_union (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ ∪ s₂) := fun t => by
  rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)), inter_diff_assoc _ _ s₁,
    Set.inter_assoc _ _ s₁, inter_eq_self_of_subset_right Set.subset_union_left,
    union_diff_left, h₂ (t ∩ s₁)]
  simp [diff_eq, add_assoc]

variable {m} in
lemma IsCaratheodory.biUnion_of_finite {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Finite)
    (h : ∀ i ∈ t, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i ∈ t, s i) := by
  classical
  lift t to Finset ι using ht
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    simp only [Finset.mem_coe, Finset.mem_insert, iUnion_iUnion_eq_or_left] at h ⊢
    exact m.isCaratheodory_union (h _ <| Or.inl rfl) (IH fun _ hj ↦ h _ <| Or.inr hj)

theorem measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : IsCaratheodory m s₁) {t : Set α} :
    m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁) + m (t ∩ s₂) := by
  rw [h₁, Set.inter_assoc, Set.union_inter_cancel_left, inter_diff_assoc, union_diff_cancel_left h]

theorem isCaratheodory_iUnion_lt {s : ℕ → Set α} :
    ∀ {n : ℕ}, (∀ i < n, IsCaratheodory m (s i)) → IsCaratheodory m (⋃ i < n, s i)
  | 0, _ => by simp
  | n + 1, h => by
    rw [biUnion_lt_succ]
    exact isCaratheodory_union m
            (isCaratheodory_iUnion_lt fun i hi => h i <| lt_of_lt_of_le hi <| Nat.le_succ _)
            (h n (le_refl (n + 1)))

theorem isCaratheodory_inter (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ ∩ s₂) := by
  rw [← isCaratheodory_compl_iff, Set.compl_inter]
  exact isCaratheodory_union _ (isCaratheodory_compl _ h₁) (isCaratheodory_compl _ h₂)

lemma isCaratheodory_diff (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ \ s₂) := m.isCaratheodory_inter h₁ (m.isCaratheodory_compl h₂)

lemma isCaratheodory_partialSups {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {s : ι → Set α} (h : ∀ i, m.IsCaratheodory (s i)) (i : ι) :
    m.IsCaratheodory (partialSups s i) := by
  simpa only [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion, ← Finset.mem_coe,
    Finset.coe_Iic] using .biUnion_of_finite (finite_Iic _) (fun j _ ↦ h j)

lemma isCaratheodory_disjointed {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {s : ι → Set α} (h : ∀ i, m.IsCaratheodory (s i)) (i : ι) :
    m.IsCaratheodory (disjointed s i) :=
  disjointedRec (fun _ j ht ↦ m.isCaratheodory_diff ht <| h j) (h i)

theorem isCaratheodory_sum {s : ℕ → Set α} (h : ∀ i, IsCaratheodory m (s i))
    (hd : Pairwise (Disjoint on s)) {t : Set α} :
    ∀ {n}, (∑ i ∈ Finset.range n, m (t ∩ s i)) = m (t ∩ ⋃ i < n, s i)
  | 0 => by simp
  | Nat.succ n => by
    rw [biUnion_lt_succ, Finset.sum_range_succ, Set.union_comm, isCaratheodory_sum h hd,
      m.measure_inter_union _ (h n), add_comm]
    intro a
    simpa using fun (h₁ : a ∈ s n) i (hi : i < n) h₂ => (hd (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩

/-- Use `isCaratheodory_iUnion` instead, which does not require the disjoint assumption. -/
theorem isCaratheodory_iUnion_of_disjoint {s : ℕ → Set α} (h : ∀ i, IsCaratheodory m (s i))
    (hd : Pairwise (Disjoint on s)) : IsCaratheodory m (⋃ i, s i) := by
      apply (isCaratheodory_iff_le' m).mpr
      intro t
      have hp : m (t ∩ ⋃ i, s i) ≤ ⨆ n, m (t ∩ ⋃ i < n, s i) := by
        convert measure_iUnion_le (μ := m) fun i => t ∩ s i using 1
        · simp [inter_iUnion]
        · simp [ENNReal.tsum_eq_iSup_nat, isCaratheodory_sum m h hd]
      refine le_trans (add_le_add_right hp _) ?_
      rw [ENNReal.iSup_add]
      refine iSup_le fun n => le_trans (add_le_add_left ?_ _)
        (ge_of_eq (isCaratheodory_iUnion_lt m (fun i _ => h i) _))
      refine m.mono (diff_subset_diff_right ?_)
      exact iUnion₂_subset fun i _ => subset_iUnion _ i

lemma isCaratheodory_iUnion {s : ℕ → Set α} (h : ∀ i, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact m.isCaratheodory_iUnion_of_disjoint (m.isCaratheodory_disjointed h)
    (disjoint_disjointed _)

theorem f_iUnion {s : ℕ → Set α} (h : ∀ i, IsCaratheodory m (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) := by
  refine le_antisymm (measure_iUnion_le s) ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have := @isCaratheodory_sum _ m _ h hd univ n
  simp only [inter_comm, inter_univ, univ_inter] at this; simp only [this]
  exact m.mono (iUnion₂_subset fun i _ => subset_iUnion _ i)

/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system. -/
def caratheodoryDynkin : MeasurableSpace.DynkinSystem α where
  Has := IsCaratheodory m
  has_empty := isCaratheodory_empty m
  has_compl s := isCaratheodory_compl m s
  has_iUnion_nat _ hf hn := by apply isCaratheodory_iUnion m hf

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀ t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory : MeasurableSpace α := by
  apply MeasurableSpace.DynkinSystem.toMeasurableSpace (caratheodoryDynkin m)
  intro s₁ s₂
  apply isCaratheodory_inter

theorem isCaratheodory_iff {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ ∀ t, m t = m (t ∩ s) + m (t \ s) :=
  Iff.rfl

theorem isCaratheodory_iff_le {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  isCaratheodory_iff_le' m

protected theorem iUnion_eq_of_caratheodory {s : ℕ → Set α}
    (h : ∀ i, MeasurableSet[OuterMeasure.caratheodory m] (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  f_iUnion m h hd

end CaratheodoryMeasurable

variable {α : Type*}

theorem ofFunction_caratheodory {m : Set α → ℝ≥0∞} {s : Set α} {h₀ : m ∅ = 0}
    (hs : ∀ t, m (t ∩ s) + m (t \ s) ≤ m t) :
    MeasurableSet[(OuterMeasure.ofFunction m h₀).caratheodory] s := by
  apply (isCaratheodory_iff_le _).mpr
  refine fun t => le_iInf fun f => le_iInf fun hf => ?_
  refine
    le_trans
      (add_le_add ((iInf_le_of_le fun i => f i ∩ s) <| iInf_le _ ?_)
        ((iInf_le_of_le fun i => f i \ s) <| iInf_le _ ?_))
      ?_
  · rw [← iUnion_inter]
    exact inter_subset_inter_left _ hf
  · rw [← iUnion_diff]
    exact diff_subset_diff_left hf
  · rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun i => hs _

theorem boundedBy_caratheodory {m : Set α → ℝ≥0∞} {s : Set α}
    (hs : ∀ t, m (t ∩ s) + m (t \ s) ≤ m t) : MeasurableSet[(boundedBy m).caratheodory] s := by
  apply ofFunction_caratheodory; intro t
  rcases t.eq_empty_or_nonempty with h | h
  · simp [h, Set.not_nonempty_empty]
  · convert le_trans _ (hs t)
    · simp [h]
    exact add_le_add iSup_const_le iSup_const_le

@[simp]
theorem zero_caratheodory : (0 : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun _ _ _ => (add_zero _).symm

theorem top_caratheodory : (⊤ : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun s _ =>
    (isCaratheodory_iff_le _).2 fun t =>
      t.eq_empty_or_nonempty.elim (fun ht => by simp [ht]) fun ht => by
        simp only [ht, top_apply, le_top]

theorem le_add_caratheodory (m₁ m₂ : OuterMeasure α) :
    m₁.caratheodory ⊓ m₂.caratheodory ≤ (m₁ + m₂ : OuterMeasure α).caratheodory :=
  fun s ⟨hs₁, hs₂⟩ t => by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

theorem le_sum_caratheodory {ι} (m : ι → OuterMeasure α) :
    ⨅ i, (m i).caratheodory ≤ (sum m).caratheodory := fun s h t => by
  simp [fun i => MeasurableSpace.measurableSet_iInf.1 h i t, ENNReal.tsum_add]

theorem le_smul_caratheodory (a : ℝ≥0∞) (m : OuterMeasure α) :
    m.caratheodory ≤ (a • m).caratheodory := fun s h t => by
      simp only [smul_apply, smul_eq_mul]
      rw [(isCaratheodory_iff m).mp h t]
      simp [mul_add]

@[simp]
theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
  top_unique fun s _ t => by
    by_cases ht : a ∈ t; swap; · simp [ht]
    by_cases hs : a ∈ s <;> simp [*]

end OuterMeasure

end MeasureTheory

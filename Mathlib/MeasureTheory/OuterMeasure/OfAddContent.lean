/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Trim

/-!
# Caratheodorys extension theorem

## Main declarations

`Measure.ofAddContent`: Construct a measure from a sigma-subadditive content on a semiring,
assuming the semiring
generates a given measurable structure. The measure is defined on this measurable structure.

## Main results
* `inducedOuterMeasure_addContent_of_subadditive`:
A semiadditive content on a semiring induces an outer measure.
* `isCaratheodory_inducedOuterMeasure`: The Caratheodory measurable sets are at least members of
  the SetSemiring

-/

open Set

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)}

namespace OuterMeasure

section OfFunction

theorem ofFunction_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem _ _ m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hs_subset ↦ ?_
  calc m s = m (s ∩ ⋃ i, f i) := by rw [inter_eq_self_of_subset_left hs_subset]
    _ = m (⋃ i, s ∩ f i) := by rw [inter_iUnion]
    _ ≤ ∑' i, m (s ∩ f i) := by
      refine m_sigma_subadd (fun i ↦ hC.inter_mem _ hs _ (hf i)) ?_
      rwa [← inter_iUnion, inter_eq_self_of_subset_left hs_subset]
    _ ≤ ∑' i, m (f i) := by
      refine tsum_le_tsum (fun i ↦ ?_) ENNReal.summable ENNReal.summable
      exact addContent_mono hC (hC.inter_mem _ hs _ (hf i)) (hf i) Set.inter_subset_right

end OfFunction

end OuterMeasure

theorem inducedOuterMeasure_addContent_of_subadditive (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m s := by
  suffices inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m.extend hC s by
    rwa [m.extend_eq hC hs] at this
  refine Eq.trans ?_ (OuterMeasure.ofFunction_addContent_eq hC (m.extend hC) ?_ ?_ hs)
  · congr
  · intro f hf hf_mem
    rw [m.extend_eq hC hf_mem]
    refine (m_sigma_subadd hf hf_mem).trans_eq ?_
    congr with i
    rw [m.extend_eq hC (hf i)]
  · exact fun _ ↦ m.extend_eq_top _

theorem caratheodory_semiring_extension' (hC : IsSetSemiring C) (m : AddContent C)
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    (OuterMeasure.ofFunction m addContent_empty).IsCaratheodory s := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro t
  conv_rhs => rw [OuterMeasure.ofFunction_eq_iInf_mem _ _ m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hf_subset ↦ ?_
  let A : ℕ → Finset (Set α) := fun i ↦ hC.disjointOfDiff (hf i) (hC.inter_mem _ (hf i) _ hs)
  have h_diff_eq_sUnion i : f i \ s = ⋃₀ A i := by simp [A, IsSetSemiring.sUnion_disjointOfDiff]
  classical
  have h_m_eq i : m (f i) = m (f i ∩ s) + ∑ u in A i, m u :=
    eq_add_disjointOfDiff_of_subset hC (hC.inter_mem (f i) (hf i) s hs) (hf i) inter_subset_left
  simp_rw [h_m_eq]
  rw [tsum_add ENNReal.summable ENNReal.summable]
  refine add_le_add ?_ ?_
  · refine iInf_le_of_le (fun i ↦ f i ∩ s) <| iInf_le_of_le ?_ le_rfl
    rw [← iUnion_inter]
    exact Set.inter_subset_inter_left _ hf_subset
  · /- `⊢ (OuterMeasure.ofFunction m ⋯) (t \ s) ≤ ∑' n, ∑ u ∈ A n, m u`
    `OuterMeasure.ofFunction` is by definition an infimum over sums, equal here to
    `⨅ (f' : ℕ → Set α) (_ : t \ s ⊆ ⋃ i, f' i), ∑' i, m (f' i)`.
    The issue is that we don't have one sum on the right, but two sums.
    We introduce functions (`e` and `g`) to write those two sums as `∑' i, m ((g ∘ e) i)`,
    and then argue that the infimum is less that this particular sum. -/
    let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
    let g : ℕ × ℕ → Set α := fun n ↦
      if h : n.2 < (A n.1).card then (A n.1).ordered ⟨n.2, h⟩ else ∅
    suffices h_sum_sum : ∑' i, ∑ u in A i, m u = ∑' n, m (g (e n)) by
      rw [h_sum_sum]
      refine iInf_le_of_le _ (iInf_le_of_le ?_ le_rfl)
      suffices h_Union : (⋃ i, g (e i)) = (⋃ i, f i) \ s by
        rw [h_Union]
        exact diff_subset_diff hf_subset subset_rfl
      suffices ⋃ x, g x = ⋃ i, f i \ s by
        rw [iUnion_diff, ← biUnion_range, Equiv.range_eq_univ]
        simpa only [Set.mem_univ, iUnion_true]
      simp only [g, iUnion_dite, iUnion_empty,
        Set.union_empty, h_diff_eq_sUnion]
      ext x
      simp only [← Finset.iUnion_ordered, mem_iUnion, Prod.exists]
      constructor
      · rintro ⟨a, b, h, h_mem⟩
        exact ⟨a, ⟨b, h⟩, h_mem⟩
      · rintro ⟨a, ⟨b, h⟩, h_mem⟩
        exact ⟨a, b, h, h_mem⟩
    suffices ∀ i, ∑ u in A i, m u = ∑' n, m (g ⟨i, n⟩) by
      simp_rw [this]
      rw [← ENNReal.tsum_prod' (f := fun p ↦ m (g p)),
        ← tsum_range (fun n ↦ m (g n)) e.injective, Equiv.range_eq_univ,
        tsum_univ fun n ↦ m (g n)]
    intro i
    rw [← Finset.sum_ordered]
    let e_fin_range : Fin (A i).card ≃ Finset.range (A i).card :=
      { toFun := fun j ↦ ⟨j, Finset.mem_range.mpr j.2⟩
        invFun := fun j ↦ ⟨j, Finset.mem_range.mp j.2⟩
        left_inv := fun j ↦ by simp only [Subtype.coe_mk, Fin.eta]
        right_inv := fun j ↦ by simp only [Fin.val_mk, Subtype.coe_eta] }
    rw [Fintype.sum_equiv e_fin_range (fun j ↦ m (Finset.ordered (A i) j)) fun j ↦
        m (Finset.ordered (A i) (e_fin_range.symm j))]
    swap; · intro j; simp only [Equiv.symm_apply_apply]
    have : ∑' n, m (g (i, n)) =
        ∑' n : ((Finset.range (A i).card : Finset ℕ) : Set ℕ), m (g (i, n)) := by
      rw [tsum_subtype ((Finset.range (A i).card : Finset ℕ) : Set ℕ) fun n ↦ m (g (i, n))]
      congr with n
      rw [Set.indicator_apply]
      split_ifs with h_lt
      · simp only [h_lt, mem_setOf_eq, if_true]
      · have : ¬ (i, n).snd < (A (i, n).fst).card := by simpa using h_lt
        simp only [this, not_false_eq_true, dif_neg, addContent_empty, g]
    rw [this, Finset.tsum_subtype' (Finset.range (A i).card) fun n ↦ m (g (i, n)),
      ← Finset.sum_coe_sort (Finset.range (A i).card)]
    congr with j
    simp only [g]
    rw [dif_pos (Finset.mem_range.mp j.2)]
    congr

theorem caratheodory_semiring_extension (hC : IsSetSemiring C) (m : AddContent C)
    {s : Set α} (hs : s ∈ C) :
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s :=
  caratheodory_semiring_extension' hC (m.extend hC) (fun _ ↦ m.extend_eq_top hC) hs

theorem isCaratheodory_inducedOuterMeasure (hC : IsSetSemiring C) (m : AddContent C)
    (s : Set α) (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s := by
  induction hs with
  | basic u hu => exact caratheodory_semiring_extension hC m hu
  | empty => exact OuterMeasure.isCaratheodory_empty _
  | compl t _ h => exact OuterMeasure.isCaratheodory_compl _ h
  | iUnion f _ h => exact OuterMeasure.isCaratheodory_iUnion _ h

/-- Construct a measure from a sigma-subadditive function on a semiring. This
measure is defined on the associated Carathéodory sigma-algebra. -/
noncomputable def Measure.ofAddContentCaratheodory (hC : IsSetSemiring C)
    (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    @Measure α (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).caratheodory :=
  letI : MeasurableSpace α :=
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).caratheodory
  { inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty with
    m_iUnion := fun f hf hd ↦ OuterMeasure.iUnion_eq_of_caratheodory _ hf hd
    trim_le := by
      apply le_inducedOuterMeasure.mpr fun s hs ↦ ?_
      have hs_meas : MeasurableSet[(inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem
          addContent_empty).caratheodory] s := by
        show (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s
        exact caratheodory_semiring_extension hC m hs
      rw [OuterMeasure.trim_eq _ hs_meas,
        inducedOuterMeasure_addContent_of_subadditive hC m m_sigma_subadd hs] }

theorem Measure.ofAddContentCaratheodory_eq_inducedOuterMeasure (hC : IsSetSemiring C)
    (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (s : Set α) :
    Measure.ofAddContentCaratheodory hC m m_sigma_subadd s
      = inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s := rfl

theorem Measure.ofAddContentCaratheodory_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i)≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddContentCaratheodory hC m m_sigma_subadd s = m s :=
  inducedOuterMeasure_addContent_of_subadditive hC m  m_sigma_subadd hs

/-- Construct a measure from a sigma-subadditive content on a semiring, assuming the semiring
generates a given measurable structure. The measure is defined on this measurable structure. -/
noncomputable def Measure.ofAddContent [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    Measure α :=
  (Measure.ofAddContentCaratheodory hC m m_sigma_subadd).trim
    (by rw [← hC_gen]; exact isCaratheodory_inducedOuterMeasure hC m)

theorem Measure.ofAddContent_eq [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddContent hC hC_gen m m_sigma_subadd s = m s := by
  rw [Measure.ofAddContent, trim_measurableSet_eq]
  · exact Measure.ofAddContentCaratheodory_eq hC m m_sigma_subadd hs
  · rw [← hC_gen]; exact MeasurableSpace.measurableSet_generateFrom hs

end MeasureTheory

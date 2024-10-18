import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.KolmogorovExtension4.Content

open Finset Set MeasureTheory Order

open scoped Classical BigOperators NNReal Topology ENNReal MeasureTheory

namespace MeasureTheory

variable {α : Type _} {C : Set (Set α)}

/-- Same as the definition of `of_function`, except that `f i` belongs to `C`. The hypothesis
`m_top` applies in particular to a function of the form `extend m'`. -/
theorem ofFunction_eq_iInf_mem (s : Set α) (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)
    (m_top : ∀ (s) (_ : s ∉ C), m s = ∞) :
    OuterMeasure.ofFunction m m_empty s =
      ⨅ (f : ℕ → Set α) (_hf : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) := by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · refine le_iInf fun f ↦ le_iInf fun _ ↦ le_iInf fun h ↦ ?_
    refine iInf₂_le _ ?_
    exact h
  · simp_rw [le_iInf_iff]
    intro f hf_subset
    refine iInf_le_of_le f ?_
    by_cases hf : ∀ i, f i ∈ C
    · exact iInf_le_of_le hf (iInf_le_of_le hf_subset le_rfl)
    · simp only [hf, not_false_eq_true, iInf_neg, top_le_iff]
      push_neg at hf
      obtain ⟨i, hfi_not_mem⟩ := hf
      have hfi_top : m (f i) = ∞ := m_top _ hfi_not_mem
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, hfi_top⟩

theorem inducedOuterMeasure_eq_iInf_mem (hC : ∅ ∈ C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC = 0) (s : Set α) :
    inducedOuterMeasure m hC m_empty s =
      ⨅ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) (hf i) := by
  rw [inducedOuterMeasure, ofFunction_eq_iInf_mem s (extend m) _ fun s hs ↦ extend_eq_top m hs]
  simp_rw [← extend_eq m]

theorem OuterMeasure.ofFunction_eq_of_mono_of_subadditive (hC : SetSemiring C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0) (m_mono : ∀ ⦃s t : Set α⦄ (_hs : s ∈ C) (_ht : t ∈ C), s ⊆ t → m s ≤ m t)
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ (s) (_ : s ∉ C), m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m m_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem s m m_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hs_subset ↦ ?_
  calc
    m s = m (s ∩ ⋃ i, f i) := by rw [inter_eq_self_of_subset_left hs_subset]
    _ = m (⋃ i, s ∩ f i) := by rw [inter_iUnion]
    _ ≤ ∑' i, m (s ∩ f i) := by
      refine m_sigma_subadd (fun i ↦ hC.inter_mem _ hs _ (hf i)) ?_
      rwa [← inter_iUnion, inter_eq_self_of_subset_left hs_subset]
    _ ≤ ∑' i, m (f i) :=
      by
      refine tsum_le_tsum (fun i ↦ ?_) ENNReal.summable ENNReal.summable
      exact m_mono (hC.inter_mem _ hs _ (hf i)) (hf i) Set.inter_subset_right

theorem OuterMeasure.ofFunction_addContent_eq (hC : SetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ (s) (_ : s ∉ C), m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s :=
  OuterMeasure.ofFunction_eq_of_mono_of_subadditive hC m addContent_empty (fun _ _ ↦ m.mono hC)
    m_sigma_subadd m_top hs

theorem OuterMeasure.ofFunction_eq_of_add_of_subadditive (hC : SetSemiring C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ (s) (_ : s ∉ C), m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m m_empty s = m s :=
  OuterMeasure.ofFunction_eq_of_mono_of_subadditive hC m m_empty
    (fun _ _ ↦ monotone_of_additive hC m m_add) m_sigma_subadd m_top hs

theorem inducedOuterMeasure_eq_of_add_of_subadditive (hC : SetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    {s : Set α} (hs : s ∈ C) : inducedOuterMeasure m hC.empty_mem m_empty s = m s hs :=
  (OuterMeasure.ofFunction_eq_of_add_of_subadditive hC (extend m) _ (extend_sUnion_eq_sum m m_add)
      (extend_sum_le m m_sigma_subadd) (fun _ hs ↦ extend_eq_top m hs) hs).trans
    (extend_eq m hs)

theorem caratheodory_semiring_extension' (hC : SetSemiring C) (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)
    (m_add : ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_top : ∀ (s) (_ : s ∉ C), m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.IsCaratheodory (OuterMeasure.ofFunction m m_empty) s := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro t
  conv_rhs => rw [ofFunction_eq_iInf_mem _ _ m_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hf_subset ↦ ?_
  let A : ℕ → Finset (Set α) := fun i ↦ hC.diffFinset (hC.inter_mem _ (hf i) _ hs) (hf i)
  have h_diff_eq_sUnion : ∀ i, f i \ s = ⋃₀ A i := by
    intro i
    simp only [A]
    rw [← SetSemiring.diff_eq_sUnion, Set.inter_comm, diff_inter_self_eq_diff]
  have h_m_eq : ∀ i, m (f i) = m (f i ∩ s) + ∑ u in A i, m u := by
    intro i
    rw [hC.eq_add_diffFinset_of_subset m m_add (hC.inter_mem _ (hf i) _ hs) (hf i)
        inter_subset_left]
  simp_rw [h_m_eq]
  rw [tsum_add ENNReal.summable ENNReal.summable]
  refine add_le_add ?_ ?_
  · refine iInf_le_of_le (fun i ↦ f i ∩ s) ?_
    refine iInf_le_of_le ?_ le_rfl
    rw [← iUnion_inter]
    exact Set.inter_subset_inter_left _ hf_subset
  · let e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm
    let g' : ℕ × ℕ → Set α := fun n ↦
      if h : n.2 < (A n.1).card then (A n.1).ordered ⟨n.2, h⟩ else ∅
    have h_sum_sum : ∑' i, ∑ u in A i, m u = ∑' n, m (g' (e n)) := by
      have h1 : ∀ i, ∑ u in A i, m u = ∑' n, m (g' ⟨i, n⟩) := by
        intro i
        rw [← sum_ordered]
        let e_fin_range : Fin (A i).card ≃ Finset.range (A i).card :=
          { toFun := fun j ↦ ⟨j, Finset.mem_range.mpr j.2⟩
            invFun := fun j ↦ ⟨j, Finset.mem_range.mp j.2⟩
            left_inv := fun j ↦ by simp only [Subtype.coe_mk, Fin.eta]
            right_inv := fun j ↦ by simp only [Fin.val_mk, Subtype.coe_eta] }
        rw [Fintype.sum_equiv e_fin_range (fun j ↦ m (Finset.ordered (A i) j)) fun j ↦
            m (Finset.ordered (A i) (e_fin_range.symm j))]
        swap
        · dsimp only [A]
          intro j
          simp only [Equiv.symm_apply_apply]
        have : ∑' n, m (g' (i, n)) =
            ∑' n : ((Finset.range (A i).card : Finset ℕ) : Set ℕ), m (g' (i, n)) := by
          rw [tsum_subtype ((Finset.range (A i).card : Finset ℕ) : Set ℕ) fun n ↦ m (g' (i, n))]
          congr
          ext1 n
          simp only [Set.indicator_apply]
          by_cases h_lt : n ∈ ((Finset.range (A i).card : Finset ℕ) : Set ℕ)
          · simp only [h_lt, mem_setOf_eq, if_true]
          · have : ¬(i, n).snd < (A (i, n).fst).card := by
              change ¬n < (A i).card
              simpa only [coe_range, Set.mem_Iio] using h_lt
            simp only at h_lt this
            simp only [g', h_lt, mem_setOf_eq, if_false, this, not_false_iff, dif_neg, m_empty]
        rw [this, Finset.tsum_subtype' (Finset.range (A i).card) fun n ↦ m (g' (i, n))]
        simp only [g']
        rw [← Finset.sum_coe_sort (Finset.range (A i).card)]
        congr
        ext1 j
        classical
        simp only [A]
        rw [dif_pos]
        swap
        · exact Finset.mem_range.mp j.2
        congr
      simp_rw [h1]
      rw [(_ : ∑' (i : ℕ) (n : ℕ), m (g' (i, n)) = ∑' n : ℕ × ℕ, m (g' n))]
      swap; · rw [ENNReal.tsum_prod']
      rw [← tsum_range (fun n ↦ m (g' n)) e.injective, Equiv.range_eq_univ,
        tsum_subtype (univ : Set (ℕ × ℕ)) fun n ↦ m (g' n)]
      simp_rw [indicator_univ]
    have h_Union : (⋃ i, g' (e i)) = (⋃ i, f i) \ s := by
      rw [iUnion_diff, ← biUnion_range]
      simp_rw [Equiv.range_eq_univ]
      simp only [Set.mem_univ, iUnion_true]
      rw [iUnion_dite]
      simp only [iUnion_empty, Set.union_empty]
      simp_rw [h_diff_eq_sUnion]
      ext1 x
      simp_rw [← iUnion_ordered, mem_iUnion]
      simp only [Prod.exists]
      constructor
      · rintro ⟨a, b, h, h_mem⟩
        exact ⟨a, ⟨b, h⟩, h_mem⟩
      · rintro ⟨a, ⟨b, h⟩, h_mem⟩
        exact ⟨a, b, h, h_mem⟩
    rw [h_sum_sum]
    refine iInf_le_of_le _ (iInf_le_of_le ?_ le_rfl)
    rw [h_Union]
    exact diff_subset_diff hf_subset subset_rfl

theorem caratheodory_semiring_extension (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    {s : Set α} (hs : s ∈ C) :
    (inducedOuterMeasure m hC.empty_mem m_empty).IsCaratheodory s :=
  caratheodory_semiring_extension' hC (extend m) _ (extend_sUnion_eq_sum m m_add)
    (fun _ hs ↦ extend_eq_top m hs) hs

noncomputable def Measure.ofAddSubaddCaratheodory (hC : SetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i)) :
    @Measure α (inducedOuterMeasure m hC.empty_mem m_empty).caratheodory := by
  letI : MeasurableSpace α := (inducedOuterMeasure m hC.empty_mem m_empty).caratheodory
  exact { inducedOuterMeasure m hC.empty_mem m_empty with
    m_iUnion := fun f hf hd ↦ OuterMeasure.iUnion_eq_of_caratheodory _ hf hd
    trim_le := by
      refine le_inducedOuterMeasure.mpr fun s hs ↦ ?_
      have hs_meas : MeasurableSet[(inducedOuterMeasure m hC.empty_mem m_empty).caratheodory] s := by
        show (inducedOuterMeasure m hC.empty_mem m_empty).IsCaratheodory s
        exact caratheodory_semiring_extension hC m m_empty m_add hs
      rw [OuterMeasure.trim_eq _ hs_meas,
        inducedOuterMeasure_eq_of_add_of_subadditive hC m m_empty m_add m_sigma_subadd hs] }

theorem Measure.ofAddSubaddCaratheodory_eq_inducedOuterMeasure (hC : SetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    (s : Set α) :
    Measure.ofAddSubaddCaratheodory hC m m_empty m_add m_sigma_subadd s
      = inducedOuterMeasure m hC.empty_mem m_empty s := rfl

theorem Measure.ofAddSubaddCaratheodory_eq (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddSubaddCaratheodory hC m m_empty m_add m_sigma_subadd s = m s hs :=
  inducedOuterMeasure_eq_of_add_of_subadditive hC m m_empty m_add m_sigma_subadd hs

theorem isCaratheodory_partialSups {m : OuterMeasure α} {s : ℕ → Set α}
    (h : ∀ i, m.IsCaratheodory (s i)) (i : ℕ) : m.IsCaratheodory (partialSups s i) := by
  induction' i with i hi
  · rw [partialSups_zero]; exact h 0
  rw [partialSups_succ]
  exact m.isCaratheodory_union hi (h (i + 1))

theorem isCaratheodory_disjointed {m : OuterMeasure α} {s : ℕ → Set α}
    (h : ∀ i, m.IsCaratheodory (s i)) (i : ℕ) : m.IsCaratheodory (disjointed s i) := by
  induction' i with i _
  · rw [disjointed_zero]; exact h 0
  rw [disjointed_succ, diff_eq]
  refine m.isCaratheodory_inter (h (i + 1)) (m.isCaratheodory_compl ?_)
  exact isCaratheodory_partialSups h i

theorem isCaratheodory_iUnion {m : OuterMeasure α} {s : ℕ → Set α}
    (h : ∀ i, m.IsCaratheodory (s i)) : m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact OuterMeasure.isCaratheodory_iUnion_nat m (isCaratheodory_disjointed h)
    (disjoint_disjointed _)

theorem isCaratheodory_generateFrom (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (s : Set α) (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    (inducedOuterMeasure m hC.empty_mem m_empty).IsCaratheodory s := by
  apply MeasurableSpace.generateFrom_induction
  · exact fun _ ↦ caratheodory_semiring_extension hC m m_empty m_add
  · exact OuterMeasure.isCaratheodory_empty _
  · exact fun _ ↦ OuterMeasure.isCaratheodory_compl _
  · exact fun _ hf ↦ isCaratheodory_iUnion hf
  · exact hs

noncomputable def Measure.ofAddSubadd [mα : MeasurableSpace α] (hC : SetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i)) :
    Measure α :=
  (Measure.ofAddSubaddCaratheodory hC m m_empty m_add m_sigma_subadd).trim
    (by rw [← hC_gen]; exact isCaratheodory_generateFrom hC m m_empty m_add)

theorem Measure.ofAddSubadd_eq [mα : MeasurableSpace α] (hC : SetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddSubadd hC hC_gen m m_empty m_add m_sigma_subadd s = m s hs := by
  rw [Measure.ofAddSubadd, trim_measurableSet_eq]
  · exact Measure.ofAddSubaddCaratheodory_eq hC m m_empty m_add m_sigma_subadd hs
  · rw [← hC_gen]; exact MeasurableSpace.measurableSet_generateFrom hs

noncomputable def Measure.ofAddContent [mα : MeasurableSpace α] (hC : SetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    Measure α :=
  Measure.ofAddSubadd hC hC_gen (fun s _ ↦ m s) addContent_empty
    (fun I hI hI_disj hI_sUnion ↦ (m.add I hI hI_disj hI_sUnion).trans
      (by rw [Finset.sum_coe_sort]))
    m_sigma_subadd

theorem Measure.ofAddContent_eq [mα : MeasurableSpace α] (hC : SetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) : Measure.ofAddContent hC hC_gen m m_sigma_subadd s = m s :=
  Measure.ofAddSubadd_eq _ _ _ _ _ _ hs

end MeasureTheory

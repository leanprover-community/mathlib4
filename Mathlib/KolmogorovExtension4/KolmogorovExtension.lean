import Mathlib.KolmogorovExtension4.CaratheodoryExtension
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.KolmogorovExtension4.RegularityCompacts
import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.KolmogorovExtension4.RegularContent

open Set

open scoped ENNReal BigOperators

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

section KolFunDef

variable {s t : Set (∀ i, α i)}

/-- We will show that this is an additive set function that defines a measure. -/
noncomputable def kolmogorovFun (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) (s : Set (∀ i, α i))
    (hs : s ∈ cylinders α) : ℝ≥0∞ :=
  P (cylinders.finset hs) (cylinders.set hs)

theorem kolmogorovFun_congr_set (hs : s ∈ cylinders α) (h_eq : s = t) :
    kolmogorovFun P s hs = kolmogorovFun P t (by rwa [h_eq] at hs ) := by congr

variable [Nonempty (∀ i, α i)]

theorem kolmogorovFun_congr (hP : IsProjectiveMeasureFamily P) {s : Set (∀ i, α i)}
    (hs : s ∈ cylinders α) {I : Finset ι} {S : Set (∀ i : I, α i)} (hs_eq : s = cylinder I S)
    (hS : MeasurableSet S) : kolmogorovFun P s hs = P I S :=
  hP.congr_cylinder (cylinders.measurableSet hs) hS ((cylinders.eq_cylinder hs).symm.trans hs_eq)

theorem kolmogorovFun_empty (hP : IsProjectiveMeasureFamily P) :
    kolmogorovFun P ∅ (empty_mem_cylinders α) = 0 := by
  rw [kolmogorovFun_congr hP (empty_mem_cylinders α) (cylinder_empty ∅).symm MeasurableSet.empty,
    measure_empty]

theorem kolmogorovFun_union (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) (hst : Disjoint s t) :
    kolmogorovFun P (s ∪ t) (union_mem_cylinders hs ht) =
      kolmogorovFun P s hs + kolmogorovFun P t ht := by
  rw [mem_cylinders] at hs ht
  obtain ⟨I, S, hS, hs_eq⟩ := hs
  obtain ⟨J, T, hT, ht_eq⟩ := ht
  classical
  let S' := (fun f : ∀ i : (I ∪ J : Finset ι), α i ↦
    fun j : I ↦ f ⟨j, Finset.mem_union_left J j.prop⟩) ⁻¹' S
  let T' := (fun f : ∀ i : (I ∪ J : Finset ι), α i ↦
    fun j : J ↦ f ⟨j, Finset.mem_union_right I j.prop⟩) ⁻¹' T
  have hS' : MeasurableSet S' := by
    refine measurableSet_preimage ?_ hS
    exact measurable_pi_lambda _ (fun j ↦ measurable_pi_apply _)
  have hT' : MeasurableSet T' := by
    refine measurableSet_preimage ?_ hT
    exact measurable_pi_lambda _ (fun j ↦ measurable_pi_apply _)
  have h_eq1 : s = cylinder (I ∪ J) S' := by rw [hs_eq]; exact cylinder_eq_cylinder_union I S J
  have h_eq2 : t = cylinder (I ∪ J) T' := by rw [ht_eq]; exact cylinder_eq_cylinder_union J T I
  have h_eq3 : s ∪ t = cylinder (I ∪ J) (S' ∪ T') := by
    rw [hs_eq, ht_eq]; exact union_cylinder _ _ _ _
  rw [kolmogorovFun_congr hP hs h_eq1 hS', kolmogorovFun_congr hP ht h_eq2 hT',
    kolmogorovFun_congr hP _ h_eq3 (hS'.union hT'), measure_union _ hT']
  rwa [hs_eq, ht_eq, disjoint_cylinder_iff] at hst

theorem kolmogorovFun_additive (hP : IsProjectiveMeasureFamily P) (I : Finset (Set (∀ i, α i)))
    (h_ss : ↑I ⊆ cylinders α) (h_dis : PairwiseDisjoint (I : Set (Set (∀ i, α i))) id)
    (h_mem : ⋃₀ ↑I ∈ cylinders α) :
    kolmogorovFun P (⋃₀ I) h_mem = ∑ u : I, kolmogorovFun P u (h_ss u.prop) := by
  refine sUnion_eq_sum_of_union_eq_add' ?_ ?_ _ ?_ ?_ I h_ss h_dis h_mem
  · exact empty_mem_cylinders α
  · exact union_mem_cylinders
  · exact kolmogorovFun_empty hP
  · exact kolmogorovFun_union hP

/-- `kolmogorovFun` as an additive content. -/
noncomputable def kolContent (hP : IsProjectiveMeasureFamily P) : AddContent (cylinders α) :=
  extendContent setSemiringCylinders (kolmogorovFun P) (kolmogorovFun_empty hP)
    (kolmogorovFun_additive hP)

theorem kolContent_eq (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α) :
    kolContent hP s = kolmogorovFun P s hs := by rw [kolContent, extendContent_eq]

theorem kolContent_ne_top [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ cylinders α) : kolContent hP s ≠ ∞ := by
  rw [kolContent_eq hP hs]; exact measure_ne_top _ _

theorem kolContent_congr (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α) {I : Finset ι}
    {S : Set (∀ i : I, α i)} (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    kolContent hP s = P I S := by rw [kolContent_eq, kolmogorovFun_congr hP hs hs_eq hS]

theorem kolContent_mono (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) (hst : s ⊆ t) : kolContent hP s ≤ kolContent hP t :=
  (kolContent hP).mono setSemiringCylinders hs ht hst

theorem kolContent_iUnion_le (hP : IsProjectiveMeasureFamily P) ⦃s : ℕ → Set (∀ i : ι, α i)⦄
    (hs : ∀ n, s n ∈ cylinders α) (n : ℕ) :
    kolContent hP (⋃ i ≤ n, s i) ≤ ∑ i in Finset.range (n + 1), kolContent hP (s i) :=
  addContent_iUnion_le (kolContent hP) setRing_cylinders hs n

theorem kolContent_diff (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) : kolContent hP s - kolContent hP t ≤ kolContent hP (s \ t) :=
  addContent_diff (kolContent hP) setRing_cylinders hs ht

end KolFunDef

section InnerRegular

local notation "Js" => cylinders.finset

local notation "As" => cylinders.set

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem exists_compact
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ IsClosed K ∧ K ⊆ A ∧ P J (A \ K) ≤ ε := by
  by_cases hPA : P J A = 0
  · refine ⟨∅, isCompact_empty, isClosed_empty, empty_subset _, ?_⟩
    rw [diff_empty, hPA]
    exact zero_le ε
  have h : P J A - ε < P J A := ENNReal.sub_lt_self (measure_ne_top _ _) hPA hε.ne'
  obtain ⟨K, hKA, ⟨hK_compact, hK_closed⟩, h_lt⟩ := hP_inner J hA (P J A - ε) h
  refine ⟨K, hK_compact, hK_closed, hKA, ?_⟩
  rw [measure_diff hKA hK_closed.measurableSet (measure_ne_top (P J) _)]
  have h_le := h_lt.le
  rw [tsub_le_iff_left] at h_le ⊢
  rwa [add_comm]

lemma innerRegular_kolContent [∀ i, Nonempty (α i)] (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet)
    {s : Set (∀ i, α i)} (hs : s ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (K : Set (∀ i, α i)) (_ : K ∈ closedCompactCylinders α),
      K ⊆ s ∧ kolContent hP (s \ K) ≤ ε := by
  obtain ⟨K', hK'_compact, hK'_closed, hK'_subset, hK'⟩ := exists_compact hP_inner
    (Js hs) (As hs) (cylinders.measurableSet hs) ε hε
  refine ⟨cylinder (Js hs) K', ?_, ?_, ?_⟩
  · exact cylinder_mem_closedCompactCylinders _ _ hK'_closed hK'_compact
  · conv_rhs => rw [cylinders.eq_cylinder hs]
    simp_rw [cylinder]
    rw [Function.Surjective.preimage_subset_preimage_iff]
    · exact hK'_subset
    · intro y
      let x := (inferInstance : Nonempty (∀ i, α i)).some
      classical
      refine ⟨fun i ↦ if hi : i ∈ Js hs then y ⟨i, hi⟩ else x i, ?_⟩
      ext1 i
      simp only [Finset.coe_mem, dite_true]
  · simp only
    have : (s \ cylinder (Js hs) K') = (cylinder (Js hs) (As hs) \ cylinder (Js hs) K') := by
      congr
      exact cylinders.eq_cylinder hs
    rw [this, diff_cylinder_same]
    refine (le_of_eq ?_).trans hK'
    have h_meas : MeasurableSet (As hs \ K') :=
      MeasurableSet.diff (cylinders.measurableSet hs) hK'_closed.measurableSet
    exact kolContent_congr hP (cylinder_mem_cylinders _ _ h_meas) rfl h_meas

end InnerRegular

section InnerRegularAssumption

variable [∀ i, Nonempty (α i)] [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem kolContent_sigma_additive_of_innerRegular (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet)
    ⦃f : ℕ → Set (∀ i, α i)⦄ (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α)
    (h_disj : Pairwise (Disjoint on f)) :
    kolContent hP (⋃ i, f i) = ∑' i, kolContent hP (f i) := by
  refine (kolContent hP).sigma_additive_of_regular setRing_cylinders ?_ isCompactSystem_cylinders
    (fun t ht ↦ mem_cylinder_of_mem_closedCompactCylinders ht) ?_ hf hf_Union h_disj
  · exact fun hx ↦ kolContent_ne_top _ hx
  · intros t ht ε hε
    convert innerRegular_kolContent hP hP_inner ht ε hε with u
    refine ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ?_⟩
    obtain ⟨a, b, c⟩ := h
    exact ⟨a, b, c⟩

theorem kolContent_sigma_subadditive_of_innerRegular (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet)
    ⦃f : ℕ → Set (∀ i, α i)⦄ (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α) :
    kolContent hP (⋃ i, f i) ≤ ∑' i, kolContent hP (f i) :=
  (kolContent hP).sigma_subadditive_of_sigma_additive setRing_cylinders
    (kolContent_sigma_additive_of_innerRegular hP hP_inner) f hf hf_Union

end InnerRegularAssumption

/-- Projective limit of a projective measure family. -/
noncomputable def projectiveLimitWithWeakestHypotheses [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, BorelSpace (α i)] [∀ i, SecondCountableTopology (α i)]
    [∀ i, CompleteSpace (α i)] [∀ i, Nonempty (α i)] (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ i, IsFiniteMeasure (P i)] (hP : IsProjectiveMeasureFamily P) : Measure (∀ i, α i) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders (kolContent hP)
    (kolContent_sigma_subadditive_of_innerRegular hP fun J ↦
      innerRegular_isCompact_isClosed_measurableSet_of_complete_countable (P J))

section Polish

variable [∀ i, Nonempty (α i)] [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem kolContent_sigma_additive (hP : IsProjectiveMeasureFamily P) ⦃f : ℕ → Set (∀ i, α i)⦄
    (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α)
    (h_disj : Pairwise (Disjoint on f)) :
    kolContent hP (⋃ i, f i) = ∑' i, kolContent hP (f i) := by
  refine kolContent_sigma_additive_of_innerRegular hP ?_ hf hf_Union h_disj
  exact fun J ↦ PolishSpace.innerRegular_isCompact_measurableSet (P J)

theorem kolContent_sigma_subadditive (hP : IsProjectiveMeasureFamily P) ⦃f : ℕ → Set (∀ i, α i)⦄
    (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α) :
    kolContent hP (⋃ i, f i) ≤ ∑' i, kolContent hP (f i) := by
  refine kolContent_sigma_subadditive_of_innerRegular hP ?_ hf hf_Union
  exact fun J ↦ PolishSpace.innerRegular_isCompact_measurableSet (P J)

/-- Projective limit of a projective measure family. -/
noncomputable def projectiveLimit (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ i, IsFiniteMeasure (P i)] (hP : IsProjectiveMeasureFamily P) : Measure (∀ i, α i) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders (kolContent hP)
    (kolContent_sigma_subadditive hP)

/-- **Kolmogorov extension theorem**: for any projective measure family `P`, there exists a measure
on `Π i, α i` which is the projective limit of `P`. That measure is given by
`projective_limit P hP`, where `hP : is_projective_measure_family P`.
The projective limit is unique: see `is_projective_limit_unique`. -/
theorem isProjectiveLimit_projectiveLimit (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit P hP) P := by
  intro J
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_proj
  have h_mem : (fun (x : ∀ i : ι, (fun i : ι ↦ α i) i) (i : ↥J) ↦ x ↑i) ⁻¹' s ∈ cylinders α := by
    rw [mem_cylinders]; exact ⟨J, s, hs, rfl⟩
  rw [projectiveLimit, Measure.ofAddContent_eq _ _ _ _ h_mem, kolContent_congr hP h_mem rfl hs]

instance isFiniteMeasure_projectiveLimit [Nonempty ι] (hP : IsProjectiveMeasureFamily P) :
    IsFiniteMeasure (projectiveLimit P hP) :=
  isFiniteMeasure_of_isProjectiveLimit (isProjectiveLimit_projectiveLimit hP)

instance isProbabilityMeasure_projectiveLimit [hι : Nonempty ι]
    {P : ∀ J : Finset ι, Measure (∀ j : J, α j)} [∀ i, IsProbabilityMeasure (P i)]
    (hP : IsProjectiveMeasureFamily P) : IsProbabilityMeasure (projectiveLimit P hP) := by
  constructor
  rw [← cylinder_univ ({hι.some} : Finset ι),
    (isProjectiveLimit_projectiveLimit hP).measure_cylinder _ MeasurableSet.univ]
  exact measure_univ

end Polish

end MeasureTheory

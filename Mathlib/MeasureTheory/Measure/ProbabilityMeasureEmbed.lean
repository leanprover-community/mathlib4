/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.CompletelyRegular
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Dirac deltas as probability measures and embedding of a space into probability measures on it

## Main definitions
* `diracProba`: The Dirac delta mass at a point as a probability measure.

## Main results
* `embedding_diracProba`: If `X` is a completely regular T0 space with its Borel sigma algebra,
  then the mapping that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
  `X ↪ ProbabilityMeasure X`.

## Tags
probability measure, Dirac delta, embedding
-/

open Topology Metric Filter Set ENNReal NNReal BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section generic_lemmas

namespace MeasureTheory

-- UPDATE: Weaken hypotheses to `[TopologicalSpace Ω]` instead of `[PseudoEMetricSpace Ω]`
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto' {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed

lemma ProbabilityMeasure.isClosed_vanishingSet {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] (S : Set Ω) :
    IsClosed {μ : ProbabilityMeasure Ω |
              ∀ (f : Ω →ᵇ ℝ≥0), (∀ s ∈ S, f s = 0) → μ.toWeakDualBCNN f = 0} := by
  have aux : ∀ (f : Ω →ᵇ ℝ≥0), IsClosed {μ : ProbabilityMeasure Ω | μ.toWeakDualBCNN f = 0} := by
    intro f
    have obs := ProbabilityMeasure.continuous_testAgainstNN_eval (Ω := Ω) f
    rw [continuous_iff_isClosed] at obs
    exact obs {0} isClosed_singleton
  convert @isClosed_biInter (ProbabilityMeasure Ω) (Ω →ᵇ ℝ≥0)
            _ {f | ∀ s ∈ S, f s = 0} (fun f ↦ {μ : ProbabilityMeasure Ω | μ.toWeakDualBCNN f = 0})
            (fun i _ ↦ aux i)
  ext μ
  simp only [ProbabilityMeasure.toWeakDualBCNN_apply, mem_setOf_eq, mem_iInter]

end MeasureTheory

lemma dist_le_one_of_mem_unitInterval {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) :
    dist x y ≤ 1 := by
  rw [Real.dist_eq]
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (by linarith)]
    simp only [neg_sub]
    exact (sub_le_self _ hx.1).trans hy.2
  · rw [abs_of_pos (by linarith)]
    exact (sub_le_self _ hy.1).trans hx.2

lemma CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x ∉ K) :
    ∃ (f : X →ᵇ ℝ≥0), f x = 1 ∧ (∀ y ∈ K, f y = 0) := by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  set h := ContinuousMap.mk (fun x ↦ Real.toNNReal ((1 : ℝ) - g x))
            (continuous_real_toNNReal.comp (continuous_const.sub g_cont.subtype_val))
  set f := BoundedContinuousFunction.mkOfBound h 1 (by
    intro x y
    simp only [ContinuousMap.coe_mk, h]
    apply (Real.lipschitzWith_toNNReal.dist_le_mul (1 - g x) (1 - g y)).trans
    simp only [NNReal.coe_one, dist_sub_eq_dist_add_right, one_mul]
    rw [Real.dist_eq]
    ring_nf
    simpa [neg_add_eq_sub, ← Real.dist_eq, dist_comm] using
      dist_le_one_of_mem_unitInterval (Subtype.coe_prop (g x)) (Subtype.coe_prop (g y)))
  refine ⟨f, ?_, ?_⟩
  · simp only [mkOfBound_coe, ContinuousMap.coe_mk, gx_zero, Icc.coe_zero, sub_zero,
               Real.toNNReal_one, f, h]
  · intro y y_in_K
    simp only [mkOfBound_coe, ContinuousMap.coe_mk, g_one_on_K y_in_K, Pi.one_apply, Icc.coe_one,
               sub_self, Real.toNNReal_zero, f, h]

end generic_lemmas

namespace MeasureTheory

section dirac_injective

variable {X : Type*} [MeasurableSpace X]

/-- Dirac delta measures at two points are equal if every measurable set contains either both or
neither of the points. -/
lemma dirac_eq_dirac_iff_forall_measurableSet {x y : X} :
    Measure.dirac x = Measure.dirac y ↔ ∀ A, MeasurableSet A → (x ∈ A ↔ y ∈ A) := by
  constructor
  · intro h A A_mble
    have obs := congr_arg (fun μ ↦ μ A) h
    simp only [Measure.dirac_apply' _ A_mble] at obs
    by_cases x_in_A : x ∈ A
    · simpa only [x_in_A, indicator_of_mem, Pi.one_apply, true_iff, Eq.comm (a := (1 : ℝ≥0∞)),
                  indicator_eq_one_iff_mem] using obs
    · simpa only [x_in_A, indicator_of_not_mem, Eq.comm (a := (0 : ℝ≥0∞)), indicator_apply_eq_zero,
                  false_iff, not_false_eq_true, Pi.one_apply, one_ne_zero, imp_false] using obs
  · intro h
    ext A A_mble
    by_cases x_in_A : x ∈ A
    · simp only [Measure.dirac_apply' _ A_mble, x_in_A, indicator_of_mem, Pi.one_apply,
                 (h A A_mble).mp x_in_A]
    · have y_notin_A : y ∉ A := by simp_all only [false_iff, not_false_eq_true]
      simp only [Measure.dirac_apply' _ A_mble, x_in_A, y_notin_A,
                 not_false_eq_true, indicator_of_not_mem]

/-- Dirac delta measures at two points are different if and only if there is a measurable set
containing one of the points but not the other. -/
lemma dirac_ne_dirac_iff {x y : X} :
    Measure.dirac x ≠ Measure.dirac y ↔ ∃ A, MeasurableSet A ∧ x ∈ A ∧ y ∉ A := by
  apply not_iff_not.mp
  simp only [ne_eq, not_not, not_exists, not_and, dirac_eq_dirac_iff_forall_measurableSet]
  refine ⟨fun h A A_mble ↦ by simp only [h A A_mble, imp_self], fun h A A_mble ↦ ?_⟩
  by_cases x_in_A : x ∈ A
  · simp only [x_in_A, h A A_mble x_in_A]
  · simpa only [x_in_A, false_iff] using h Aᶜ (MeasurableSet.compl_iff.mpr A_mble) x_in_A

/-- Dirac delta measures at two different points are different if all singletons are measurable. -/
lemma dirac_ne_dirac [MeasurableSingletonClass X] {x y : X} (x_ne_y : x ≠ y) :
    Measure.dirac x ≠ Measure.dirac y :=
  dirac_ne_dirac_iff.mpr ⟨{x}, measurableSet_singleton x, rfl, Ne.symm x_ne_y⟩

/-- Dirac delta measures at two different points in a T0 topological space are different if the
sigma algebra contains all open sets. -/
lemma dirac_ne_dirac' {X : Type*} [TopologicalSpace X] [T0Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {x y : X} (x_ne_y : x ≠ y) :
    Measure.dirac x ≠ Measure.dirac y := by
  apply dirac_ne_dirac_iff.mpr
  obtain ⟨U, U_open, mem_U⟩ := exists_isOpen_xor'_mem x_ne_y
  by_cases x_in_U : x ∈ U
  · refine ⟨U, U_open.measurableSet, x_in_U, ?_⟩
    simp_all only [ne_eq, xor_true, not_false_eq_true]
  · refine ⟨Uᶜ, U_open.isClosed_compl.measurableSet, x_in_U, ?_⟩
    simp_all only [ne_eq, xor_false, id_eq, mem_compl_iff, not_true_eq_false, not_false_eq_true]

end dirac_injective

section embed_to_probabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Dirac delta mass at a point `x : Ω` as a `ProbabilityMeasure`. -/
noncomputable def diracProba (x : Ω) : ProbabilityMeasure Ω :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

/-- The assignment `x ↦ diracProba x` is injective if all singletons are measurable. -/
lemma injective_diracProba {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] :
    Function.Injective (fun (x : X) ↦ diracProba x) := by
  intro x y x_ne_y
  by_contra con
  exact dirac_ne_dirac con <| congr_arg Subtype.val x_ne_y

@[simp]
lemma diracProba_toMeasure_apply' (x : Ω) {A : Set Ω} (A_mble : MeasurableSet A) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply' x A_mble

@[simp]
lemma diracProba_toMeasure_apply_of_mem {x : Ω} {A : Set Ω} (x_in_A : x ∈ A) :
    (diracProba x).toMeasure A = 1 := Measure.dirac_apply_of_mem x_in_A

@[simp]
lemma diracProba_toMeasure_apply [MeasurableSingletonClass Ω] (x : Ω) (A : Set Ω) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply _ _

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- The assignment `x ↦ diracProba x` is continuous `Ω → ProbabilityMeasure Ω`. -/
lemma continuous_diracProba : Continuous (fun (x : Ω) ↦ diracProba x) := by
  rw [continuous_iff_continuousAt]
  apply fun x ↦ ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f ↦ ?_
  have f_mble : Measurable (fun ω ↦ (f ω : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp only [diracProba, ProbabilityMeasure.coe_mk, lintegral_dirac' _ f_mble]
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt

/-- In a T0 topological space equipped with a sigma algebra which contains all open sets,
the assignment `x ↦ diracProba x` is injective. -/
lemma injective_diracProba_of_T0 [T0Space Ω] :
    Function.Injective (fun (x : Ω) ↦ diracProba x) := by
  intro x y x_ne_y
  by_contra con
  exact dirac_ne_dirac' con <| congr_arg Subtype.val x_ne_y

lemma not_tendsto_diracProba_of_not_tendsto [CompletelyRegularSpace Ω] {x : Ω} (L : Filter Ω)
    (h : ¬ Tendsto id L (𝓝 x)) :
    ¬ Tendsto diracProba L (𝓝 (diracProba x)) := by
  have obs : ∃ U, U ∈ 𝓝 x ∧ ∃ᶠ x in L, x ∉ U := by
    by_contra! con
    apply h
    intro U U_nhd
    simpa only [not_frequently, not_not] using con U U_nhd
  obtain ⟨U, U_nhd, hU⟩ := obs
  have Uint_nhd : interior U ∈ 𝓝 x := by simpa only [interior_mem_nhds] using U_nhd
  obtain ⟨f, fx_eq_one, f_vanishes_outside⟩ :=
    CompletelyRegularSpace.exists_BCNN isOpen_interior.isClosed_compl
      (by simpa only [mem_compl_iff, not_not] using mem_of_mem_nhds Uint_nhd)
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  simp only [diracProba, ProbabilityMeasure.coe_mk, not_forall]
  use f
  simp only [lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable),
             fx_eq_one]
  apply not_tendsto_iff_exists_frequently_nmem.mpr
  refine ⟨Ioi 0, Ioi_mem_nhds (by simp only [ENNReal.coe_one, zero_lt_one]),
          hU.mp (eventually_of_forall ?_)⟩
  intro x x_notin_U
  rw [f_vanishes_outside x
      (compl_subset_compl.mpr (show interior U ⊆ U from interior_subset) x_notin_U)]
  simp only [ENNReal.coe_zero, mem_Ioi, lt_self_iff_false, not_false_eq_true]

lemma tendsto_diracProba_iff_tendsto [CompletelyRegularSpace Ω] {x : Ω} (L : Filter Ω) :
    Tendsto diracProba L (𝓝 (diracProba x)) ↔ Tendsto id L (𝓝 x) := by
  constructor
  · contrapose
    apply not_tendsto_diracProba_of_not_tendsto
  · intro h
    have aux := (@continuous_diracProba Ω _ _ _).continuousAt (x := x)
    simp only [ContinuousAt] at aux
    apply aux.comp h

/-- An inverse function to `diracProba` (only really an inverse under hypotheses that
guarantee injectivity of `diracProba`). -/
noncomputable def diracProbaSymm : range (diracProba (Ω := Ω)) → Ω :=
  fun μ' ↦ (mem_range.mp μ'.prop).choose

@[simp] lemma diracProba_diracProbaSymm (μ : range (diracProba (Ω := Ω))) :
    diracProba (diracProbaSymm μ) = μ := (mem_range.mp μ.prop).choose_spec

lemma diracProbaSymm_eq [T0Space Ω] {x : Ω} {μ : range (diracProba (Ω := Ω))}
    (h : μ = diracProba x) :
    diracProbaSymm μ = x := by
  apply injective_diracProba_of_T0 (Ω := Ω)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec

/-- In a T0 topological space `Ω`, the assignment `x ↦ diracProba x` is a bijection to its
range in `ProbabilityMeasure Ω`. -/
noncomputable def diracProbaEquiv [T0Space Ω] : Ω ≃ range (diracProba (Ω := Ω)) where
  toFun := fun x ↦ ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaSymm
  left_inv x := by apply diracProbaSymm_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaSymm])

/-- The composition of `diracProbaEquiv.symm` and `diracProba` is the subtype inclusion. -/
lemma diracProba_comp_diracProbaEquiv_symm_eq_val [T0Space Ω] :
    diracProba ∘ (diracProbaEquiv (Ω := Ω)).symm = fun μ ↦ μ.val := by
  funext μ; simp [diracProbaEquiv]

lemma tendsto_diracProbaEquivSymm_iff_tendsto [T0Space Ω] [CompletelyRegularSpace Ω]
    {μ : range (diracProba (Ω := Ω))} (F : Filter (range (diracProba (Ω := Ω)))) :
    Tendsto diracProbaEquiv.symm F (𝓝 (diracProbaEquiv.symm μ)) ↔ Tendsto id F (𝓝 μ) := by
  have key :=
    tendsto_diracProba_iff_tendsto (F.map diracProbaEquiv.symm) (x := diracProbaEquiv.symm μ)
  rw [← (diracProbaEquiv (Ω := Ω)).symm_comp_self, ← tendsto_map'_iff] at key
  simp only [tendsto_map'_iff, map_map, Equiv.self_comp_symm, map_id] at key
  simp only [← key, diracProba_comp_diracProbaEquiv_symm_eq_val]
  convert tendsto_subtype_rng.symm
  exact apply_rangeSplitting (fun x => diracProba x) μ

/-- In a T0 topological space, `diracProbaEquiv` is continuous. -/
lemma continuous_diracProbaEquiv [T0Space Ω] :
    Continuous (diracProbaEquiv (Ω := Ω)) :=
  Continuous.subtype_mk continuous_diracProba mem_range_self

/-- In a completely regular T0 topological space, the inverse of `diracProbaEquiv` is continuous. -/
lemma continuous_diracProbaEquivSymm [T0Space Ω] [CompletelyRegularSpace Ω] :
    Continuous (diracProbaEquiv (Ω := Ω)).symm := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds (y := diracProbaSymm μ)
  exact (@tendsto_diracProbaEquivSymm_iff_tendsto Ω _ _ _ _ _ μ (𝓝 μ)).mpr fun _ mem_nhd ↦ mem_nhd

/-- In a completely regular T0 topological space `Ω`, `diracProbaEquiv` is a homeomorphism to
its image in `ProbabilityMeasure Ω`. -/
noncomputable def homeomorph_diracProba [T0Space Ω] [CompletelyRegularSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] : Ω ≃ₜ range (diracProba (Ω := Ω)) :=
  @Homeomorph.mk Ω _ _ _ diracProbaEquiv continuous_diracProbaEquiv continuous_diracProbaEquivSymm

/-- If `X` is a completely regular T0 space with its Borel sigma algebra, then the mapping
that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
`X → ProbabilityMeasure X`. -/
theorem embedding_diracProba [T0Space Ω] [CompletelyRegularSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] : Embedding (fun (x : Ω) ↦ diracProba x) :=
  embedding_subtype_val.comp homeomorph_diracProba.embedding

end embed_to_probabilityMeasure

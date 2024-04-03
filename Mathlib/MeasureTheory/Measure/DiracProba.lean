/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.CompletelyRegular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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

/-- Dirac delta measures at two different points in a T0 topological space are different if the
sigma algebra contains all open sets. -/
lemma MeasureTheory.dirac_ne_dirac' {X : Type*} [TopologicalSpace X] [T0Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {x y : X} (x_ne_y : x ≠ y) :
    Measure.dirac x ≠ Measure.dirac y := by
  apply dirac_ne_dirac_iff.mpr
  obtain ⟨U, U_open, mem_U⟩ := exists_isOpen_xor'_mem x_ne_y
  by_cases x_in_U : x ∈ U
  · refine ⟨U, U_open.measurableSet, x_in_U, ?_⟩
    simp_all only [ne_eq, xor_true, not_false_eq_true]
  · refine ⟨Uᶜ, U_open.isClosed_compl.measurableSet, x_in_U, ?_⟩
    simp_all only [ne_eq, xor_false, id_eq, mem_compl_iff, not_true_eq_false, not_false_eq_true]

lemma CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x ∉ K) :
    ∃ (f : X →ᵇ ℝ≥0), f x = 1 ∧ (∀ y ∈ K, f y = 0) := by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  -- TODO: Golf the following once we have subtraction on BoundedContinuousFunction with ℝ≥0 values.
  -- The only thing we want is `x ↦ 1 - g x` as `f : X →ᵇ ℝ≥0`.
  set h := ContinuousMap.mk (fun x ↦ Real.toNNReal ((1 : ℝ) - g x))
            (continuous_real_toNNReal.comp (continuous_const.sub g_cont.subtype_val))
  set f := BoundedContinuousFunction.mkOfBound h 1 (by
    intro x y
    simp only [ContinuousMap.coe_mk, h]
    apply (Real.lipschitzWith_toNNReal.dist_le_mul (1 - g x) (1 - g y)).trans
    simp only [NNReal.coe_one, dist_sub_eq_dist_add_right, one_mul, Real.dist_eq]
    ring_nf
    simpa [neg_add_eq_sub, ← Real.dist_eq, dist_comm] using
      Real.dist_le_of_mem_Icc_01 (Subtype.coe_prop (g x)) (Subtype.coe_prop (g y)))
  refine ⟨f, ?_, ?_⟩
  · simp only [mkOfBound_coe, ContinuousMap.coe_mk, gx_zero, Icc.coe_zero, sub_zero,
               Real.toNNReal_one, f, h]
  · intro y y_in_K
    simp only [mkOfBound_coe, ContinuousMap.coe_mk, g_one_on_K y_in_K, Pi.one_apply, Icc.coe_one,
               sub_self, Real.toNNReal_zero, f, h]

end generic_lemmas

namespace MeasureTheory

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

@[simp] lemma diracProba_toMeasure_apply' (x : Ω) {A : Set Ω} (A_mble : MeasurableSet A) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply' x A_mble

@[simp] lemma diracProba_toMeasure_apply_of_mem {x : Ω} {A : Set Ω} (x_in_A : x ∈ A) :
    (diracProba x).toMeasure A = 1 := Measure.dirac_apply_of_mem x_in_A

@[simp] lemma diracProba_toMeasure_apply [MeasurableSingletonClass Ω] (x : Ω) (A : Set Ω) :
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
  obtain ⟨U, U_nhd, hU⟩ : ∃ U, U ∈ 𝓝 x ∧ ∃ᶠ x in L, x ∉ U := by
    by_contra! con
    apply h
    intro U U_nhd
    simpa only [not_frequently, not_not] using con U U_nhd
  have Uint_nhd : interior U ∈ 𝓝 x := by simpa only [interior_mem_nhds] using U_nhd
  obtain ⟨f, fx_eq_one, f_vanishes_outside⟩ :=
    CompletelyRegularSpace.exists_BCNN isOpen_interior.isClosed_compl
      (by simpa only [mem_compl_iff, not_not] using mem_of_mem_nhds Uint_nhd)
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  rw [not_forall]
  use f
  simp only [diracProba, ProbabilityMeasure.coe_mk, fx_eq_one,
             lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable)]
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
noncomputable def diracProbaInverse : range (diracProba (Ω := Ω)) → Ω :=
  fun μ' ↦ (mem_range.mp μ'.prop).choose

@[simp] lemma diracProba_diracProbaInverse (μ : range (diracProba (Ω := Ω))) :
    diracProba (diracProbaInverse μ) = μ := (mem_range.mp μ.prop).choose_spec

lemma diracProbaInverse_eq [T0Space Ω] {x : Ω} {μ : range (diracProba (Ω := Ω))}
    (h : μ = diracProba x) :
    diracProbaInverse μ = x := by
  apply injective_diracProba_of_T0 (Ω := Ω)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec

/-- In a T0 topological space `Ω`, the assignment `x ↦ diracProba x` is a bijection to its
range in `ProbabilityMeasure Ω`. -/
noncomputable def diracProbaEquiv [T0Space Ω] : Ω ≃ range (diracProba (Ω := Ω)) where
  toFun := fun x ↦ ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaInverse
  left_inv x := by apply diracProbaInverse_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaInverse])

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
  apply continuousAt_of_tendsto_nhds (y := diracProbaInverse μ)
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

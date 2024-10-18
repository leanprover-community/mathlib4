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
* `isEmbedding_diracProba`: If `X` is a completely regular T0 space with its Borel sigma algebra,
  then the mapping that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
  `X ↪ ProbabilityMeasure X`.

## Tags
probability measure, Dirac delta, embedding
-/

open Topology Metric Filter Set ENNReal NNReal BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

lemma CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x ∉ K) :
    ∃ (f : X →ᵇ ℝ≥0), f x = 1 ∧ (∀ y ∈ K, f y = 0) := by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  have g_bdd : ∀ x y, dist (Real.toNNReal (g x)) (Real.toNNReal (g y)) ≤ 1 := by
    refine fun x y ↦ ((Real.lipschitzWith_toNNReal).dist_le_mul (g x) (g y)).trans ?_
    simpa using Real.dist_le_of_mem_Icc_01 (g x).prop (g y).prop
  set g' := BoundedContinuousFunction.mkOfBound
      ⟨fun x ↦ Real.toNNReal (g x), continuous_real_toNNReal.comp g_cont.subtype_val⟩ 1 g_bdd
  set f := 1 - g'
  refine ⟨f, by simp [f, g', gx_zero], fun y y_in_K ↦ by simp [f, g', g_one_on_K y_in_K]⟩

namespace MeasureTheory

section embed_to_probabilityMeasure

variable {X : Type*} [MeasurableSpace X]

/-- The Dirac delta mass at a point `x : X` as a `ProbabilityMeasure`. -/
noncomputable def diracProba (x : X) : ProbabilityMeasure X :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

/-- The assignment `x ↦ diracProba x` is injective if all singletons are measurable. -/
lemma injective_diracProba {X : Type*} [MeasurableSpace X] [MeasurableSpace.SeparatesPoints X] :
    Function.Injective (fun (x : X) ↦ diracProba x) := by
  intro x y x_eq_y
  rw [← dirac_eq_dirac_iff]
  rwa [Subtype.ext_iff] at x_eq_y

@[simp] lemma diracProba_toMeasure_apply' (x : X) {A : Set X} (A_mble : MeasurableSet A) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply' x A_mble

@[simp] lemma diracProba_toMeasure_apply_of_mem {x : X} {A : Set X} (x_in_A : x ∈ A) :
    (diracProba x).toMeasure A = 1 := Measure.dirac_apply_of_mem x_in_A

@[simp] lemma diracProba_toMeasure_apply [MeasurableSingletonClass X] (x : X) (A : Set X) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply _ _

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The assignment `x ↦ diracProba x` is continuous `X → ProbabilityMeasure X`. -/
lemma continuous_diracProba : Continuous (fun (x : X) ↦ diracProba x) := by
  rw [continuous_iff_continuousAt]
  apply fun x ↦ ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f ↦ ?_
  have f_mble : Measurable (fun X ↦ (f X : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp only [diracProba, ProbabilityMeasure.coe_mk, lintegral_dirac' _ f_mble]
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt

/-- In a T0 topological space equipped with a sigma algebra which contains all open sets,
the assignment `x ↦ diracProba x` is injective. -/
lemma injective_diracProba_of_T0 [T0Space X] :
    Function.Injective (fun (x : X) ↦ diracProba x) := by
  intro x y δx_eq_δy
  by_contra x_ne_y
  exact dirac_ne_dirac x_ne_y <| congr_arg Subtype.val δx_eq_δy

lemma not_tendsto_diracProba_of_not_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X)
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
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, not_forall]
  use f
  simp only [diracProba, ProbabilityMeasure.coe_mk, fx_eq_one,
             lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable)]
  apply not_tendsto_iff_exists_frequently_nmem.mpr
  refine ⟨Ioi 0, Ioi_mem_nhds (by simp only [ENNReal.coe_one, zero_lt_one]),
          hU.mp (Eventually.of_forall ?_)⟩
  intro x x_notin_U
  rw [f_vanishes_outside x
        (compl_subset_compl.mpr (show interior U ⊆ U from interior_subset) x_notin_U)]
  simp only [ENNReal.coe_zero, mem_Ioi, lt_self_iff_false, not_false_eq_true]

lemma tendsto_diracProba_iff_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X) :
    Tendsto diracProba L (𝓝 (diracProba x)) ↔ Tendsto id L (𝓝 x) := by
  constructor
  · contrapose
    exact not_tendsto_diracProba_of_not_tendsto L
  · intro h
    have aux := (@continuous_diracProba X _ _ _).continuousAt (x := x)
    simp only [ContinuousAt] at aux
    exact aux.comp h

/-- An inverse function to `diracProba` (only really an inverse under hypotheses that
guarantee injectivity of `diracProba`). -/
noncomputable def diracProbaInverse : range (diracProba (X := X)) → X :=
  fun μ' ↦ (mem_range.mp μ'.prop).choose

-- We redeclare `X` here to temporarily avoid the `[TopologicalSpace X]` instance.
@[simp] lemma diracProba_diracProbaInverse {X : Type*} [MeasurableSpace X]
    (μ : range (diracProba (X := X))) :
    diracProba (diracProbaInverse μ) = μ := (mem_range.mp μ.prop).choose_spec

lemma diracProbaInverse_eq [T0Space X] {x : X} {μ : range (diracProba (X := X))}
    (h : μ = diracProba x) :
    diracProbaInverse μ = x := by
  apply injective_diracProba_of_T0 (X := X)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec

/-- In a T0 topological space `X`, the assignment `x ↦ diracProba x` is a bijection to its
range in `ProbabilityMeasure X`. -/
noncomputable def diracProbaEquiv [T0Space X] : X ≃ range (diracProba (X := X)) where
  toFun := fun x ↦ ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaInverse
  left_inv x := by apply diracProbaInverse_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaInverse])

/-- The composition of `diracProbaEquiv.symm` and `diracProba` is the subtype inclusion. -/
lemma diracProba_comp_diracProbaEquiv_symm_eq_val [T0Space X] :
    diracProba ∘ (diracProbaEquiv (X := X)).symm = fun μ ↦ μ.val := by
  funext μ; simp [diracProbaEquiv]

lemma tendsto_diracProbaEquivSymm_iff_tendsto [T0Space X] [CompletelyRegularSpace X]
    {μ : range (diracProba (X := X))} (F : Filter (range (diracProba (X := X)))) :
    Tendsto diracProbaEquiv.symm F (𝓝 (diracProbaEquiv.symm μ)) ↔ Tendsto id F (𝓝 μ) := by
  have key :=
    tendsto_diracProba_iff_tendsto (F.map diracProbaEquiv.symm) (x := diracProbaEquiv.symm μ)
  rw [← (diracProbaEquiv (X := X)).symm_comp_self, ← tendsto_map'_iff] at key
  simp only [tendsto_map'_iff, map_map, Equiv.self_comp_symm, map_id] at key
  simp only [← key, diracProba_comp_diracProbaEquiv_symm_eq_val]
  convert tendsto_subtype_rng.symm
  exact apply_rangeSplitting (fun x ↦ diracProba x) μ

/-- In a T0 topological space, `diracProbaEquiv` is continuous. -/
lemma continuous_diracProbaEquiv [T0Space X] :
    Continuous (diracProbaEquiv (X := X)) :=
  Continuous.subtype_mk continuous_diracProba mem_range_self

/-- In a completely regular T0 topological space, the inverse of `diracProbaEquiv` is continuous. -/
lemma continuous_diracProbaEquivSymm [T0Space X] [CompletelyRegularSpace X] :
    Continuous (diracProbaEquiv (X := X)).symm := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds (y := diracProbaInverse μ)
  exact (tendsto_diracProbaEquivSymm_iff_tendsto _).mpr fun _ mem_nhd ↦ mem_nhd

/-- In a completely regular T0 topological space `X`, `diracProbaEquiv` is a homeomorphism to
its image in `ProbabilityMeasure X`. -/
noncomputable def diracProbaHomeomorph [T0Space X] [CompletelyRegularSpace X] :
    X ≃ₜ range (diracProba (X := X)) :=
  @Homeomorph.mk X _ _ _ diracProbaEquiv continuous_diracProbaEquiv continuous_diracProbaEquivSymm

/-- If `X` is a completely regular T0 space with its Borel sigma algebra, then the mapping
that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
`X → ProbabilityMeasure X`. -/
theorem isEmbedding_diracProba [T0Space X] [CompletelyRegularSpace X] :
    IsEmbedding (fun (x : X) ↦ diracProba x) :=
  IsEmbedding.subtypeVal.comp diracProbaHomeomorph.isEmbedding

end embed_to_probabilityMeasure

end MeasureTheory

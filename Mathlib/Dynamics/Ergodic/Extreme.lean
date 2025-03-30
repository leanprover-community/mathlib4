/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
TODO
-/

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal Topology

instance HasCountableSeparatingOn.range_Iio {X : Type*} [TopologicalSpace X] [LinearOrder X]
    [OrderTopology X] [SecondCountableTopology X] {s : Set X} :
    HasCountableSeparatingOn X (· ∈ range Iio) s := by
  constructor
  rcases TopologicalSpace.exists_countable_dense X with ⟨s, hsc, hsd⟩
  set t := s ∪ {x | ∃ y, y ⋖ x}
  refine ⟨Iio '' t, .image ?_ _, ?_, ?_⟩
  · exact hsc.union countable_setOf_covBy_left
  · exact image_subset_range _ _
  · rintro x - y - h
    by_contra! hne
    wlog hlt : x < y generalizing x y
    · refine this y x ?_ hne.symm (hne.lt_or_lt.resolve_left hlt)
      simpa only [iff_comm] using h
    cases (Ioo x y).eq_empty_or_nonempty with
    | inl he =>
      specialize h (Iio y) (mem_image_of_mem _ (.inr ⟨x, hlt, by simpa using Set.ext_iff.mp he⟩))
      simp [hlt.not_le] at h
    | inr hne =>
      rcases hsd.inter_open_nonempty _ isOpen_Ioo hne with ⟨z, ⟨hxz, hzy⟩, hzs⟩
      simpa [hxz, hzy.not_lt] using h (Iio z) (mem_image_of_mem _ (.inl hzs))

instance HasCountableSeparatingOn.range_Ioi {X : Type*} [TopologicalSpace X] [LinearOrder X]
    [OrderTopology X] [SecondCountableTopology X] {s : Set X} :
    HasCountableSeparatingOn X (· ∈ range Ioi) s :=
  HasCountableSeparatingOn.range_Iio (X := Xᵒᵈ)

theorem Filter.EventuallyEq.of_forall_eventually_lt_iff {α X : Type*} [TopologicalSpace X]
    [LinearOrder X] [OrderTopology X] [SecondCountableTopology X]
    {l : Filter α} [CountableInterFilter l] {f g : α → X} (h : ∀ x, ∀ᶠ a in l, f a < x ↔ g a < x) :
    f =ᶠ[l] g :=
  -- TODO: why is this required?
  have : HasCountableSeparatingOn X (· ∈ range Iio) univ := inferInstance
  .of_forall_separating_preimage (· ∈ range Iio) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α} {f : α → α}

-- TODO: do we need `μ ≪ ν` here, or the absolutely continuous part is automatically invariant?
theorem MeasureTheory.MeasurePreserving.rnDeriv_comp_aeEq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) (hμν : μ ≪ ν) :
    μ.rnDeriv ν ∘ f =ᵐ[ν] μ.rnDeriv ν := by
  refine .of_forall_eventually_lt_iff fun c ↦ ?_
  set s := {a | μ.rnDeriv ν a < c}
  have hsm : MeasurableSet s := measurable_rnDeriv _ _ measurableSet_Iio
  have hμ_diff : μ (f ⁻¹' s \ s) = μ (s \ f ⁻¹' s) :=
    measure_diff_symm (hfμ.measurable hsm).nullMeasurableSet hsm.nullMeasurableSet
      (hfμ.measure_preimage hsm.nullMeasurableSet) (measure_ne_top _ _)
  have hν_diff : ν (f ⁻¹' s \ s) = ν (s \ f ⁻¹' s) :=
    measure_diff_symm (hfν.measurable hsm).nullMeasurableSet hsm.nullMeasurableSet
      (hfν.measure_preimage hsm.nullMeasurableSet) (measure_ne_top _ _)
  suffices f ⁻¹' s =ᵐ[ν] s from this.mem_iff
  suffices ν (f ⁻¹' s \ s) = 0 from (ae_le_set.mpr this).antisymm (ae_le_set.mpr <| hν_diff ▸ this)
  contrapose! hμ_diff with h₀
  apply ne_of_gt
  calc
    μ (s \ f ⁻¹' s) = ∫⁻ a in s \ f ⁻¹' s, μ.rnDeriv ν a ∂ν := (setLIntegral_rnDeriv hμν _).symm
    _ < ∫⁻ _ in s \ f ⁻¹' s, c ∂ν := by
      apply setLIntegral_strict_mono (hsm.diff (hfμ.measurable hsm)) (hν_diff ▸ h₀) measurable_const
      · rw [setLIntegral_rnDeriv hμν]
        apply measure_ne_top
      · exact .of_forall fun x hx ↦ hx.1
    _ = ∫⁻ _ in f ⁻¹' s \ s, c ∂ν := by simp [hν_diff]
    _ ≤ ∫⁻ a in f ⁻¹' s \ s, μ.rnDeriv ν a ∂ν :=
      setLIntegral_mono (by fun_prop) (fun x hx ↦ not_lt.mp hx.2)
    _ = μ (f ⁻¹' s \ s) := setLIntegral_rnDeriv hμν _

namespace Ergodic

/-- Given a constant `c ≠ ∞`, an extreme point of the set of measures that are invariant under `f`
and have total mass `c` is an ergodic measure. -/
theorem of_mem_extremePoints_meas_univ_eq {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = c}) : Ergodic f μ := by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert Ergodic.zero_measure hf.measurable
    rw [← Measure.measure_univ_eq_zero, h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have hfin : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have : ∀ s, MeasurableSet s → f ⁻¹' s = s → μ s ≠ 0 → c • μ[|s] ∈ S := by
      intro s hsm hfs hμs
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · convert hf.restrict_preimage hsm
        exact hfs.symm
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using H
    obtain ⟨hcond, -⟩ : c • μ[|s] = μ ∧ c • μ[|sᶜ] = μ := by
      apply h.2 (this s hsm hfs hs) (this sᶜ hsm.compl (by rw [preimage_compl, hfs]) hs')
      refine ⟨μ s / c, μ sᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
      · rw [← ENNReal.add_div, measure_add_measure_compl hsm, h.1.2, ENNReal.div_self hc₀ hc]
      · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
          ENNReal.mul_inv_cancel, *]
    rw [← hcond] at hs'
    simp [ProbabilityTheory.cond_apply, hsm] at hs'

/-- An extreme point of the set of invariant probability measures is an ergodic measure. -/
theorem of_mem_extremePoints
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) :
    Ergodic f μ :=
  .of_mem_extremePoints_meas_univ_eq ENNReal.one_ne_top <| by
    simpa only [isProbabilityMeasure_iff] using h

-- TODO: do we need `IsFiniteMeasure ν` here?
theorem eq_smul_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ)
    (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ∃ c : ℝ≥0∞, ν = c • μ := by
  have := hfν.rnDeriv_comp_aeEq hμ.toMeasurePreserving hνμ
  obtain ⟨c, hc⟩ := hμ.ae_eq_const_of_ae_eq_comp₀ (measurable_rnDeriv _ _).nullMeasurable this
  use c
  ext s hs
  calc
    ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm <| setLIntegral_rnDeriv hνμ _
    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
    _ = (c • μ) s := by simp

theorem eq_of_absolutelyContinuous_meas_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) :
    ν = μ := by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]

theorem eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ :=
  eq_of_absolutelyContinuous_meas_univ_eq hμ hfν hνμ <| by simp

theorem mem_extremePoints_meas_univ_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} := by
  rw [mem_extremePoints']
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_meas_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'

theorem mem_extremePoints [IsProbabilityMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} := by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_meas_univ_eq

end Ergodic

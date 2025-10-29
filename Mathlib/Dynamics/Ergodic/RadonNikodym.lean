/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Order.CountableSeparating

/-!
# Radon-Nikodym derivative of invariant measures

Given two finite invariant measures of a self-map,
we prove that their singular parts, their absolutely continuous parts,
and their Radon-Nikodym derivatives are invariant too.

For the first two theorems, we only assume that one of the measures is finite
and the other is σ-finite.

## TODO

It isn't clear if the finiteness assumptions are optimal in this file.
We should either weaken them, or describe an example showing that it's impossible.
-/

open MeasureTheory Measure Set

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X} [IsFiniteMeasure μ]

namespace MeasureTheory.MeasurePreserving

/-- The singular part of a finite invariant measure of a self-map
with respect to a σ-finite invariant measure is an invariant measure. -/
protected theorem singularPart [SigmaFinite ν] {f : X → X}
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) :
    MeasurePreserving f (μ.singularPart ν) (μ.singularPart ν) := by
  rcases (μ.mutuallySingular_singularPart ν).symm with ⟨s, hsm, hνs, hμs⟩
  convert hfμ.restrict_preimage hsm using 1
  · refine singularPart_eq_restrict ?_ (hfν.preimage_null hνs)
    rw [← mem_ae_iff, ← Filter.eventuallyEq_univ,
      ae_eq_univ_iff_measure_eq (hfμ.measurable hsm).nullMeasurableSet]
    calc
      μ.singularPart ν (f ⁻¹' s) = (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) (f ⁻¹' s) := by
        rw [← hfν.measure_preimage hsm.nullMeasurableSet] at hνs
        rw [add_apply, withDensity_absolutelyContinuous _ _ hνs, zero_add]
      _ = (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) s := by
        rw [rnDeriv_add_singularPart, hfμ.measure_preimage hsm.nullMeasurableSet]
      _ = μ.singularPart ν s := by
        rw [add_apply, withDensity_absolutelyContinuous _ _ hνs, zero_add]
      _ = μ.singularPart ν univ := by
        rw [← measure_add_measure_compl hsm, hμs, add_zero]
  · exact singularPart_eq_restrict hμs hνs

/-- The absolutely continuous part of a finite invariant measure of a self-map
with respect to a σ-finite invariant measure is an invariant measure. -/
protected theorem withDensity_rnDeriv [SigmaFinite ν] {f : X → X}
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) :
    MeasurePreserving f (ν.withDensity (μ.rnDeriv ν)) (ν.withDensity (μ.rnDeriv ν)) := by
  use hfμ.measurable
  ext s hs
  rw [← ENNReal.add_left_inj (measure_ne_top (μ.singularPart ν) s), map_apply hfμ.measurable hs,
    ← add_apply, rnDeriv_add_singularPart,
    ← (hfμ.singularPart hfν).measure_preimage hs.nullMeasurableSet, ← add_apply,
    rnDeriv_add_singularPart, hfμ.measure_preimage hs.nullMeasurableSet]

/-- The Radon-Nikodym derivative of a finite invariant measure of a self-map `f`
with respect to another finite invariant measure of `f` is a.e. invariant under `f`. -/
theorem rnDeriv_comp_aeEq [IsFiniteMeasure ν] {f : X → X}
    (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePreserving f ν ν) :
    μ.rnDeriv ν ∘ f =ᵐ[ν] μ.rnDeriv ν := by
  wlog hμν : μ ≪ ν generalizing μ
  · specialize this (hfμ.withDensity_rnDeriv hfν) (withDensity_absolutelyContinuous _ _)
    refine .trans (.trans ?_ this) (rnDeriv_withDensity ν (measurable_rnDeriv μ ν))
    apply hfν.quasiMeasurePreserving.ae_eq_comp
    exact (rnDeriv_withDensity ν (measurable_rnDeriv μ ν)).symm
  refine .of_forall_eventually_lt_iff fun c ↦ ?_
  set s := {a | μ.rnDeriv ν a < c}
  have hsm : MeasurableSet s := measurable_rnDeriv _ _ measurableSet_Iio
  have hμ_diff : μ (f ⁻¹' s \ s) = μ (s \ f ⁻¹' s) :=
    measure_diff_symm (hfμ.measurable hsm).nullMeasurableSet hsm.nullMeasurableSet
      (hfμ.measure_preimage hsm.nullMeasurableSet) (by finiteness)
  have hν_diff : ν (f ⁻¹' s \ s) = ν (s \ f ⁻¹' s) :=
    measure_diff_symm (hfν.measurable hsm).nullMeasurableSet hsm.nullMeasurableSet
      (hfν.measure_preimage hsm.nullMeasurableSet) (by finiteness)
  suffices f ⁻¹' s =ᵐ[ν] s from this.mem_iff
  suffices ν (f ⁻¹' s \ s) = 0 from (ae_le_set.mpr this).antisymm (ae_le_set.mpr <| hν_diff ▸ this)
  contrapose! hμ_diff with h₀
  apply ne_of_gt
  calc
    μ (s \ f ⁻¹' s) = ∫⁻ a in s \ f ⁻¹' s, μ.rnDeriv ν a ∂ν := (setLIntegral_rnDeriv hμν _).symm
    _ < ∫⁻ _ in s \ f ⁻¹' s, c ∂ν := by
      apply setLIntegral_strict_mono (hsm.diff (hfμ.measurable hsm)) (hν_diff ▸ h₀) measurable_const
      · rw [setLIntegral_rnDeriv hμν]
        finiteness
      · exact .of_forall fun x hx ↦ hx.1
    _ = ∫⁻ _ in f ⁻¹' s \ s, c ∂ν := by simp [hν_diff]
    _ ≤ ∫⁻ a in f ⁻¹' s \ s, μ.rnDeriv ν a ∂ν :=
      setLIntegral_mono (by fun_prop) (fun x hx ↦ not_lt.mp hx.2)
    _ = μ (f ⁻¹' s \ s) := setLIntegral_rnDeriv hμν _

end MeasureTheory.MeasurePreserving

/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `Asymptotics.IsBigO.integrableAtFilter`: If `f = O[l] g` on measurably generated `l`,
  `f` is strongly measurable at `l`, and `g` is integrable at `l`, then `f` is integrable at `l`.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`: If `f` is locally integrable,
  and `f =O[cocompact] g` for some `g` integrable at `cocompact`, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop`: If `f` is locally integrable,
  and `f =O[atBot] g`, `f =O[atTop] g'` for some `g`, `g'` integrable at `atBot` and `atTop`
  respectively, then `f` is integrable.
-/

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : α → E} {g : α → F} {a b : α} {μ : Measure α} {l : Filter α}

/-- If `f = O[l] g` on measurably generated `l`, `f` is strongly measurable at `l`,
and `g` is integrable at `l`, then `f` is integrable at `l`. -/
theorem _root_.Asymptotics.IsBigO.integrableAtFilter [IsMeasurablyGenerated l]
    (hf : f =O[l] g) (hfm : StronglyMeasurableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  let C' : NNReal := ⟨max C 0, le_max_right C 0⟩
  obtain ⟨s, hsl, hs⟩ := hC.exists_mem
  obtain ⟨t, htl, ht⟩ := hg
  obtain ⟨u, hul, hu⟩ := hfm
  obtain ⟨S, hS, hs_meas, hs_le⟩ :=
    IsMeasurablyGenerated.exists_measurable_subset <| inter_mem (inter_mem hsl htl) hul
  use S, hS, hu.mono_measure <| Measure.restrict_mono (fun _ hx ↦ (hs_le hx).2) le_rfl
  calc
    _ ≤ ∫⁻ (x : α) in S, C' * ‖g x‖₊ ∂μ := by
      refine lintegral_mono_ae <| (ae_restrict_iff' hs_meas).mpr <| ae_of_all _ fun x hx => ?_
      rewrite [← ENNReal.coe_mul, ENNReal.coe_le_coe]
      refine (hs x (hs_le hx).1.1).trans ?_
      show C * ‖g x‖ ≤ (max C 0) * ‖g x‖
      gcongr
      apply le_max_left
    _ = C' * ∫⁻ (x : α) in S, ↑‖g x‖₊ ∂μ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_ne_top <| ne_top_of_lt
      <| ht.mono_set (fun _ hx ↦ (hs_le hx).1.2) |>.2

/-- Variant of `MeasureTheory.Integrable.mono` taking `f =O[⊤] (g)` instead of `‖f(x)‖ ≤ ‖g(x)‖` -/
theorem _root_.Asymptotics.IsBigO.integrable (hfm : AEStronglyMeasurable f μ)
    (hf : f =O[⊤] g) (hg : Integrable g μ) : Integrable f μ := by
  rewrite [← integrableAtFilter_top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg

variable [TopologicalSpace α] [SecondCountableTopology α]

namespace MeasureTheory

/-- If `f` is locally integrable, and `f =O[cocompact] g` for some `g` integrable at `cocompact`,
then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_cocompact [IsMeasurablyGenerated (cocompact α)]
    (hf : LocallyIntegrable f μ) (ho : f =O[cocompact α] g)
    (hg : IntegrableAtFilter g (cocompact α) μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_cocompact.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

variable [LinearOrder α] [CompactIccSpace α] {g' : α → F}

/-- If `f` is locally integrable, and `f =O[atBot] g`, `f =O[atTop] g'` for some
`g`, `g'` integrable at `atBot` and `atTop` respectively, then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_atBot_atTop
    [IsMeasurablyGenerated (atBot (α := α))] [IsMeasurablyGenerated (atTop (α := α))]
    (hf : LocallyIntegrable f μ)
    (ho : f =O[atBot] g) (hg : IntegrableAtFilter g atBot μ)
    (ho' : f =O[atTop] g') (hg' : IntegrableAtFilter g' atTop μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨ho.integrableAtFilter ?_ hg, ho'.integrableAtFilter ?_ hg'⟩, hf⟩
  all_goals exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

/-- If `f` is locally integrable on `(∞, a]`, and `f =O[atBot] g`, for some
`g` integrable at `atBot`, then `f` is integrable on `(∞, a]`. -/
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    (hf : LocallyIntegrableOn f (Iic a) μ) (ho : f =O[atBot] g)
    (hg : IntegrableAtFilter g atBot μ) : IntegrableOn f (Iic a) μ := by
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Iic a, Iic_mem_atBot a, hf.aestronglyMeasurable⟩

/-- If `f` is locally integrable on `[a, ∞)`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable on `[a, ∞)`. -/
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atTop [IsMeasurablyGenerated (atTop (α := α))]
    (hf : LocallyIntegrableOn f (Ici a) μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : IntegrableOn f (Ici a) μ := by
  refine integrableOn_Ici_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Ici a, Ici_mem_atTop a, hf.aestronglyMeasurable⟩

/-- If `f` is locally integrable, `f` has a bottom element, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    [OrderTop α] (hf : LocallyIntegrable f μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  sorry

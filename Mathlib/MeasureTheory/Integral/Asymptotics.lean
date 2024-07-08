/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Group.Measure
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
  and `f =O[atBot] g`, `f =O[atTop] g'` for some `g`, `g'` integrable `atBot` and `atTop`
  respectively, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant`:
  If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g` for some
  `g` integrable `atTop`, then `f` is integrable.
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
  obtain ⟨s, hsl, hsm, hfg, hf, hg⟩ :=
    (hC.smallSets.and <| hfm.eventually.and hg.eventually).exists_measurable_mem_of_smallSets
  refine ⟨s, hsl, (hg.norm.const_mul C).mono hf ?_⟩
  refine (ae_restrict_mem hsm).mono fun x hx ↦ ?_
  exact (hfg x hx).trans (le_abs_self _)

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

section LinearOrder

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

/-- If `f` is locally integrable, `f` has a top element, and `f =O[atBot] g`, for some
`g` integrable at `atBot`, then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    [OrderTop α] (hf : LocallyIntegrable f μ) (ho : f =O[atBot] g)
    (hg : IntegrableAtFilter g atBot μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

/-- If `f` is locally integrable, `f` has a bottom element, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_atTop [IsMeasurablyGenerated (atTop (α := α))]
    [OrderBot α] (hf : LocallyIntegrable f μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

end LinearOrder

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] [CompactIccSpace α]

/-- If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    [IsMeasurablyGenerated (atTop (α := α))] [MeasurableNeg α] [μ.IsNegInvariant]
    (hf : LocallyIntegrable f μ) (hsymm : norm ∘ f =ᵐ[μ] norm ∘ f ∘ Neg.neg) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  have h_int := (hf.locallyIntegrableOn (Ici 0)).integrableOn_of_isBigO_atTop ho hg
  rw [← integrableOn_univ, ← Iic_union_Ici_of_le le_rfl, integrableOn_union]
  refine ⟨?_, h_int⟩
  have h_map_neg : (μ.restrict (Ici 0)).map Neg.neg = μ.restrict (Iic 0) := by
    conv => rhs; rw [← Measure.map_neg_eq_self μ, measurableEmbedding_neg.restrict_map]
    simp
  rw [IntegrableOn, ← h_map_neg, measurableEmbedding_neg.integrable_map_iff]
  refine h_int.congr' ?_ hsymm.restrict
  refine AEStronglyMeasurable.comp_aemeasurable ?_ measurable_neg.aemeasurable
  exact h_map_neg ▸ hf.aestronglyMeasurable.restrict

end LinearOrderedAddCommGroup

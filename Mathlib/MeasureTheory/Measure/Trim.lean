/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Typeclasses

/-!
# Restriction of a measure to a sub-σ-algebra


## Main definitions

* `MeasureTheory.Measure.trim`: restriction of a measure to a sub-sigma algebra.

-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*}

/-- Restriction of a measure to a sub-σ-algebra.
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `OuterMeasure.trim`, see the lemma
`toOuterMeasure_trim_eq_trim_toOuterMeasure`. -/
noncomputable
def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m ≤ m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))
#align measure_theory.measure.trim MeasureTheory.Measure.trim

@[simp]
theorem trim_eq_self [MeasurableSpace α] {μ : Measure α} : μ.trim le_rfl = μ := by
  simp [Measure.trim]
#align measure_theory.trim_eq_self MeasureTheory.trim_eq_self

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

theorem toOuterMeasure_trim_eq_trim_toOuterMeasure (μ : Measure α) (hm : m ≤ m0) :
    @Measure.toOuterMeasure _ m (μ.trim hm) = @OuterMeasure.trim _ m μ.toOuterMeasure := by
  rw [Measure.trim, toMeasure_toOuterMeasure (ms := m)]
#align measure_theory.to_outer_measure_trim_eq_trim_to_outer_measure MeasureTheory.toOuterMeasure_trim_eq_trim_toOuterMeasure

@[simp]
theorem zero_trim (hm : m ≤ m0) : (0 : Measure α).trim hm = (0 : @Measure α m) := by
  simp [Measure.trim, @OuterMeasure.toMeasure_zero _ m]
#align measure_theory.zero_trim MeasureTheory.zero_trim

theorem trim_measurableSet_eq (hm : m ≤ m0) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s := by
  rw [Measure.trim, toMeasure_apply (ms := m) _ _ hs, Measure.coe_toOuterMeasure]
#align measure_theory.trim_measurable_set_eq MeasureTheory.trim_measurableSet_eq

theorem le_trim (hm : m ≤ m0) : μ s ≤ μ.trim hm s := by
  simp_rw [Measure.trim]
  exact @le_toMeasure_apply _ m _ _ _
#align measure_theory.le_trim MeasureTheory.le_trim

lemma trim_add {ν : Measure α} (hm : m ≤ m0) : (μ + ν).trim hm = μ.trim hm + ν.trim hm :=
  @Measure.ext _ m _ _ (fun s hs ↦ by simp [trim_measurableSet_eq hm hs])

theorem measure_eq_zero_of_trim_eq_zero (hm : m ≤ m0) (h : μ.trim hm s = 0) : μ s = 0 :=
  le_antisymm ((le_trim hm).trans (le_of_eq h)) (zero_le _)
#align measure_theory.measure_eq_zero_of_trim_eq_zero MeasureTheory.measure_eq_zero_of_trim_eq_zero

theorem measure_trim_toMeasurable_eq_zero {hm : m ≤ m0} (hs : μ.trim hm s = 0) :
    μ (@toMeasurable α m (μ.trim hm) s) = 0 :=
  measure_eq_zero_of_trim_eq_zero hm (by rwa [@measure_toMeasurable _ m])
#align measure_theory.measure_trim_to_measurable_eq_zero MeasureTheory.measure_trim_toMeasurable_eq_zero

theorem ae_of_ae_trim (hm : m ≤ m0) {μ : Measure α} {P : α → Prop} (h : ∀ᵐ x ∂μ.trim hm, P x) :
    ∀ᵐ x ∂μ, P x :=
  measure_eq_zero_of_trim_eq_zero hm h
#align measure_theory.ae_of_ae_trim MeasureTheory.ae_of_ae_trim

theorem ae_eq_of_ae_eq_trim {E} {hm : m ≤ m0} {f₁ f₂ : α → E}
    (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12
#align measure_theory.ae_eq_of_ae_eq_trim MeasureTheory.ae_eq_of_ae_eq_trim

theorem ae_le_of_ae_le_trim {E} [LE E] {hm : m ≤ m0} {f₁ f₂ : α → E}
    (h12 : f₁ ≤ᵐ[μ.trim hm] f₂) : f₁ ≤ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12
#align measure_theory.ae_le_of_ae_le_trim MeasureTheory.ae_le_of_ae_le_trim

theorem trim_trim {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ ≤ m₂} {hm₂ : m₂ ≤ m0} :
    (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂) := by
  refine @Measure.ext _ m₁ _ _ (fun t ht => ?_)
  rw [trim_measurableSet_eq hm₁₂ ht, trim_measurableSet_eq (hm₁₂.trans hm₂) ht,
    trim_measurableSet_eq hm₂ (hm₁₂ t ht)]
#align measure_theory.trim_trim MeasureTheory.trim_trim

theorem restrict_trim (hm : m ≤ m0) (μ : Measure α) (hs : @MeasurableSet α m s) :
    @Measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm := by
  refine @Measure.ext _ m _ _ (fun t ht => ?_)
  rw [@Measure.restrict_apply α m _ _ _ ht, trim_measurableSet_eq hm ht,
    Measure.restrict_apply (hm t ht),
    trim_measurableSet_eq hm (@MeasurableSet.inter α m t s ht hs)]
#align measure_theory.restrict_trim MeasureTheory.restrict_trim

instance isFiniteMeasure_trim (hm : m ≤ m0) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.trim hm) where
  measure_univ_lt_top := by
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_lt_top _ _
#align measure_theory.is_finite_measure_trim MeasureTheory.isFiniteMeasure_trim

theorem sigmaFiniteTrim_mono {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    (hm₂ : m₂ ≤ m) [SigmaFinite (μ.trim (hm₂.trans hm))] : SigmaFinite (μ.trim hm) := by
  refine ⟨⟨?_⟩⟩
  refine
    { set := spanningSets (μ.trim (hm₂.trans hm))
      set_mem := fun _ => Set.mem_univ _
      finite := fun i => ?_
      spanning := iUnion_spanningSets _ }
  calc
    (μ.trim hm) (spanningSets (μ.trim (hm₂.trans hm)) i) =
        ((μ.trim hm).trim hm₂) (spanningSets (μ.trim (hm₂.trans hm)) i) := by
      rw [@trim_measurableSet_eq α m₂ m (μ.trim hm) _ hm₂ (measurable_spanningSets _ _)]
    _ = (μ.trim (hm₂.trans hm)) (spanningSets (μ.trim (hm₂.trans hm)) i) := by
      rw [@trim_trim _ _ μ _ _ hm₂ hm]
    _ < ∞ := measure_spanningSets_lt_top _ _
#align measure_theory.sigma_finite_trim_mono MeasureTheory.sigmaFiniteTrim_mono

theorem sigmaFinite_trim_bot_iff : SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ := by
  rw [sigmaFinite_bot_iff]
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩ <;> have h_univ := h.measure_univ_lt_top
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ] at h_univ
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ]
#align measure_theory.sigma_finite_trim_bot_iff MeasureTheory.sigmaFinite_trim_bot_iff

lemma Measure.AbsolutelyContinuous.trim {ν : Measure α} (hμν : μ ≪ ν) (hm : m ≤ m0) :
    μ.trim hm ≪ ν.trim hm := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hsν ↦ ?_)
  rw [trim_measurableSet_eq hm hs] at hsν ⊢
  exact hμν hsν

end MeasureTheory

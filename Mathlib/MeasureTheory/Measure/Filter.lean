/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# Filters related to measures

This file provides some properties of `ae` the filter of sets whose complement has measure `0`.
Most of these properties are in this file because they either require the module structure
or the lattice structure of the space of measures.

We also define `cofinite` the filter of sets whose complement has finite measure.

## Tags

measure, almost everywhere, cofinite
-/

public section

open Set Filter
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : MeasureTheory.Measure α} {s t : Set α}

section AE

open Measure

@[simp]
theorem ae_eq_bot : ae μ = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]

@[simp]
theorem ae_neBot : (ae μ).NeBot ↔ μ ≠ 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)

instance [NeZero μ] : (ae μ).NeBot := ae_neBot.2 <| NeZero.ne μ

@[simp]
theorem ae_zero : ae (0 : Measure α) = ⊥ :=
  ae_eq_bot.2 rfl

@[gcongr, mono]
theorem ae_mono (h : μ ≤ ν) : ae μ ≤ ae ν :=
  fun s hs ↦ bot_unique <| (h sᶜ).trans_eq hs

instance : IsMeasurablyGenerated (ae μ) :=
  ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

protected theorem AEDisjoint.of_le (h : AEDisjoint μ s t) (h' : ν ≤ μ) :
    AEDisjoint ν s t :=
  bot_unique <| (h' (s ∩ t)).trans_eq h

theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (h' : ν ≤ μ) :
    NullMeasurableSet s ν := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, ht, hst.filter_mono (ae_mono h')⟩

lemma NullMeasurableSet.smul_measure (h : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    NullMeasurableSet s (c • μ) := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, ht, hst.filter_mono (ae_smul_measure_le c)⟩

lemma nullMeasurableSet_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    NullMeasurableSet s (c • μ) ↔ NullMeasurableSet s μ := by
  simp only [nullMeasurableSet_iff_eventuallyMeasurableSet, μ.ae_ennreal_smul_measure_eq hc]

theorem _root_.AEMeasurable.mono_measure {f : α → β} (h : AEMeasurable f μ) (h' : ν ≤ μ) :
    AEMeasurable f ν := by
  obtain ⟨g, hg, hfg⟩ := h
  exact ⟨g, hg, hfg.filter_mono (ae_mono h')⟩

theorem Measure.measure_support_eq_zero_iff {E : Type*} [Zero E] (μ : Measure α := by volume_tac)
    {f : α → E} : μ f.support = 0 ↔ f =ᵐ[μ] 0 := by
  rfl

end AE

section Cofinite

namespace Measure

/-! ### The `cofinite` filter -/

/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
@[expose]
def cofinite (μ : Measure α) : Filter α :=
  comk (μ · < ∞) (by simp) (fun _ ht _ hs ↦ (measure_mono hs).trans_lt ht) fun s hs t ht ↦
    (measure_union_le s t).trans_lt <| ENNReal.add_lt_top.2 ⟨hs, ht⟩

theorem mem_cofinite : s ∈ μ.cofinite ↔ μ sᶜ < ∞ :=
  Iff.rfl

theorem compl_mem_cofinite : sᶜ ∈ μ.cofinite ↔ μ s < ∞ := by rw [mem_cofinite, compl_compl]

theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞ :=
  Iff.rfl

instance : IsMeasurablyGenerated μ.cofinite where
  exists_measurable_subset s hs := by
    refine ⟨(toMeasurable μ sᶜ)ᶜ, ?_, (measurableSet_toMeasurable _ _).compl, ?_⟩
    · rwa [compl_mem_cofinite, measure_toMeasurable]
    · rw [compl_subset_comm]
      apply subset_toMeasurable

theorem cofinite_le_ae : μ.cofinite ≤ ae μ := by
  intro s hs
  simp_all [mem_cofinite, mem_ae_iff]

end Measure

end Cofinite

end MeasureTheory

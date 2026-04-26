/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# `L^p`-seminorms on `count` and `dirac`
-/

public section

open MeasureTheory Measure ENNReal Set Filter
variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p : ℝ≥0∞} {x : α}

namespace MeasureTheory

@[simp]
lemma eLpNorm_dirac (f : α → ε) (i : α) (hp : p ≠ 0) :
    eLpNorm f p (dirac i) = ‖f i‖ₑ := by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Set.Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]

lemma enorm_le_eLpNorm_count (f : α → ε) (i : α) (hp : p ≠ 0) :
    ‖f i‖ₑ ≤ eLpNorm f p count := by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac f i hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ ≤ eLpNorm f p count := eLpNorm_restrict_le ..

omit [MeasurableSingletonClass α] in
lemma eLpNorm_count_lt_top_of_lt [Finite α] (h : ∀ i, ‖f i‖ₑ < ∞) :
    eLpNorm f p .count < ∞ := by
  letI _ := Fintype.ofFinite α
  let C : ℝ≥0∞ := Finset.univ.sup (‖f ·‖ₑ)
  have hC : ∀ x, ‖f x‖ₑ ≤ C := fun x => Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ x)
  have hC_lt : C < ∞ := by
    simp [C, Finset.sup_lt_iff, h]
  refine (eLpNorm_mono_enorm (μ := (count : Measure α)) (p := p) (f := f)
    (g := fun _ : α => C) fun x => by simpa [C] using hC x).trans_lt ?_
  exact (memLp_const_enorm (μ := (count : Measure α)) (p := p) (c := C) hC_lt.ne).eLpNorm_lt_top

lemma eLpNorm_count_lt_top [Finite α] (hp : p ≠ 0) :
    eLpNorm f p .count < ∞ ↔ ∀ i, ‖f i‖ₑ < ∞ :=
  ⟨fun h i ↦ (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

end MeasureTheory

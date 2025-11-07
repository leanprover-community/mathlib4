/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# ℒp spaces and products

-/

open scoped ENNReal

namespace MeasureTheory

variable {α β ε : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

lemma MemLp.comp_fst {f : α → ε} (hf : MemLp f p μ) (ν : Measure β) [IsFiniteMeasure ν] :
    MemLp (fun x ↦ f x.1) p (μ.prod ν) := by
  have hf' : MemLp f p (ν .univ • μ) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.fst) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

lemma MemLp.comp_snd {f : β → ε} (hf : MemLp f p ν) (μ : Measure α) [IsFiniteMeasure μ]
    [SFinite ν] :
    MemLp (fun x ↦ f x.2) p (μ.prod ν) := by
  have hf' : MemLp f p (μ .univ • ν) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.snd) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

end MeasureTheory

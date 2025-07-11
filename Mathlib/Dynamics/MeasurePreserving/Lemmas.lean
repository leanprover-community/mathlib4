/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Lemmas associated to measure preserving systems

`MeasurePreserving` is defined in `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`. Here we have
some associated results which are best not placed in the same file because they need additional
imports.

-/

namespace MeasurePreserving

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} [MeasurableSpace α] {μ : Measure α} {φ : α → ℝ}

/-- If an observable is integrable then the observable formed by composing with iterates of a
measure preserving map is also integrable. -/
lemma comp_iterate_integrable {i : ℕ} (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) :
    Integrable (φ ∘ f^[i]) μ := by
  apply (integrable_map_measure _ _).mp
  · rwa [(hf.iterate i).map_eq]
  · rw [(hf.iterate i).map_eq]
    exact hφ.aestronglyMeasurable
  exact (hf.iterate i).measurable.aemeasurable

end MeasurePreserving

/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib

open MeasureTheory

variable {α : Type*} {m : MeasurableSpace α}

example (μ : FiniteMeasure α) (f : α → ℂ) (hf : Integrable f μ) (S : Set ℂ) (hS : IsClosed S)
    (h : ∀ E : Set α, MeasurableSet E → 0 < μ E → (∫ x in E, f x ∂μ) / (μ E : ℂ) ∈ S) :
    ∀ᵐ x ∂(μ : Measure α), f x ∈ S := sorry

example (μ : ComplexMeasure α) : IsFiniteMeasure μ.variation := sorry

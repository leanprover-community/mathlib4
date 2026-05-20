/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurability of Birkhoff sums
-/

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {f : α → α} {g : α → ℝ} {n : ℕ} {μ : Measure α}

@[fun_prop]
public lemma birkhoffSum_measurable (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffSum f g n) := by
  apply Finset.measurable_sum
  measurability

@[fun_prop]
public lemma birkhoffSum_aestronglyMeasurable (hf : MeasurePreserving f μ μ)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffSum f g n) μ := by
  apply Finset.aestronglyMeasurable_fun_sum
  exact fun i _ ↦ hg.comp_measurePreserving (hf.iterate i)

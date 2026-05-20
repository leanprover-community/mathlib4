/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability of Birkhoff sums
-/

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {f : α → α} {g : α → ℝ} {n : ℕ} {μ : Measure α}

public lemma birkhoffSum_integrable (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    Integrable (birkhoffSum f g n) μ :=
  integrable_finsetSum _ fun _ _ ↦ (hf.iterate _).integrable_comp_of_integrable hg

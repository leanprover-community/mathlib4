/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.NormedSpace.FiniteDimension

/-!
# Rademacher theorem: a Lipschitz function is differentiable almost everywhere

-/

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Filter

/-
noncomputable def directionalDeriv (f : E → ℝ) (v : E) (x : E) : ℝ :=
  limsup (fun (n : ℕ) ↦ n • (f (x + ((1 : ℝ)/n) • v) - f x)) (atTop : Filter ℕ)

lemma measurable_directionalDeriv {f : E → ℝ} (hf : Continuous f) (v : E) :
    Measurable (directionalDeriv f v) := by
  have Z := measurable_limsup (f := (fun (n : ℕ) (x : E) ↦ n • (f (x + ((1 : ℝ)/n) • v) - f x)))


#exit

lemma zoug : trivial := sorry
-/

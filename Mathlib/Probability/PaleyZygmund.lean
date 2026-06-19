/-
Copyright (c) 2026 Yanxin Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yanxin Zhou
-/
module


public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!

# Paley–Zygmund inequality
This file contains the *Paley-Zygmund inequality* which states that,
given a nonnegative random variable Z with finite variance, if 0 ≤ θ ≤ 1,
then P(Z > θ EZ) ≥ (1-θ)^2 (EZ)^2/EZ^2. The proof uses Cauchy-Schwarz inequality.

## Main Result
- `ProbabilityTheory.paley_zygmund`: the Paley-Zygmund inequality.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}








end ProbabilityTheory

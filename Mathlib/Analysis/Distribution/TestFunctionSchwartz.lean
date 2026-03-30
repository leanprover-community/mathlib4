/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ramabadran, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Compactly supported smooth functions as Schwartz functions

This file defines the canonical continuous linear map from test functions to Schwartz functions,
and the induced (linear) restriction map from tempered distributions to distributions.
-/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped Distributions SchwartzMap

variable {𝕜 E F : Type*}

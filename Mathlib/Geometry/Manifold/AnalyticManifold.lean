/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee, Geoffrey Irving
-/
module

public import Mathlib.Deprecated.AnalyticManifold

@[expose] public section

deprecated_module
  "Analytic manifolds are deprecated, use `IsManifold I ω M`" (since := "2025-04-13")

set_option linter.directoryDependency false

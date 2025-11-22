/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module "The lift_lets tactic was moved to Lean core; \
  you can probably just remove this import" (since := "2025-05-02")

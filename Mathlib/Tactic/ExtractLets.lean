/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Lean.Expr.Basic
public import Mathlib.Tactic.Basic
public import Batteries.Tactic.Lint.Misc
public import Mathlib.Tactic.Linter.DeprecatedModule

@[expose] public section

deprecated_module "The extract_let tactic was moved to Lean core; \
  you can probably just remove this import" (since := "2025-05-02")

/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Throwaway test of the style autofix workflow

Do not merge. This file is not imported in `Mathlib.lean`, and the `example` below has a space
before a semicolon. `lake exe mk_all` and `lake exe lint-style --fix` should fix both.
-/

example : True ∧ True := by
  constructor; trivial; trivial

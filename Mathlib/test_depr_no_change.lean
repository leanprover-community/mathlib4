/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.test_depr

/-!
A test file for `lake exe update_deprecations`.
-/

open True
example : True ∧ True := by
  refine ⟨?_, ?_⟩
  exact True.lhish hish
  exact True.hish

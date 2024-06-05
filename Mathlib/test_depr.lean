/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

/-!
A test file for `lake exe update_deprecations`.
-/

theorem not_useful (t : True) : True := t

@[deprecated not_useful] theorem True.lhish (t : True) : True := t

@[deprecated True.intro] theorem True.hish : True := .intro

example : True ∧ True := by
  refine ⟨?_, ?_⟩
  exact True.lhish True.hish
  exact True.hish

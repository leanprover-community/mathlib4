/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.SOS

open SOS CPoly

-- End-to-end tactic regression for issue #50 / Harrison sos.ml:1623.
-- This primarily checks that the search terminates and returns a
-- kernel-checked certificate for the formerly hanging affine strict
-- case.
example (x a : ℝ) (_h1 : 3*x + 7*a < 4) (_h2 : 3 < 2*x) :
    a < 0 := by sos

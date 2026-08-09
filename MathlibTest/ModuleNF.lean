/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

import Mathlib.Tactic.ModuleNF

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (a b : R) (x : M) : a • x + b • x = (a + b) • x := by module_nf

example {V : Type*} [AddCommMonoid V] (x y : V) : x + (y + x) = x + x + y := by module_nf

example (a b : R) (x : M) : a • x - b • x = (a - b) • x := by module_nf

example (a : R) (v w : M) :
    (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by module_nf

example (a b : R) (x : M) : a • b • x = (a * b) • x := by module_nf

example (a b : R) (x : M) (h : (a + b) • x = 0) : a • x + b • x = 0 := by
  module_nf
  exact h

example (a b : R) (x : M) (h : a • x + b • x = 0) : (b + a) • x = 0 := by
  module_nf at h ⊢
  exact h

example (x y : M) (h : 2 • x + y = 0) : x + (y + x) = 0 := by
  module_nf
  exact h

example (f : M → M) (a b : R) (x : M) :
    f (a • x + b • x) = f ((a + b) • x) := by
  fail_if_success module
  module_nf

example [Preorder M] (a b : R) (x : M) (h : (a + b) • x ≤ 0) : a • x + b • x ≤ 0 := by
  module_nf
  exact h

-- atoms are identified at `.instances` transparency, like `match_scalars` and `module`:
-- `((2 : ℕ) : R)` and `(2 : R)` are the same atom
example (f : R → M) : f ((2 : ℕ) : R) + f ((2 : ℕ) : R) = f (2 : R) + f ((2 : ℕ) : R) := by
  module_nf

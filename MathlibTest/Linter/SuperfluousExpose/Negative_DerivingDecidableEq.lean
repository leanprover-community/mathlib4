/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a structure with `deriving DecidableEq`. Lean exposes the body of the derived
instance in every public section, but the derived `decEq` function is a `def` whose body the
section modifier controls, and the `decide` proof below reads it. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.DerivingDecidableEq

structure Point where
  x : Nat
  y : Nat
deriving DecidableEq

theorem point_eq : (⟨0, 0⟩ : Point) = ⟨0, 0⟩ := by decide

end SuperfluousExposeTest.DerivingDecidableEq

end

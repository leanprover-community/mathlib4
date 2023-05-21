/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis
-/
import Lean.Meta.Tactic.Simp.SimpTheorems

/-! # Internal simp attribute for `qify` tactic -/

/-- The simpset `qify_simps` is used by the tactic `qify` to moved expression from `ℕ` or `ℤ` to `ℚ`
which gives a well-behaved division. -/
register_simp_attr qify_simps

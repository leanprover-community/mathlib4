/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis
-/
import Lean.Meta.Tactic.Simp.SimpTheorems

/-! # Internal simp attribute for `zify` tactic -/

/-- The simpset `zify_simps` is used by the tactic `zify` to moved expression from `ℕ` to `ℤ`
which gives a well-behaved subtraction. -/
register_simp_attr zify_simps

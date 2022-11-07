/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Lean.Meta.Tactic.Simp.SimpTheorems

/-! # Register the `simp` tag for the `nontriviality` tactic. -/

/-- Simp lemmas for `nontriviality` tactic -/
register_simp_attr nontriviality

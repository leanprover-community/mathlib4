/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module

public import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

/-! TODO: Move this to `Mathlib/Tactic/Attr/Register.lean` before merging -/

public meta section

/-- `coassoc_simps` is a simp set useful to prove tautologies on coalgebras.
It mimics the strategy of `mon_tauto`.
See the docstring of `mon_tauto` for a more detailed overview. -/
register_simp_attr coassoc_simps

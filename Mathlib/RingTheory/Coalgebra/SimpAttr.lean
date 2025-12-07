module

public import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

public meta section

/-- `coassoc_simps` is a simp set useful to prove tautologies on coalgebras.
It mimics the strategy of `mon_tauto`.
See the docstring of `mon_tauto` for a more detailed overview. -/
register_simp_attr coassoc_simps

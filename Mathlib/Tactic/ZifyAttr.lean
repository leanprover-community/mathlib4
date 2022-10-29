import Lean

/-- The simpset `zify_simps` is used by the tactic `zify` to moved expression from `ℕ` to `ℤ`
which gives a well-behaved substraction. -/
register_simp_attr zify_simps

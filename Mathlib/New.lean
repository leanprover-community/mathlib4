import Mathlib.Tactic.Linter.RemoveDeprecations

example := 0

-- A comment for a result that should disappear
example := 1

-- A comment for `I_should_be_kept`
@[deprecated (since := "2025-07-01")] theorem I_should_be_kept : True := trivial

@[deprecated (since := "2025-07-01")] example : True := trivial

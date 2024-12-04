import Mathlib.Tactic.Linter.LetLinter


example : let n := 7; n = 7 := rfl

set_option linter.let true in
example : let n := 7; n = 7 := rfl

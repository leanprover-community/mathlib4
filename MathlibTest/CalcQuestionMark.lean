import Mathlib.Tactic.Widget.Calc

/-!
Note that while the suggestions look incorrectly indented here,
this is an artifact of the rendering to a string for `guard_msgs` (https://github.com/leanprover/lean4/issues/7191).

When used from the widget that appears in VSCode, they insert correctly-indented code.
-/

/--
info: Create calc tactic:
  • calc
        1 = 1 := by sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 1 = 1 := by
  have := 0
  calc?


/--
info: Create calc tactic:
  • calc
        a ≤ a := by sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a : Nat) : a ≤ a := by
  calc?

-- an indented `calc?`

/--
info: Create calc tactic:
  • calc
          a ≤ a := by sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a : Nat) : a ≤ a := by
  all_goals
    calc?

-- a deliberately long line
/--
info: Create calc tactic:
  • calc
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                            1 +
                          1 +
                        1 +
                      1 +
                    1 +
                  1 +
                1 +
              1 =
            8 + 8 + 8 + 8 :=
          by sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example :
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 + 8 + 8 + 8 := by
  calc?

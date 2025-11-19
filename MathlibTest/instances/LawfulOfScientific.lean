import Mathlib

-- `grind` will infer these instances often, so it is important that they remain fast.

set_option maxHeartbeats 10 in
#guard_msgs in
example : Lean.Grind.LawfulOfScientific ℚ := inferInstance

set_option maxHeartbeats 100 in
#guard_msgs in
example : Lean.Grind.LawfulOfScientific ℝ := inferInstance

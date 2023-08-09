import Mathlib.Tactic.Change
import Std.Tactic.GuardMsgs

set_option pp.unicode.fun true

/-- info: change 0 = 1
---
info: change (fun x ↦ x) 0 = 1
---
info: change (fun x ↦ x) 0 = 1
---
error: The given term is not DefEq to the goal
-/
#guard_msgs in
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- change 0 = 1
  change?        -- change (fun x ↦ x) 0 = 1
  change? _      -- change (fun x ↦ x) 0 = 1
  change? 1 = _  -- The given term is not DefEq to the goal

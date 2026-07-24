import Mathlib.Tactic.EnsureConstructive
import Mathlib.Data.List.Basic

opaque a : Bool
noncomputable def x : Bool := Classical.choice inferInstance
noncomputable def y : Bool := x
noncomputable def z : Bool := x || y || a

/--
error: `z` is not constructive. It depends on

• `a` (opaque)
• `Classical.choice` (axiom)

via the following paths:
z
├a ❌️ (opaque)
├y
│└x
│ └Classical.choice ❌️ (axiom)
└x
 └(⋯)
-/
#guard_msgs in
ensure_constructive z

/--
error: `z` is not constructive. It depends on

• `a` (opaque)

via the following paths:
z
└a ❌️ (opaque)
-/
#guard_msgs in
ensure_constructive z up_to x

/-- warning: `List.map` does not produce a violation in `z`, and may be removed. -/
#guard_msgs (warning, drop error) in
ensure_constructive z up_to x, List.map

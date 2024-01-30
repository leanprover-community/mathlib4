import Mathlib.Tactic.Eqns
import Std.Tactic.GuardMsgs

def t : Nat := 0 + 1

theorem t_def : t = 1 := rfl
-- this rw causes lean to generate equations itself for t before the user can register them
theorem t_def' : t = 1 := by rw [t]

/--
error: There already exist stored eqns for 't'; registering new equations
will not have the desired effect.
-/
#guard_msgs(error) in
attribute [eqns t_def] t

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
-- the above should error as the above equation would not have changed the output of the below
example (n : Nat) : t = n := by
  rw [t]
  admit

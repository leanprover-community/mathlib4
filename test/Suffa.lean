import Mathlib.Tactic.Suffa

/--
info: Try this: suffices 1 = 0 by
    rw [Nat.zero_add]
    exact this
-/
#guard_msgs in
example {h : False} : 0 + 1 = 0 := by
  suffa rw [Nat.zero_add]
  simp;
  exact h.elim

/--
info: Try this: suffices False by
    rw [Nat.zero_add]
    simp; exact this
-/
#guard_msgs in
example {h : False} : 0 + 1 = 0 := by
  suffa rw [Nat.zero_add]
        simp;
  exact h.elim

/--
info: Try this: suffices False by
    rw [Nat.zero_add]
    simp
    exact this
-/
#guard_msgs in
example {h : False} : 0 + 1 = 0 := by
  suffa rw [Nat.zero_add]
        simp
  exact h.elim

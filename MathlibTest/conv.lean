import Mathlib.Tactic.Conv

/-- Testing nested `conv in ... => ...` -/
example (a b c : Nat) : a + b + c = c + a + b := by
  conv =>
    conv in a + b =>
      rw [Nat.add_comm]
    guard_target = b + a + c = c + a + b
    rw [Nat.add_comm, Nat.add_assoc]
    conv in (occs := 4) _ + _ =>
      guard_target = a + b
      rw [Nat.add_comm]

/-- Testing nested `conv in ... => ...` -/
example (a b : Nat) : (a + b) + (a + b) = (b + a) + (b + a) := by
  conv =>
    lhs
    conv in (occs := *) a + b =>
      rw [Nat.add_comm]
    guard_target = b + a + (b + a)

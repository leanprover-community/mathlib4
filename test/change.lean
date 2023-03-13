import Mathlib.Tactic.Basic
import Std.Tactic.GuardExpr

example : n + 2 = m := by
  change n + 1 + 1 = _
  guard_target =ₛ n + 1 + 1 = m
  sorry

example (h : n + 2 = m) : False := by
  change _ + 1 = _ at h
  guard_hyp h :ₛ n + 1 + 1 = m
  sorry

example : n + 2 = m := by
  fail_if_success change true
  fail_if_success change _ + 3 = _
  fail_if_success change _ * _ = _
  change (_ : Nat) + _ = _
  sorry

-- `change ... at ...` allows placeholders to mean different things at different hypotheses
example (h : n + 3 = m) (h' : n + 2 = m) : False := by
  change _ + 1 = _ at h h'
  guard_hyp h :ₛ n + 2 + 1 = m
  guard_hyp h' :ₛ n + 1 + 1 = m
  sorry

-- `change ... at ...` preserves dependencies
example (p : n + 2 = m → Type) (h : n + 2 = m) (x : p h) : false := by
  change _ + 1 = _ at h
  guard_hyp x :ₛ p h
  sorry

example : Nat := by
  fail_if_success change Type 1
  sorry

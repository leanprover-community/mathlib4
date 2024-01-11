import Mathlib.Tactic.Change
import Std.Tactic.GuardExpr

set_option pp.unicode.fun true

set_option autoImplicit true
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

def foo (a b c : Nat) := if a < b then c else 0

example : foo 1 2 3 = 3 := by
  change (if _ then _ else _) = _
  change ite _ _ _ = _
  change (if _ < _ then _ else _) = _
  change _ = (if true then 3 else 4)
  rfl

example (h : foo 1 2 3 = 4) : True := by
  change ite _ _ _ = _ at h
  guard_hyp h :ₛ ite (1 < 2) 3 0 = 4
  trivial

example (h : foo 1 2 3 = 4) : True := by
  change (if _ then _ else _) = _ at h
  guard_hyp h : (if 1 < 2 then 3 else 0) = 4
  trivial

example (α : Type) [LT α] (x : α) (h : x < x) : x < id x := by
  change _ < _ -- can defer LT typeclass lookup, just like `show`
  change _ < _ at h -- can defer LT typeclass lookup at h too
  guard_target =ₛ x < id x
  change _ < x
  guard_target =ₛ x < x
  exact h

example (x y : Nat) (h : x = y) : True := by
  change (if 1 < 2 then x else ?_) = y at h
  rotate_left
  · exact 4
  guard_hyp h : (if 1 < 2 then x else 4) = y
  · trivial

example : let x := 22; let y : Nat := x; let z : Fin (y + 1) := 0; z.1 < y + 1 := by
  intro x y z -- `z` was erroneously marked as unused
  change _ at y
  exact z.2
/--
info: Try this: change 0 = 1
---
info: Try this: change (fun x ↦ x) 0 = 1
---
info: Try this: change (fun x ↦ x) 0 = 1
---
error: The term
  1 = 0
is not defeq to the goal:
  (fun x ↦ x) 0 = 1
-/
#guard_msgs in
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- change 0 = 1
  change?        -- change (fun x ↦ x) 0 = 1
  change? _      -- change (fun x ↦ x) 0 = 1
  change? 1 = 0
    -- The term
    --   1 = 0
    -- is not defeq to the goal:
    --   (fun x ↦ x) 0 = 1

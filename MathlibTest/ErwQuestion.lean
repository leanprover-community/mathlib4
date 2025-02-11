import Mathlib.Tactic.ErwQuestion

def f (x : Nat) := x + 1
def a := 37
theorem f_a : f a = 38 := rfl
def b := a

/--
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  f a
⊢ f b = 38
-/
#guard_msgs in
example : f b = 38 := by rw [f_a]

example : f b = 38 := by erw [f_a]

/--
info: b
  and
a
  are defeq at default transparency, but not at reducible transparency.
-/
#guard_msgs in
example : f b = 38 := by erw? [f_a]

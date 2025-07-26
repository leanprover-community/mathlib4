import Mathlib.Tactic.ErwQuestion

def f (x : Nat) := x + 1
def a := 37
theorem f_a : f a = 38 := rfl
def b := a

-- make sure that `erw'` is noisy, so that it gets picked up by CI
/-- info: Debugging `erw?` -/
#guard_msgs in
example : f 37 = 38 := by
  erw? [f]

/--
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  f a
⊢ f b = 38
-/
#guard_msgs in
example : f b = 38 := by rw [f_a]

example : f b = 38 := by erw [f_a]

/--
info: Debugging `erw?`
---
info: ❌️ at reducible transparency,
  b
and
  a
are not defeq, but they are at default transparency.
-/
#guard_msgs in
example : f b = 38 := by erw? [f_a]

set_option tactic.erw?.verbose true in
/--
info: Debugging `erw?`
---
info: ❌️ at reducible transparency,
  b
and
  a
are not defeq, but they are at default transparency.
---
info: Expression appearing in target:
  f b = 38

Expression from `erw`: f a = 38

❌️ at reducible transparency,
  f b = 38
and
  f a = 38
are not defeq.

✅️ at reducible transparency,
  38
and
  38
are defeq.

❌️ at reducible transparency,
  Eq (f b)
and
  Eq (f a)
are not defeq.

❌️ at reducible transparency,
  f b
and
  f a
are not defeq.

❌️ at reducible transparency,
  b
and
  a
are not defeq.
-/
#guard_msgs in
example : f b = 38 := by erw? [f_a]

import Mathlib.Tactic.ErwQuestion

section Single

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
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  f a
in the target expression
  f b = 38

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

end Single

section Sequence

def c := 38
theorem f_c : f c = 39 := rfl

/--
info: Debugging `erw?`
---
info: ❌️ at reducible transparency,
  b
and
  a
are not defeq, but they are at default transparency.
---
info: ❌️ at reducible transparency,
  f 38
and
  f c
are not defeq, but they are at default transparency.
-/
#guard_msgs in
example : f (f b) = 39 := by erw? [f_a, f_c]

end Sequence

section Location

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
example (h : f b = c) : c = 38 := by
  erw? [f_a] at h
  exact h.symm

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
info: Expression appearing in h:
  f b = c

Expression from `erw`: f a = c

❌️ at reducible transparency,
  f b = c
and
  f a = c
are not defeq.

✅️ at reducible transparency,
  c
and
  c
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
example (h : f b = c) : c = 38 := by
  erw? [f_a] at h
  exact h.symm

end Location

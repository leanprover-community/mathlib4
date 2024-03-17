import Mathlib.Tactic.Abel

variable {α : Type _} {a b : α}

example [AddCommMonoid α] : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] : (a + b) - ((b + a) + a) = -a := by abel
example [AddCommGroup α] (x : α) : x - 0 = x := by abel
example [AddCommMonoid α] : (3 : ℕ) • a = a + (2 : ℕ) • a := by abel
example [AddCommGroup α] : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
example [AddCommGroup α] (a b : α) : a-2•b = a -2•b := by abel

example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel1
example [AddCommGroup α] (a b : α) : (a + b) - ((b + a) + a) = -a := by abel1
example [AddCommGroup α] (x : α) : x - 0 = x := by abel1
example [AddCommMonoid α] (a : α) : (3 : ℕ) • a = a + (2 : ℕ) • a := by abel1
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel1
example [AddCommGroup α] (a b : α) : a - 2•b = a - 2•b := by abel1
example [AddCommGroup α] (a : α) : 0 + a = a := by abel1
example [AddCommGroup α] (n : ℕ) (a : α) : n • a = n • a := by abel1
example [AddCommGroup α] (n : ℕ) (a : α) : 0 + n • a = n • a := by abel1


example [AddCommMonoid α] (a b c d e : α) :
  a + (b + (a + (c + (a + (d + (a + e)))))) = e + d + c + b + 4 • a := by abel1
example [AddCommGroup α] (a b c d e : α) :
  a + (b + (a + (c + (a + (d + (a + e)))))) = e + d + c + b + 4 • a := by abel1
example [AddCommGroup α] (a b c d : α) :
  a + b + (c + d - a) = b + c + d := by abel1
example [AddCommGroup α] (a b c : α) :
  a + b + c + (c - a - a) = (-1)•a + b + 2•c := by abel1

-- Make sure we fail on some non-equalities.
example [AddCommMonoid α] (a b c d e : α) :
    a + (b + (a + (c + (a + (d + (a + e)))))) = e + d + c + b + 3 • a ∨ True := by
  fail_if_success
    left; abel1
  right; trivial
example [AddCommGroup α] (a b c d e : α) :
    a + (b + (a + (c + (a + (d + (a + e)))))) = e + d + c + b + 3 • a ∨ True := by
  fail_if_success
    left; abel1
  right; trivial
example [AddCommGroup α] (a b c d : α) :
    a + b + (c + d - a) = b + c - d ∨ True := by
  fail_if_success
    left; abel1
  right; trivial
example [AddCommGroup α] (a b c : α) :
    a + b + c + (c - a - a) = (-1)•a + b + c ∨ True := by
  fail_if_success
    left; abel1
  right; trivial

-- `abel!` should see through terms that are definitionally equal,
def id' (x : α) := x
example [AddCommGroup α] (a b : α) : a + b - b - id' a = 0 := by
  fail_if_success
    abel1
  abel1!

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Interaction.20of.20abel.20with.20casting/near/319895001
example [AddCommGroup α] : True := by
  have : ∀ (p q r s : α), s + p - q = s - r - (q - r - p) := by
    intro p q r s
    abel
  trivial

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Interaction.20of.20abel.20with.20casting/near/319897374
example [AddCommGroup α] (x y z : α) : y = x + z - (x - y + z) := by
  have : True := trivial
  abel

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/abel.20bug.3F/near/368707560
example [AddCommGroup α] (a b s : α) : -b + (s - a) = s - b - a := by abel_nf

/--
error: abel_nf made no progress
-/
#guard_msgs in
example : False := by abel_nf

/--
error: abel_nf made no progress
-/
#guard_msgs in
example [AddCommGroup α] (x y z : α) (w : x = y + z) : False := by
  abel_nf at w

example [AddCommGroup α] (x y z : α) (h : False) (w : x - x = y + z) : False := by
  abel_nf at w
  guard_hyp w : 0 = y + z
  assumption

/--
error: abel_nf made no progress
-/
#guard_msgs in
example [AddCommGroup α] (x y z : α) (_w : x = y + z) : False := by
  abel_nf at *

-- Prior to https://github.com/leanprover/lean4/pull/2917 this would fail
-- (the `at *` would close the goal,
-- and then error when trying to work on the hypotheses because there was no goal.)
example [AddCommGroup α] (x y z : α) (_w : x = y + z) : x - x = 0 := by
  abel_nf at *

/--
error: abel_nf made no progress
-/
-- Ideally this would specify that it made no progress at `w`.
#guard_msgs in
example [AddCommGroup α] (x y z : α) (w : x = y + z) : x - x = 0 := by
  abel_nf at w ⊢

/--
error: abel_nf made no progress
-/
-- Ideally this would specify that it made no progress at `⊢`.
#guard_msgs in
example [AddCommGroup α] (x y z : α) (w : x - x = y + z) : x = 0 := by
  abel_nf at w ⊢

example [AddCommGroup α] (x y z : α) (h : False) (w : x - x = y + z) : False := by
  abel_nf at *
  guard_hyp w : 0 = y + z
  assumption

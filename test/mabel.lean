import Mathlib.Tactic.Mabel

variable {α : Type _} {a b : α}
def id' (x : α) := x

section multiplicative
example [CommMonoid α] : a * (b * a) = a * a * b := by mabel
example [CommGroup α] : (a * b) / ((b * a) * a) = a⁻¹ := by mabel
example [CommGroup α] (x : α) : x / 1 = x := by mabel
example [CommMonoid α] : a^(3 : ℕ) = a * a^(2 : ℕ) := by mabel
example [CommGroup α] : a^(3 : ℤ) = a * a^(2 : ℤ) := by mabel
example [CommGroup α] (a b : α) : a/b^2 = a * b^(-2 : ℤ) := by mabel

example [CommMonoid α] (a b : α) : a * (b * a) = a * a * b := by mabel1
example [CommGroup α] (a b : α) : (a * b) / ((b * a) * a) = a⁻¹ := by mabel1
example [CommGroup α] (x : α) : x / 1 = x := by mabel1
example [CommMonoid α] (a : α) : a^(3 : ℕ) = a * a^(2 : ℕ) := by mabel1
example [CommGroup α] (a : α) : a^(3 : ℤ) = a * a^(2 : ℤ) := by mabel1
example [CommGroup α] (a b : α) : a / b^2 = a / b^2 := by mabel1
example [CommGroup α] (a : α) : 1 * a = a := by mabel1
example [CommGroup α] (n : ℕ) (a : α) : a^n = a^n := by mabel1
example [CommGroup α] (n : ℕ) (a : α) : 1 * a^n = a^n := by mabel1


example [CommMonoid α] (a b c d e : α) :
  a * (b * (a * (c * (a * (d * (a * e)))))) = e * d * c * b * a^4 := by mabel1
example [CommGroup α] (a b c d e : α) :
  a * (b * (a * (c * (a * (d * (a * e)))))) = e * d * c * b * a^4 := by mabel1
example [CommGroup α] (a b c d : α) :
  a * b * (c * d / a) = b * c * d := by mabel1
example [CommGroup α] (a b c : α) :
  a * b * c * (c / a / a) = a^(-1 : ℤ) * b * c^2 := by mabel1

-- Make sure we fail on some non-equalities.
example [CommMonoid α] (a b c d e : α) :
    a * (b * (a * (c * (a * (d * (a * e)))))) = e * d * c * b * a^3 ∨ True := by
  fail_if_success
    left; mabel1
  right; trivial
example [CommGroup α] (a b c d e : α) :
    a * (b * (a * (c * (a * (d * (a * e)))))) = e * d * c * b * a^3 ∨ True := by
  fail_if_success
    left; mabel1
  right; trivial
example [CommGroup α] (a b c d : α) :
    a * b * (c * d / a) = b * c / d ∨ True := by
  fail_if_success
    left; mabel1
  right; trivial
example [CommGroup α] (a b c : α) :
    a * b * c * (c / a / a) = a^(-1 : ℤ) * b * c ∨ True := by
  fail_if_success
    left; mabel1
  right; trivial

-- `mabel!` should see through terms that are definitionally equal,
example [CommGroup α] (a b : α) : a * b / b / id' a = 1 := by
  fail_if_success
    mabel1
  mabel1!

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Interaction.20of.20mabel.20with.20casting/near/319895001
example [CommGroup α] : True := by
  have : ∀ (p q r s : α), s * p / q = s / r / (q / r / p) := by
    intro p q r s
    mabel
  trivial

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Interaction.20of.20mabel.20with.20casting/near/319897374
example [CommGroup α] (x y z : α) : y = x * z / (x / y * z) := by
  have : True := trivial
  mabel

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mabel.20bug.3F/near/368707560
example [CommGroup α] (a b s : α) : b⁻¹ * (s / a) = s / b / a := by mabel_nf

/--
error: to_additive requires an equality goal
-/
#guard_msgs in
example : False := by mabel_nf

/--
error: mabel_nf made no progress
-/
#guard_msgs in
example [CommGroup α] (x y z : α) (w : x = y * z) : False := by
  mabel_nf at w

example [CommGroup α] (x y z : α) (h : False) (w : x / x = y * z) : False := by
  mabel_nf at w
  guard_hyp w : 1 = y * z
  assumption

/--
error: mabel_nf made no progress
-/
#guard_msgs in
example [CommGroup α] (x y z : α) (_w : x = y * z) : False := by
  mabel_nf at *

-- Prior to https://github.com/leanprover/lean4/pull/2917 this would fail
-- (the `at *` would close the goal,
-- and then error when trying to work on the hypotheses because there was no goal.)
example [CommGroup α] (x y z : α) (_w : x = y * z) : x / x = 1 := by
  mabel_nf at *

/--
error: mabel_nf made no progress
-/
-- Ideally this would specify that it made no progress at `w`.
#guard_msgs in
example [CommGroup α] (x y z : α) (w : x = y * z) : x / x = 1 := by
  mabel_nf at w ⊢

/--
error: mabel_nf made no progress
-/
-- Ideally this would specify that it made no progress at `⊢`.
#guard_msgs in
example [CommGroup α] (x y z : α) (w : x / x = y * z) : x = 1 := by
  mabel_nf at w ⊢

example [CommGroup α] (x y z : α) (h : False) (w : x / x = y * z) : False := by
  mabel_nf at *
  guard_hyp w : 1 = y * z
  assumption
end multiplicative

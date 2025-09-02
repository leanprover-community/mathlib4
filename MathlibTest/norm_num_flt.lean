import Mathlib.Tactic.NormNum

-- From https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Proving.20FLT.20with.20norm_num/near/429746342

variable (ignore_me_please : ∀ a b c n : ℕ, a ^ n + b ^ n ≠ c ^ n)

-- previously this proof would work!
/--
error: unsolved goals
n : ℕ
hn : n > 2
a b c : ℕ
⊢ ¬a ^ n + b ^ n = c ^ n
-/
#guard_msgs in
example (n) (hn : n > 2) (a b c : ℕ) : a ^ n + b ^ n ≠ c ^ n := by
  clear ignore_me_please -- I promise not to use this, it would be cheating
  norm_num [*]

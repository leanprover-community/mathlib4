import Mathlib.Tactic.Setm

variable {a b c : Nat}

/- Basic usage -/
example : 1 + 2 = 3 := by
  setm ?A + ?B = (_ : Nat)
  guard_hyp A := 1
  guard_hyp B := 2
  guard_hyp hA : A = 1
  guard_hyp hB : B = 2
  trivial

/- Usage with `using` and `at` keywords -/
example (h1 : 1 + 1 = 3) (h2 : 1 + 3 = 5) (h3 : 2 + 2 = 5) : true := by
  setm ?A + _ = (?B : Nat) using h2 at h1 h2 h3
  guard_hyp A := 1
  guard_hyp B := 5
  guard_hyp h1 : A + A = 3
  guard_hyp h2 : A + 3 = B
  guard_hyp h3 : 2 + 2 = B
  trivial

/- Test reusing named holes -/
example (h : b + a = c) : a + b = c := by
  /- setm 1-/
  setm ?A + ?B = (_ : Nat)
  guard_hyp A := a
  guard_hyp B := b
  /- clean up -/
  unfold_let A B
  clear hA hB A B
  /- setm 2 -/
  rewrite [Nat.add_comm]
  setm ?A + ?B = (_ : Nat) at h ⊢
  guard_hyp A := b
  guard_hyp B := a
  exact h

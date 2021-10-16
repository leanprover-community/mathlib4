import Mathlib.Tactic.Basic

example : ∀ a b : Nat, a = b → b = a := by
  introv h
  exact h.symm

example (n : Nat) : n = n := by
  induction n
  exacts [rfl, rfl]
  exacts []

example (n : Nat) : Nat := by
  guardHyp n : Nat
  let m : Nat := 1
  guardHyp m := 1
  guardHyp m : Nat := 1
  guardTarget Nat
  exact 0

example (a b : Nat) : a ≠ b → ¬ a = b := by
  intros
  byContra H
  contradiction

example (a b : Nat) : ¬¬ a = b → a = b := by
  intros
  byContra H
  contradiction

example (p q : Prop) : ¬¬ p → p := by
  intros
  byContra H
  contradiction


example (n m : Nat) : Unit := by
  cases n
  cases m
  iterate 3 exact ()

example (p q r s : Prop) : p → q → r → s → (p ∧ q) ∧ (r ∧ s ∧ p) ∧ (p ∧ r ∧ q) := by
  intros
  repeat' constructor
  repeat' assumption

example (p q : Prop) : p → q → (p ∧ q) ∧ (p ∧ q ∧ p) := by
  intros
  constructor
  fail_if_success any_goals assumption
  all_goals constructor
  any_goals assumption
  constructor
  any_goals assumption

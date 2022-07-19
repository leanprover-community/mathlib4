import Mathlib.Tactic.SeqFocus

example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  constructor
  mapTacs [trivial, exact ⟨0, rfl⟩, trivial]

/-
-- error: too many tactics
example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  constructor
  mapTacs [trivial, exact ⟨0, rfl⟩, trivial, trivial]
-/

/-
-- error: not enough tactics
example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  constructor
  mapTacs [trivial, exact ⟨0, rfl⟩]
-/

example : ((True ∧ True) ∧ (∃ x : Nat, x = x)) ∧ (True ∧ (∃ x : Nat, x = x)) := by
  constructor
  constructor
  mapTacs [(constructor; trivial), exact ⟨0, rfl⟩, constructor]
  trivial
  trivial
  exact ⟨0, rfl⟩

/-
-- error: not enough tactics
example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  focus
  constructor <;> [trivial]
-/

example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  constructor <;> [trivial, exact ⟨0, rfl⟩]
  trivial

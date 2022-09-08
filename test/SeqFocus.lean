import Mathlib.Tactic.SeqFocus

example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  constructor
  -- error: too many tactics
  fail_if_success map_tacs [trivial, exact ⟨0, rfl⟩, trivial, trivial]
  -- error: not enough tactics
  fail_if_success map_tacs [trivial, exact ⟨0, rfl⟩]
  map_tacs [trivial, exact ⟨0, rfl⟩, trivial]

example : ((True ∧ True) ∧ (∃ x : Nat, x = x)) ∧ (True ∧ (∃ x : Nat, x = x)) := by
  constructor
  constructor
  map_tacs [(constructor; trivial), exact ⟨0, rfl⟩, constructor]
  trivial
  trivial
  exact ⟨0, rfl⟩

example : (True ∧ (∃ x : Nat, x = x)) ∧ True := by
  constructor
  -- error: not enough tactics
  fail_if_success constructor <;> [trivial]
  map_tacs [constructor <;> [trivial, exact ⟨0, rfl⟩], constructor]

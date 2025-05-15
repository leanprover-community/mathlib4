import Mathlib.Data.Finset.Basic

variable {α : Type*} {a : α}

def null (f : Set α → ℕ) (s : Set α) [NeZero (f s)] : ℕ := 0

lemma null_set (f : Set α → ℕ) (s : Set α) (_h : a ∈ s) [NeZero (f s)] : null f s = 0 := rfl
-- set_option trace.Meta.synthInstance true
-- set_option trace.Meta.isDefEq true
-- set_option trace.Elab.step true
-- set_option trace.Elab.app.args true
-- set_option trace.Elab.app.propagateExpectedType true
-- set_option trace.Elab.step.result true
set_option trace.Elab.app true
lemma null_finset (f : Set α → ℕ) (s : Finset α) (h : a ∈ s) [NeZero (f s)] :
    null f s = 0 := by
sorry
--  exact null_set f _ h  -- failed to synthesize NeZero (f (Membership.mem s.val))
-- exact null_set f s h            -- Goals accomplished!
-- exact null_set _ _ (by exact h) -- Goals accomplished!
-- exact @null_set _ _ _ _ h ‹_›   -- Goals accomplished!
-- rfl                             -- Goals accomplished!

import Mathlib.Data.Finset.Basic

variable {α : Type*} {a : α}

def Null (f : Set α → Set α) (s : Set α) [Nonempty (f s)] : ℕ := 0

lemma Null_set (f : Set α → Set α) (s : Set α) (_h : a ∈ s) [Nonempty (f s)] : Null f s = 0 := rfl

lemma Null_finset (f : Set α → Set α) (s : Finset α) (h : a ∈ s) [Nonempty (f s)] :
    Null f s = 0 := by
  exact Null_set f _ h  -- failed to synthesize Nonempty ↑(f (Membership.mem s.val))
-- exact Null_set f s h            -- works
-- exact Null_set f _ (by exact h) -- works
-- rfl                             -- works

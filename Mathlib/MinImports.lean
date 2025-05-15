import Mathlib

theorem associated_abs {α : Type*} [Ring α] [LinearOrder α] (x : α) :
    Associated x |x| := by
  obtain h | h := abs_choice x
  · rw [h]
  · rw [h]
    refine ⟨-1, by simp⟩

#min_imports

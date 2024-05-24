import Mathlib

count_heartbeats in -- Used 3826 heartbeats
example {n : ℕ} : AddLeftStrictMono (Fin (n + 1)) := by
  try infer_instance
  sorry

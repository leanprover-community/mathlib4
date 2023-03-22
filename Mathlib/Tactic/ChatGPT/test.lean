import Mathlib.Tactic.ChatGPT.Frontend

-- example (L M : List α) : (L ++ M).length = (M ++ L).length := by
--   gpt2

-- example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length := by
--   gpt2

-- example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length := by
--   gpt3

-- In the proof you just gave me:
-- ```
-- example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length :=
--   by simp [List.length_append, Nat.add_comm]
-- ```
--  there are some errors:
-- :12:2: error: unsolved goals
-- α : Type ?u.7
-- L M : List α
-- ⊢ List.length L + (List.length L + List.length M) = List.length L + List.length L + List.length M

-- Please fix these, but don't add any more steps to the proof.

example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length :=
  by simp [List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

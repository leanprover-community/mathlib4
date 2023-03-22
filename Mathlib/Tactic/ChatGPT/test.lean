import Mathlib.Tactic.ChatGPT.v2

open List

-- # First we try out `gpt2`.
-- This only makes one call to ChatGPT, but it compiles the output and checks for errors itself.
-- The "feedback" we produce here is what `gpt3` will be sending back to ChatGPT.

-- example (L M : List α) : (L ++ M).length = (M ++ L).length := by
--   gpt2

-- example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length := by
--   gpt2

-- # Now we try out `gpt3`.

example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length := by
  gpt3

-- This produces feedback on the first response, like so:

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

-- after which ChatGPT responds correctly:

-- example (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length :=
--   by simp [List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

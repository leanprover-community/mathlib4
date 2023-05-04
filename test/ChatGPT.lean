import Mathlib.Util.GPT.Chat

open GPT

-- These tests are all disabled as they should not be run in CI.

-- #eval OPENAI_API_KEY
-- #eval send "Hello world" (cfg := { trace := true })
-- #eval send "Please write just the statement of the abc conjecture, in Lean 3 syntax."

-- Check if "GPT-4" has been disabled because you don't have access yet:
-- #eval show IO _  from do return (← unavailableModels.get).toList

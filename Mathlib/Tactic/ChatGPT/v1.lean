import Mathlib.Tactic.ChatGPT.Frontend
import Mathlib.Tactic.ChatGPT.Send

open Lean

namespace Mathlib.Tactic.ChatGPT

def ex1 (code : String) : List Message :=
[ ⟨.system, "You are fixing errors in Lean 4 code. If there is a sorry in the code you should add just one tactic step, and not try to complete the proof."⟩,
  ⟨.user, s!"I'm trying to prove a mathematical statement in the Lean 4 theorem prover. Could you help me with the following code?\n```\n{code.trim}\n```"⟩ ]

-- This is commented out, because it is a live request to ChatGPT.
-- But it works, suggesting things like `def f : Nat := 3`.
-- #eval show MetaM _ from do
--   pure <| (← sendMessages <| ex1 "def f : Nat := by sorry").content.get! |> codeBlocks |>.map CodeBlock.body

-- I thought we could do this, but it apparently makes instance loops.
-- instance [Functor m] : MonadLift (ChatGPTM m) m where
--   monadLift := fun x => StateT.run' x []

elab tk:"gpt" : tactic => do
  let (_, decl) ← getSourceUpTo tk
  let decl' := decl.replace "gpt" "sorry" -- haha this will make for some fun errors
  let r ← sendMessages <| ex1 decl'
  let some response ← pure r.content | throwError "Couldn't understand the response from ChatGPT"
  let [block] ← pure <| codeBlocks response | throwError "I was hoping there'd be a single code block in the response:\n{response}"
  logInfoAt tk response
  logInfoAt tk block.text
  logInfoAt tk block.body

-- example (L M : List α) : (L ++ M).length = (M ++ L).length := by
--   gpt

-- Sample responses:

-- Working:
-- example (L M : List α) : (L ++ M).length = (M ++ L).length :=
-- by rw [List.length_append, List.length_append, Nat.add_comm]

-- Not working:
-- example (L M : List α) : (L ++ M).length = (M ++ L).length := by
--   induction L with
--   | nil => simp [List.append, List.length]
--   | cons x xs IH => simp [List.append, List.length, IH]

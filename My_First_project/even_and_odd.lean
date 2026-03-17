/-
The theory of even and odd Numbers
-/
import Mathlib.Tactic
-- import tactic

def even (n : Nat) : Prop := ∃ d, n = 2 * d
def odd (n : Nat) : Prop := ∃ d, n = 2 * d + 1

/- ## interaction with 0 -/

lemma even_zero : even 0 := ⟨0, rfl⟩
/-
How it works:
even 0 unfolds to ∃ d, 0 = 2 * d. You prove an existential by providing:

the witness: 0 (i.e. d = 0)
the proof: rfl since 0 = 2 * 0 reduces to 0 = 0 which is true by reflexivity

So ⟨0, rfl⟩ means "take d = 0, and the equality holds by computation".
-/

/- ## interaction with succ -/


-- Proof: if n = 2 * d, then n + 1 = 2 * d + 1, which matches the definition of odd
lemma odd_succ_of_even : even n → odd (n + 1) := by
  intro ⟨d, hd⟩    -- assume n is even, i.e. n = 2 * d for some witness d
  exact ⟨d, by omega⟩  -- provide d as witness: n + 1 = 2 * d + 1, proved by omega

-- If n is odd, then n + 1 is even
-- Proof: if n = 2 * d + 1, then n + 1 = 2 * d + 2 = 2 * (d + 1), which matches the definition of even
lemma even_succ_of_odd : odd n → even (n + 1) := by
  intro ⟨d, hd⟩      -- assume n is odd, i.e. n = 2 * d + 1 for some witness d
  exact ⟨d + 1, by omega⟩  -- provide d + 1 as witness: n + 1 = 2 * (d + 1), proved by omega


/-
A note on omega: it's a tactic that automatically solves linear arithmetic goals over
Nat and Int — so once we provide the right witness, omega handles the arithmetic equation
automatically without us having to do it step by step.
-/
/- ## interaction with add -/

example : 123 + 123 = 246 := by norm_num

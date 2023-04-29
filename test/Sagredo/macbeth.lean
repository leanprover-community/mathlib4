import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Tactic.Linarith

open Function

theorem surjective_pow : Function.Surjective (fun p : Nat × Nat => p.fst ^ p.snd) := by
  intro n
  cases Nat.eq_zero_or_pos n with
  | inl h0 =>
    rw [h0]
    use (0, 1)
    rfl
  | inr hpos =>
    use (n, 1)
    simp

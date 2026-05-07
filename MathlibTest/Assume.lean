module

import Mathlib.Tactic.Assume

example {α β γ} {g : β → γ} {f : α → β} (hg : g.Injective) (hf : f.Injective) :
    (g ∘ f).Injective := by
  intro x y
  assume g (f x) = g (f y)
  rename_i h
  guard_hyp h :ₛ g (f x) = g (f y)
  exact hf (hg ‹_›)

example {α β γ} {g : β → γ} {f : α → β} (hg : g.Injective) (hf : f.Injective) :
    (g ∘ f).Injective := by
  intro x y
  assume _
  rename_i h
  guard_hyp h :ₛ (g ∘ f) x = (g ∘ f) y
  exact hf (hg ‹_›)

example (p : Prop) : p → p → p → p → p → p → p := by
  assume p
  assume
    p
  assume p,
    p,
    p, p
  assumption

/-- error: Tactic 'assume' failed: No hypotheses given. -/
#guard_msgs in
example (p : Prop) : p → p := by
  assume

/--
error: Tactic 'assume' failed: Given type
  q
does not match the type
  p
of the hypothesis in the goal.
-/
#guard_msgs in
example (p q : Prop) : p → p := by
  assume q

/--
error: Tactic 'assume' failed: Goal
  p
is not an implication.
-/
#guard_msgs in
example (p q : Prop) : p → p := by
  assume p, p

example (n : Nat) : n < 5 → Fin 5 := by
  assume n < 5
  -- this style is discouraged/disallowed in Mathlib: an explicit name should be given.
  exact ⟨n, ‹_›⟩

/--
error: Tactic 'assume' failed: Given type
  Nat
is not a proposition.
-/
#guard_msgs in
example : ∀ n, n < 5 → Fin 5 := by
  assume Nat

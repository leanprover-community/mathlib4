import Mathlib.Tactic

@[simp]
lemma _root_.exists_eq_right_left {α : Sort*} {p q : α → Prop} {a' : α} :
    (∃ a, p a ∧ a = a' ∧ q a) ↔ p a' ∧ q a' := by aesop
  -- constructor
  -- · rintro ⟨a, hp, rfl, hq⟩
  --   exact ⟨hp, hq⟩
  -- · rintro ⟨hp, hq⟩
  --   use a', hp, rfl, hq

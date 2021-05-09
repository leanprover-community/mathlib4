import Mathlib.Tactic.Basic

open Or in
theorem or_assoc {a b c} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
⟨fun | inl (inl h) => inl h
     | inl (inr h) => inr (inl h)
     | inr h => inr (inr h),
 fun | inl h => inl (inl h)
     | inr (inl h) => inl (inr h)
     | inr (inr h) => inr h⟩

theorem Or.symm : a ∨ b → b ∨ a
| Or.inl h => Or.inr h
| Or.inr h => Or.inl h

theorem Or.imp_right (h : b → c) : a ∨ b → a ∨ c
| Or.inl h => Or.inl h
| Or.inr h' => Or.inr (h h')

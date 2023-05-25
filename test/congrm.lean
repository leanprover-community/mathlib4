import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Congrm

section docs

-- These are the examples from the documentation of the tactic

example {a b c d : ℕ} :
  Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ _) * (_ + _)
/-  Goals left:
⊢ a = b
⊢ d = b
⊢ c + a.pred = c + d.pred
-/
  sorry
  sorry
  sorry

example {a b : ℕ} (h : a = b) : (λ y : ℕ => ∀ z, a + a = z) = (λ x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, _ + a = w
  -- produces one goal for the underscore: ⊢ a = b
  exact h

end docs


-- Testing that the trivial `forall` rule works:
example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm (∀ x, _)
  exact h x

example (f : α → α → Prop) (h : ∀ a b, f a b = True) :
    (∀ a b, f a b) ↔ (∀ _ _ : α, True) := by
  congrm (∀ x y, _)
  exact h x y

-- Testing that the trivial `lambda` rule works:
example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm λ x => _
  rw [h]

-- Testing that the recursion works:
example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm λ (x : ℕ) => x + _
  exact h

-- Testing that trivial application rule works
example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f a = f b := by
  congrm (f _)
  exact h

-- Testing that application rule with two arguments works
example (a b c d : ℕ) (h : a = b) (h' : c = d) (f : ℕ → ℕ → ℕ) : f a c = f b d := by
  congrm (f _ _) <;> assumption

-- Testing that application rule with recursion works
example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f (f a) = f (f b) := by
  congrm (f (f _))
  exact h

-- Testing for implicit arguments in function application
example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (_ = _)
  exact h

-- Testing for correct variable in pattern
example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (a = _)
  exact h

-- Testing for wrong variable in pattern
example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (b = _)
  exact h

example {a b : ℕ} (h : a = b) : (fun _ : ℕ => ∀ z, a + a = z) = (fun _ => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, (_ + a = w)
  exact h

-- Tests that should fail:

/-

-- Testing for too many arguments
example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (Eq _ _ _) -- Todo: good error message
  exact h

-- Testing for wrong pattern
example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm (f _)
  exact h x
-/

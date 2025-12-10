import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.CongrM

private axiom test_sorry : ∀ {α}, α
namespace Tests.Congrm

set_option autoImplicit true

section docs

/-! These are the examples from the tactic documentation -/

example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ ?h1) * (?h2 + ?h3)
  case h1 =>
    guard_target = a = b
    exact test_sorry
  case h2 =>
    guard_target = d = b
    exact test_sorry
  case h3 =>
    guard_target = c + a.pred = c + d.pred
    exact test_sorry

example {a b : ℕ} (h : a = b) : (fun _y : ℕ => ∀ z, a + a = z) = (fun _x => ∀ z, b + a = z) := by
  congrm fun x => ∀ w, ?_ + a = w
  guard_hyp x : ℕ
  guard_hyp w : ℕ
  exact h

end docs

example (f : α → Prop) (h : ∀ a, f a ↔ True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  fail_if_success congrm f ?_
  congrm ∀ x, ?_
  guard_hyp x : α
  exact h x

example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm ∀ x, $(h _)

example (f : α → Prop) (h : ∀ a, f a ↔ True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm ∀ x, $(h _)

example (f : α → α → Prop) (h : ∀ a b, f a b ↔ True) :
    (∀ a b, f a b) ↔ (∀ _ _ : α, True) := by
  congrm ∀ x y, ?_
  exact h x y

example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm fun x => ?_
  guard_target = x + a = x + b
  rw [h]

example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm fun (x : ℕ) => x + ?_
  exact h

example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f a = f b := by
  congrm f ?_
  exact h

example (a b c d : ℕ) (h : a = b) (h' : c = d) (f : ℕ → ℕ → ℕ) : f a c = f b d := by
  congrm f ?_ ?_ <;> assumption

example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f (f a) = f (f b) := by
  congrm f (f ?_)
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm _ = ?_
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  fail_if_success congrm b = ?_
  congrm a = ?_
  exact h

example {b d : ℕ} (h : b = d) : (∀ a, a = b) ↔ (∀ c, c = d) := by
  congrm ∀ a, _ = ?_
  guard_target = b = d
  exact h

example {p q r s : Prop} (pr : p ↔ r) (qs : q ↔ s) : p ∧ q ↔ r ∧ s := by
  congrm ?h1 ∧ ?h2
  case h1 => guard_target = p ↔ r; assumption
  case h2 => guard_target = q ↔ s; assumption

example {f : ℕ → Prop} :
    (∃ k, f (3 + 2 + k) ∨ f (8 + 1 + k)) ↔ ∃ k, f (1 + 4 + k) ∨ f (2 + 7 + k) := by
  congrm (∃ k, f (?_ + k) ∨ f (?_ + k))
  · guard_target =ₛ 3 + 2 = 1 + 4; simp
  · guard_target =ₛ 8 + 1 = 2 + 7; simp

example {a b : ℕ} (h : a = b) : (fun _ : ℕ => ∀ z, a + a = z) = (fun _ => ∀ z, b + a = z) := by
  congrm fun x => ∀ w, ?_ + a = w
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  fail_if_success congrm Eq ?_ ?_ ?_
  congrm _ = ?_
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm _ = $h

example (f : α → Prop) (h : ∀ a, f a ↔ True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  fail_if_success congrm f ?_
  congrm ∀ _, ?_
  exact h _

example (α : Nat → Type) (f : (x : Nat) → α x) (h : i = j) : f i ≍ f j := by
  congrm f ?_
  exact h

def foo (n : Nat) : Nat := 1 + n

@[irreducible] def foo' (n : Nat) : Nat := 1 + n

-- Unfolding
example (n m : Nat) (h : n = m) : foo (2 + n) = foo (2 + m) := by
  congrm 1 + (2 + ?_)
  exact h

-- Fails unfolding irreducible
example (n m : Nat) (h : n = m) : foo' (2 + n) = foo' (2 + m) := by
  fail_if_success congrm 1 + (2 + ?_)
  cases h
  rfl

-- Reflexive relations
example (a b : Nat) (h : a = b) : 1 + a ≤ 1 + b := by
  congrm 1 + ?_
  exact h

-- Subsingleton instances
example [Fintype α] [Fintype β] (h : α = β) : Fintype.card α = Fintype.card β := by
  congrm Fintype.card ?_
  exact h

end Congrm

end Tests

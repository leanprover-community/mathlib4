import Mathlib.Tactic.Cases

example (x : α × β × γ) : True := by
  cases' x with a b; cases' b with b c
  guard_hyp a : α
  guard_hyp b : β
  guard_hyp c : γ
  trivial

example {α β γ : Type u} (x : α × β × γ) : True := by
  cases' h: x with a b
  guard_hyp a : α
  guard_hyp b : β × γ
  guard_hyp x : α × β × γ
  guard_hyp h : x = (a, b)
  trivial

noncomputable def my_rec :
  {motive : ℕ → Sort u_1} →
  (zee : motive 0) →
  (soo : (n : ℕ) → motive n → motive (n + 1)) →
  (t : ℕ) → motive t := @Nat.rec

example (x : ℕ) : True := by
  cases' h: x using my_rec with y
  case zee => guard_hyp h : x = 0; trivial
  case soo => guard_hyp h : x = y + 1; trivial

inductive Foo (α β γ)
| A (a : α)
| B (a' : α) (b' : β)
| C (a'' : α) (b'' : β) (c'' : γ)

example (x : Foo α β γ) : True := by
  cases' x with a₀ a₁ _ a₂ b₂ c₂
  · guard_hyp a₀ : α; trivial
  · guard_hyp a₁ : α; have : β := (by assumption); trivial
  · guard_hyp a₂ : α; guard_hyp b₂ : β; guard_hyp c₂ : γ; trivial

inductive Bar : ℕ → Type
| A (a b : Nat) : Bar 1
| B (c d : Nat) : Bar c

example (x : Bar 0) : True := by
  cases' x with a b c d
  · guard_hyp d : ℕ; trivial

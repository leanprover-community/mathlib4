import Mathlib.Tactic.Prune

universe u
variable {α : Type u} [Add α] [Add α] {e f : α} {a b _d : Nat} {_h : e ≠ f} (h₁ : a = b)
  (h₂ : ff = b) {c : Int}

example : a + 5 = c ∨ True := by
  prune 3
  /- goal state:
  b a: Nat
  h₁: a = b
  c: Int
  ⊢ Int.ofNat a + 5 = c ∨ True
  -/
  exact Or.inr trivial

/-- Lots of duplication of variables, since they are included *again*! -/
example {α : Type u} [Add α] [OfNat α 0] {e f : α} {a b _d : Nat} {_h : e ≠ f} (_h₁ : a = b)
  {_c : Int} : e + f = e ∨ True := by
  /- goal state:
  α✝: Type u
  inst✝³ inst✝²: Add α✝
  e✝ f✝: α✝
  a✝ b✝ _d✝: Nat
  _h✝: e✝ ≠ f✝
  h₁: a✝ = b✝
  c: Int
  α: Type u
  inst✝¹: Add α
  inst✝: OfNat α 0
  e f: α
  a b _d: Nat
  _h: e ≠ f
  _h₁: a = b
  _c: Int
  ⊢ e + f = e ∨ True
  -/
  prune
  /- goal state:
  α: Type u
  inst✝¹: Add α
  inst✝: OfNat α 0
  e f: α
  _h: e ≠ f
  ⊢ e + f = e ∨ True
  -/
  exact Or.inr trivial

example : ∃ n, n = 0 := by
  constructor
  /-
  2 goals
  case h
  a: ℕ
  ⊢ ?w = 0
  case w
  a: ℕ
  ⊢ ℕ
  -/
  prune
  rotate_left
  prune 0
  exact 0
  rfl
  /-
  1 goal
  case h
  a: ℕ
  ⊢ ?w = 0
  -/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.RCases

-- variable {α β γ : Type u}

example (x : α × β × γ) : True := by
  rcases x with ⟨a, b, c⟩
  guard_hyp a : α
  guard_hyp b : β
  guard_hyp c : γ
  trivial

example (x : α × β × γ) : True := by
  rcases x with ⟨a, -, c⟩
  guard_hyp a : α
  fail_if_success have : β := by assumption
  guard_hyp c : γ
  trivial

example (x : (α × β) × γ) : True := by
  fail_if_success rcases x with ⟨a, b, c⟩
  fail_if_success rcases x with ⟨⟨a:β, b⟩, c⟩
  rcases x with ⟨⟨a:α, b⟩, c⟩
  guard_hyp a : α
  guard_hyp b : β
  guard_hyp c : γ
  trivial

example (x y : Nat) (h : x = y) : True := by
  rcases x with _|⟨⟩|z
  · guard_hyp h : Nat.zero = y; trivial
  · guard_hyp h : Nat.succ Nat.zero = y; trivial
  · guard_hyp z : Nat
    guard_hyp h : Nat.succ (Nat.succ z) = y; trivial

example (s : α ⊕ Empty) : True := by
  rcases s with s|⟨⟨⟩⟩
  guard_hyp s : α; trivial

example : True := by
  obtain ⟨n : Nat, h : n = n, -⟩ : ∃ n : Nat, n = n ∧ True
  · exact ⟨0, rfl, trivial⟩
  trivial

example : True := by
  obtain (h : True) | ⟨⟨⟩⟩ : True ∨ False
  · exact Or.inl trivial
  guard_hyp h : True; trivial

example : True := by
  obtain h | ⟨⟨⟩⟩ : True ∨ False := Or.inl trivial
  guard_hyp h : True; trivial

example : True := by
  obtain ⟨h, h2⟩ := And.intro trivial trivial
  guard_hyp h : True; guard_hyp h2 : True; trivial

example : True := by
  fail_if_success obtain ⟨h, h2⟩
  trivial

example (x y : α × β) : True := by
  rcases x, y with ⟨⟨a, b⟩, c, d⟩
  guard_hyp a : α; guard_hyp b : β
  guard_hyp c : α; guard_hyp d : β
  trivial

example (x y : α ⊕ β) : True := by
  rcases x, y with ⟨a|b, c|d⟩
  · guard_hyp a : α; guard_hyp c : α; trivial
  · guard_hyp a : α; guard_hyp d : β; trivial
  · guard_hyp b : β; guard_hyp c : α; trivial
  · guard_hyp b : β; guard_hyp d : β; trivial

example (i j : Nat) : (Σ' x, i ≤ x ∧ x ≤ j) → i ≤ j := by
  intro h
  rcases h' : h with ⟨x, h₀, h₁⟩
  guard_hyp h' : h = ⟨x, h₀, h₁⟩
  apply Nat.le_trans h₀ h₁


example (n : Nat) : True := by
  obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := Nat.lt_or_ge 1 (n + 1)
  {trivial}; trivial

example (n : Nat) : True := by
  obtain one_lt_n | (n_le_one : n + 1 ≤ 1) := Nat.lt_or_ge 1 (n + 1)
  {trivial}; trivial

-- TODO(Mario): clear dependent
example (h : ∃ x : Nat, x = x ∧ 1 = 1) : True := by
  rcases h with ⟨-, _⟩
  -- (do lc ← tactic.local_context, guard lc.empty)
  trivial

example (h : ∃ x : Nat, x = x ∧ 1 = 1) : True := by
  rcases h with ⟨-, _, h⟩
  -- (do lc ← tactic.local_context, guard (lc.length = 1)),
  guard_hyp h : 1 = 1
  trivial

example (h : True ∨ True ∨ True) : True := by
  rcases h with - | - | -
  iterate 3
    -- (do lc ← tactic.local_context, guard lc.empty)
    · trivial

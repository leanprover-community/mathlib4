import Mathlib.Tactic.Cases
import Mathlib.Init.Logic
import Mathlib.Init.Data.Nat.Notation

set_option autoImplicit true
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

inductive Foo (α β)
  | A (a : α)
  | B (a' : α) (b' : β)
  | C (a'' : α) (b'' : β) (c'' : Foo α β)

example (x : Foo α β) : True := by
  cases' x with a₀ a₁ _ a₂ b₂ c₂
  · guard_hyp a₀ : α; trivial
  · guard_hyp a₁ : α; have : β := (by assumption); trivial
  · guard_hyp a₂ : α; guard_hyp b₂ : β; guard_hyp c₂ : Foo α β; trivial

inductive Bar : ℕ → Type
  | A (a b : Nat) : Bar 1
  | B (c d : Nat) : Bar (c + 1) → Bar c

example (x : Bar 0) : True := by
  cases' x with a b c d h
  · guard_hyp d : ℕ; guard_hyp h : Bar (0 + 1); trivial

example (n : Nat) : n = n := by
  induction' n with n ih
  · guard_target =ₛ 0 = 0; rfl
  · guard_hyp n : Nat; guard_hyp ih : n = n
    guard_target =ₛ n + 1 = n + 1; exact congr_arg (· + 1) ih

example (n : Nat) (h : n < 5) : n = n := by
  induction' n with n ih
  · guard_target =ₛ 0 = 0; rfl
  · guard_hyp n : Nat; guard_hyp ih : n < 5 → n = n; guard_hyp h :ₛ n + 1 < 5
    guard_target =ₛ n + 1 = n + 1; rfl

example (n : Nat) {m} (h : m < 5) : n = n := by
  induction' n with n ih
  · guard_target = Nat.zero = Nat.zero; rfl
  · guard_hyp n : Nat; guard_hyp ih : n = n; guard_hyp h : m < 5
    guard_target = Nat.succ n = Nat.succ n; rfl

example (n : Nat) {m} (h : m < 5) : n = n := by
  induction' n with n ih generalizing m
  · guard_target = Nat.zero = Nat.zero; rfl
  · guard_hyp n : Nat; guard_hyp ih : ∀ {m}, m < 5 → n = n; guard_hyp h : m < 5
    guard_target = Nat.succ n = Nat.succ n; rfl

example (n : Nat) : n = n := by
  induction' e : n with m ih
  · guard_hyp e : n = Nat.zero; guard_target = Nat.zero = Nat.zero; rfl
  · guard_hyp m : Nat; guard_hyp ih : n = m → m = m
    guard_hyp e : n = Nat.succ m; guard_target = Nat.succ m = Nat.succ m; rfl

example (n : Nat) : n = n := by
  induction' e : n using my_rec with m ih
  case zee =>
    guard_hyp e : n = 0; guard_target = 0 = 0; rfl
  case soo =>
    guard_hyp m : Nat; guard_hyp ih : n = m → m = m
    guard_hyp e : n = m + 1; guard_target = m + 1 = m + 1; rfl

example (x : Foo α Nat) : True := by
  induction' x with a a' b' a'' b'' c'' ih
  case A => guard_hyp a : α; trivial
  case B => guard_hyp a' : α; guard_hyp b' : Nat; trivial
  case C => guard_hyp a'' : α; guard_hyp b'' : Nat; guard_hyp c'' : Foo α Nat
            guard_hyp ih : True; trivial

example (x : Bar n) : x = x := by
  induction' x with a b c d h ih
  case A => guard_target = Bar.A a b = Bar.A a b; rfl
  case B => guard_hyp h : Bar (c + 1); guard_hyp ih : h = h
            guard_target = Bar.B c d h = Bar.B c d h; rfl

example (p q : Prop) : (p → ¬ q) → ¬ (p ∧ q) := by
  intro hpnq hpq
  apply hpnq
  cases' hpq with hp hq
  assumption
  exact hpq.2

-- Ensure that `induction'` removes generalized variables. Here: `a` and `h`
example (a b : ℕ) (h : a + b = a) : b = 0 := by
  induction' a with d hd
  · -- Test the generalized vars have been removed
    revert h
    fail_if_success (guard_hyp a : Nat)
    fail_if_success (guard_hyp h : a + b = a)
    intro h
    -- Sample proof
    rw [Nat.zero_add] at h
    assumption
  · -- Test the generalized vars have been removed
    revert h
    fail_if_success (guard_hyp a : Nat)
    fail_if_success (guard_hyp h : a + b = a)
    intro h
    -- Sample proof
    rw [Nat.succ_add, Nat.succ.injEq] at h
    apply hd
    assumption

/-- error: unnecessary 'generalizing' argument, variable 'a' is generalized automatically -/
#guard_msgs in
example (n : ℕ) (a : Fin n) : True := by
  induction' n generalizing a

/--
error: variable cannot be generalized because target depends on it
  m
-/
#guard_msgs in
example (m : ℕ) : True := by
  induction' m generalizing m

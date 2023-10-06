import Mathlib.Tactic.ApplyAt
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Std.Tactic.GuardExpr

example {α β : Type*} (f : α → β) (a : α) : β := by
  apply f at a
  guard_hyp a :ₛ β
  exact a

example {α β : Type*} (f : α → β) (a b : α) (h : a = b) : f a = f b := by
  apply congr_arg f at h
  guard_hyp h :ₛ f a = f b
  exact h

example (a b : ℕ) (h : a + 1 = b + 1) : a = b := by
  apply Nat.succ.inj at h
  guard_hyp h :ₛ a = b
  exact h

example {G : Type*} [Group G] (a b c : G) (h : a * c = b * c) : a = b := by
  apply mul_right_cancel at h
  guard_hyp h :ₛ a = b
  exact h

example {G : Type*} [Monoid G] (a b c : G) (h : a * c = b * c)
    (hh : ∀ x y z : G, x * z = y * z → x = y): a = b := by
  apply mul_right_cancel at h
  guard_hyp h :ₛ a = b
  · exact h
  · guard_target = IsRightCancelMul G
    constructor
    intros a b c
    apply hh

example {α β γ δ : Type*} (f : α → β → γ → δ) (a : α) (b : β) (g : γ) : δ := by
  apply f at g
  guard_hyp g :ₛ δ
  assumption'

example {α γ : Type*} {β : α → Type*} {a : α}
    (f : {a : α} → β a → γ) (b : β a) : γ := by
  apply f at b
  guard_hyp b :ₛ γ
  exact b

example {α β γ δ : Type*} (f : {_ : α} → β → {_ : γ} → δ) (g : γ) (a : α) (b : β) :
    δ := by
  apply f at g
  guard_hyp g :ₛ δ
  assumption'

example {α β γ δ : Type*} (f : {_ : α} → {_ : β} → (g : γ) → δ) (g : γ) (a : α) (b : β) :
    δ := by
  apply f at g
  guard_hyp g :ₛ δ
  assumption'

example {α β γ : Type*} (f : α → β) (g : γ) (a : α) : β × γ  := by
  fail_if_success apply f at g
  apply f at a
  guard_hyp a :ₛ β
  exact (a,g)

example {α β : Type*} (a : α) (b : β) : α × β := by
  fail_if_success apply a at b
  exact (a,b)

example {α β : Type*} (a : α) (b : β) : α × β := by
  fail_if_success apply a at b
  exact (a,b)

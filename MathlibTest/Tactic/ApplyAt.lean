import Mathlib.Tactic.ApplyAt
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic

example {α β : Type*} (f : α → β) (a : α) : β := by
  apply f at a
  guard_hyp a :ₛ β
  exact a

/-- `apply at` cannot clear mvarid if still used. -/
example {α : Type} (γ : α → Type) (a : α) (f : α → γ a) : γ a := by
  apply f at a
  rename_i a₂
  guard_hyp a :ₛ γ a₂
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
    intro a b c
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

/--
error: Failed to find γ as the type of a parameter of α → β.
-/
#guard_msgs in
example {α β γ : Type*} (f : α → β) (_g : γ) : β × γ  := by
  apply f at _g

/--
error: Failed: α is not the type of a function.
-/
#guard_msgs in
example {α β : Type*} (a : α) (_b : β) : α × β := by
  apply a at _b

example {α β γ : Type*} (f : α → β) (g : γ) (a : α) : β × γ  := by
  fail_if_success apply f at g
  apply f at a
  guard_hyp a :ₛ β
  exact (a, g)

example {α β : Type*} (a : α) (b : β) : α × β := by
  fail_if_success apply a at b
  exact (a, b)

example {α β : Type*} (a : α) (b : β) : α × β := by
  fail_if_success apply a at b
  exact (a, b)

-- testing field notation
example {A B : Prop} (h : A ↔ B) : A → B := by
  intro hA
  apply h.mp at hA
  assumption

example (a : ℝ) (h3 : a + 1 = 0) : a = -1 := by
  apply (congrArg (fun x => x - 1)) at h3
  simp at h3
  assumption

example (a b : ℝ) (h : -a * b = 0) : a = 0 ∨ b = 0 := by
  apply (congrArg (fun x => x / 1)) at h
  simp at h
  assumption

/-- `apply H at h` when type of `H h` depends on proof of `h` (https://github.com/leanprover-community/mathlib4/issues/20623) -/
example (h : True) : True := by
  have H (h : True) : h = h := rfl
  apply H at h
  simp at h
  exact h

/-- `apply H at h` when type of `H h` depends on proof of `h` (https://github.com/leanprover-community/mathlib4/issues/20623) -/
example (a : List Nat) (k : Nat) (hk : k < a.length) : True := by
  have H (k : Nat) {xs ys : List Nat} (hk: k < xs.length)
    (h : xs = ys) : xs[k] = ys[k]'(h ▸ hk) := h ▸ rfl
  have h : a = a.map id := by simp
  apply H k hk at h
  simp at h
  exact h

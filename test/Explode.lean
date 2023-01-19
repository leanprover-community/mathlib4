import Mathlib.Tactic.Explode.Index

-- #check Mathlib.Explode.Thm

-- OLD, CURRENT
-- 0│   │ p  ├ Prop
-- 1│   │ hP ├ p
-- 2│1,1│ ∀I │ p → p
-- 3│0,2│ ∀I │ ∀ (p : Prop), p → p
theorem theorem_1 : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)

-- OLD, CURRENT
-- 0│       │ p         ├ Prop
-- 1│       │ q         ├ Prop
-- 2│       │ hP        ├ p
-- 3│       │ hQ        ├ q
-- 4│0,1,2,3│ and.intro │ p ∧ q
-- 5│3,4    │ ∀I        │ q → p ∧ q
-- 6│2,5    │ ∀I        │ p → q → p ∧ q
-- 7│1,6    │ ∀I        │ ∀ (q : Prop), p → q → p ∧ q
-- 8│0,7    │ ∀I        │ ∀ (p q : Prop), p → q → p ∧ q
theorem theorem_2 : ∀ (p : Prop) (q : Prop), p → q → p ∧ q :=
  λ p => λ q => λ hP => λ hQ => And.intro hP hQ

-- OLD, CURRENT
-- 0 │       │ a         ├ Prop
-- 1 │       │ h         ├ a
-- 2 │       │ True      │ Prop
-- 3 │       │ hl        │ ┌ a
-- 4 │       │ trivial   │ │ True
-- 5 │3,4    │ ∀I        │ a → True
-- 6 │       │ hr        │ ┌ True
-- 7 │6,1    │ ∀I        │ True → a
-- 8 │0,2,5,7│ Iff.intro │ a ↔ True
-- 9 │1,8    │ ∀I        │ a → (a ↔ True)
-- 10│0,9    │ ∀I        │ ∀ (a : Prop), a → (a ↔ True)
theorem theorem_3 (a : Prop) (h : a) : a ↔ True :=
  Iff.intro
    (λ hl => trivial)
    (λ hr => h)

#explode theorem_3

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Basic

/-!
# Tests for the `choose` tactic
-/

example (h : ∀n m : Nat, n < m → ∃i j, m = n + i ∨ m + j = n) : true :=
by
  choose i j h using h
  guard_hyp i : ∀n m : Nat, n < m → Nat
  guard_hyp j : ∀n m : Nat, n < m → Nat
  guard_hyp h : ∀ (n m : Nat) (h : n < m), m = n + i n m h ∨ m + j n m h = n
  trivial

-- `choose!` eliminates dependencies on props, whenever possible
example (h : ∀n m : Nat, n < m → ∃i j, m = n + i ∨ m + j = n) : true :=
by
  choose! i j h using h
  guard_hyp i : Nat → Nat → Nat
  guard_hyp j : Nat → Nat → Nat
  guard_hyp h : ∀ (n m : Nat), n < m → m = n + i n m ∨ m + j n m = n
  trivial

-- without the `using hyp` syntax, `choose` will intro the hyp first
example : (∀ m : Nat, ∃i, ∀n:Nat, ∃j, m = n + i ∨ m + j = n) → true :=
by
  choose i j h
  guard_hyp i : Nat → Nat
  guard_hyp j : Nat → Nat → Nat
  guard_hyp h : ∀ (m k : Nat), m = k + i m ∨ m + j m k = k
  trivial

-- Test `simp only [exists_prop]` gets applied after choosing.
-- Because of this simp, we need a non-rfl goal
example (h : ∀ n, ∃ k ≥ 0, n = k) : ∀ _ : Nat, 1 = 1 :=
by
  choose u hu using h
  guard_hyp hu : ∀ n, u n ≥ 0 ∧ n = u n
  intro; rfl

-- test choose with conjunction
example (h : ∀ i : Nat, ∃ j, i < j ∧ j < i+i) : true :=
by
  choose f h h' using h
  guard_hyp f : Nat → Nat
  guard_hyp h : ∀ (i : Nat), i < f i
  guard_hyp h' : ∀ (i : Nat), f i < i + i
  trivial

-- test choose with nonempty instances
universe u v

instance Prod.Nonempty (α : Type u) (β : Type v) [hα : Nonempty α] [hβ : Nonempty β] :
  Nonempty (α × β) :=
hα.elim fun a => hβ.elim fun b => ⟨(a, b)⟩

example {α : Type u} (p : α → Prop) (h : ∀ i : α, p i → ∃ j : α × α, p j.1) : true :=
by
  choose! f h using h
  guard_hyp f : α → α × α
  guard_hyp h : ∀ (i : α), p i → p (f i).1
  trivial

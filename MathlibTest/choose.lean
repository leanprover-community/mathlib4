import Batteries.Util.ExtendedBinder
import Mathlib.Tactic.Choose

/-!
# Tests for the `choose` tactic
-/

set_option autoImplicit true

example {α : Type} (h : ∀ n m : α, ∀ (h : n = m), ∃ i j : α, i ≠ j ∧ h = h) : True := by
  choose! i j _x _y using h
  trivial

example (h : ∀ n m : Nat, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : Nat → Nat → Nat
  guard_hyp j : Nat → Nat → Nat
  guard_hyp h : ∀ (n m : Nat), m = n + i n m ∨ m + j n m = n
  trivial

example (h : ∀ i : Nat, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : Nat → Nat
  guard_hyp h : ∀ (i : Nat), i < 7 → i < f i
  guard_hyp h' : ∀ (i : Nat), i < 7 → f i < i + i
  trivial

/- choice -/
example (h : ∀ n m : Nat, n < m → ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ∀ n m : Nat, n < m → Nat
  guard_hyp j : ∀ n m : Nat, n < m → Nat
  guard_hyp h : ∀ (n m : Nat) (h : n < m), m = n + i n m h ∨ m + j n m h = n
  trivial

-- `choose!` eliminates dependencies on props, whenever possible
example (h : ∀ n m : Nat, n < m → ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose! i j h using h
  guard_hyp i : Nat → Nat → Nat
  guard_hyp j : Nat → Nat → Nat
  guard_hyp h : ∀ (n m : Nat), n < m → m = n + i n m ∨ m + j n m = n
  trivial

-- without the `using hyp` syntax, `choose` will intro the hyp first
example : (∀ m : Nat, ∃ i, ∀ n : Nat, ∃ j, m = n + i ∨ m + j = n) → True := by
  choose i j h
  guard_hyp i : Nat → Nat
  guard_hyp j : Nat → Nat → Nat
  guard_hyp h : ∀ (m k : Nat), m = k + i m ∨ m + j m k = k
  trivial

example (h : ∀ _n m : Nat, ∃ i, ∀ n:Nat, ∃ j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : Nat → Nat → Nat
  guard_hyp j : Nat → Nat → Nat → Nat
  guard_hyp h : ∀ (n m k : Nat), m = k + i n m ∨ m + j n m k = k
  trivial

-- Test `simp only [exists_prop]` gets applied after choosing.
-- Because of this simp, we need a non-rfl goal
example (h : ∀ n, ∃ k ≥ 0, n = k) : ∀ _ : Nat, 1 = 1 := by
  choose u hu using h
  guard_hyp hu : ∀ n, u n ≥ 0 ∧ n = u n
  intro; rfl

-- test choose with conjunction
example (h : ∀ i : Nat, ∃ j, i < j ∧ j < i+i) : True := by
  choose f h h' using h
  guard_hyp f : Nat → Nat
  guard_hyp h : ∀ (i : Nat), i < f i
  guard_hyp h' : ∀ (i : Nat), f i < i + i
  trivial

instance : ∀ [Nonempty α], Nonempty (α × α) := @fun ⟨a⟩ => ⟨(a, a)⟩

-- test choose with nonempty instances
instance : ∀ [Nonempty α] [Nonempty β], Nonempty (α × β)
  | ⟨a⟩, ⟨b⟩ => ⟨(a, b)⟩

example {α : Type u} (p : α → Prop) (h : ∀ i : α, p i → ∃ j : α × α, p j.1) : True := by
  choose! f h using h
  guard_hyp f : α → α × α
  guard_hyp h : ∀ (i : α), p i → p (f i).1
  trivial

/-! ## Type annotation tests -/

-- Basic type annotation for witness and property
example (h : ∃ n : Nat, n > 0) : True := by
  choose (n : Nat) (hn : n > 0) using h
  guard_hyp n : Nat
  guard_hyp hn : n > 0
  trivial

-- Type annotation with forall binders
example (h : ∀ m : Nat, ∃ n : Nat, m < n) : True := by
  choose (f : Nat → Nat) (hf : ∀ m, m < f m) using h
  guard_hyp f : Nat → Nat
  guard_hyp hf : ∀ (m : Nat), m < f m
  trivial

-- Mixing annotated and non-annotated arguments
example (h : ∀ m : Nat, ∃ n k : Nat, m < n ∧ n < k) : True := by
  choose f (g : Nat → Nat) hf hg using h
  guard_hyp f : Nat → Nat
  guard_hyp g : Nat → Nat
  guard_hyp hf : ∀ (m : Nat), m < f m
  guard_hyp hg : ∀ (m : Nat), f m < g m
  trivial

-- Type annotation with choose!
example (h : ∀ i : Nat, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! (f : Nat → Nat) (h : ∀ i, i < 7 → i < f i) h' using h
  guard_hyp f : Nat → Nat
  guard_hyp h : ∀ (i : Nat), i < 7 → i < f i
  guard_hyp h' : ∀ (i : Nat), i < 7 → f i < i + i
  trivial

-- Test that user-specified type annotation is preserved (matching `intro` behavior)
example (h : ∃ n : Nat, n > 0) : True := by
  choose (n : Nat) (hn : n > 0 + 0) using h
  guard_hyp n : Nat
  guard_hyp hn : n > 0 + 0  -- user-specified type is preserved
  trivial

-- Type annotation with wildcard
example (h : ∃ n : Nat, n > 0) : True := by
  choose n (hn : n > _) using h
  guard_hyp n : Nat
  guard_hyp hn : n > 0
  trivial

-- Type annotation mismatch should fail (using fail_if_success)
/--
error: type mismatch for 'n'
has type
  Nat
but is expected to have type
  Int
-/
#guard_msgs in
example (h : ∃ n : Nat, n > 0) : True := by
  choose (n : Int) hn using h
  trivial

/--
error: type mismatch for 'hn'
has type
  n > 0
but is expected to have type
  n < 0
-/
#guard_msgs in
example (h : ∃ n : Nat, n > 0) : True := by
  choose n (hn : n < 0) using h
  trivial

-- Binder predicates are not supported
/--
error: binder predicates like '< n' are not supported by choose; use a type annotation like '(h : x < n)' instead
-/
#guard_msgs in
example (h : ∃ n : Nat, n > 0) : True := by
  choose (n > 0) using h
  trivial

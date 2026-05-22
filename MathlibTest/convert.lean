module
import Mathlib.Tactic.Convert
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Image

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true

namespace Tests

example (P : Prop) (h : P) : P := by convert h

example (α β : Type) (h : α = β) (b : β) : α := by
  convert b

example (α β : Type) (h : ∀ α β : Type, α = β) (b : β) : α := by
  convert b
  apply h

example (m n : Nat) (h : m = n) (b : Fin n) : Nat × Nat × Nat × Fin m := by
  convert (37, 57, 2, b)

example (α β : Type) (h : α = β) (b : β) : Nat × α := by
  -- type eq ok since arguments to `Prod` are explicit
  convert (37, b)

example (α β : Type) (h : β = α) (b : β) : Nat × α := by
  convert ← (37, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b) using 2
  guard_target = (Nat × α) = (Nat × β)
  congr!

example {f : β → α} {x y : α} (h : x ≠ y) : f ⁻¹' {x} ∩ f ⁻¹' {y} = ∅ := by
  have : {x} ∩ {y} = (∅ : Set α) := by simpa [ne_comm] using h
  convert Set.preimage_empty
  rw [← Set.preimage_inter, this]

section convert_to

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ using 2
  rw [add_comm]

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ -- defaults to `using 1`
  congr 2
  rw [add_comm]

-- Check that `using 1` gives the same behavior as the default.
example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ using 1
  congr 2
  rw [add_comm]

end convert_to

example (prime : Nat → Prop) (n : Nat) (h : prime (2 * n + 1)) :
    prime (n + n + 1) := by
  convert h
  · guard_target = (HAdd.hAdd : Nat → Nat → Nat) = HMul.hMul
    exact test_sorry
  · guard_target = n = 2
    exact test_sorry

example (prime : Nat → Prop) (n : Nat) (h : prime (2 * n + 1)) :
    prime (n + n + 1) := by
  convert (config := .unfoldSameFun) h
  guard_target = n + n = 2 * n
  exact test_sorry

example (p q : Nat → Prop) (h : ∀ ε > 0, p ε) :
    ∀ ε > 0, q ε := by
  convert! h using 2 with ε hε
  guard_hyp hε : ε > 0
  guard_target = q ε ↔ p ε
  exact test_sorry

class Fintype (α : Type _) where
  card : Nat

axiom Fintype.foo (α : Type _) [Fintype α] : Fintype.card α = 2

axiom Fintype.foo' (α : Type _) [Fintype α] [Fintype (Option α)] : Fintype.card α = 2

axiom instFintypeBool : Fintype Bool

/- Would be "failed to synthesize instance Fintype ?m" without allowing TC failure. -/
example : @Fintype.card Bool instFintypeBool = 2 := by
  convert Fintype.foo _

example : @Fintype.card Bool instFintypeBool = 2 := by
  convert Fintype.foo' _ using 1
  guard_target = Fintype (Option Bool)
  exact test_sorry

example : True := by
  convert_to ?x + ?y = ?z
  case x => exact 1
  case y => exact 2
  case z => exact 3
  all_goals try infer_instance
  · simp
  · simp

-- This test does not work unless we specify that `α` and `β` lie in the same universe.
-- Prior to https://github.com/leanprover/lean4/pull/4493 it did,
-- because previously bodies of `example`s were (confusingly!) allowed to
-- affect the elaboration of the signature!
set_option linter.unusedTactic false in
example {α β : Type u} [Fintype α] [Fintype β] : Fintype.card α = Fintype.card β := by
  congr!
  guard_target = Fintype.card α = Fintype.card β
  congr! +typeEqs
  · guard_target = α = β
    exact test_sorry
  · rename_i inst1 inst2 h
    guard_target = inst1 ≍ inst2
    have : Subsingleton (Fintype α) := test_sorry
    congr!

example (x y z : Nat) (h : x + y = z) : y + x = z := by
  convert_to y + x = _ at h
  · rw [Nat.add_comm]
  exact h

/-! Check that we don't unfold at semireducible transparency: although `congr!` (which
`convert` relies on) applies lemmas at reducible transparency, it used to call
`assumption`/`rfl` at default transparency and solve too much.

`convert!` uses default transparency throughout, and solves the goals all at once.
-/

/-- An identity function at default transparency, to test that we don't unfold too much. -/
def semireducibleId {α : Type*} (a : α) := a

/-
-- These examples can be uncommented when `convert` is reducible by default.
example (P : ℕ → Prop) {a b : ℕ} (h : P a) : P (semireducibleId a) := by
  convert h
  guard_target =ₛ semireducibleId a = a
  rfl

example (P : ℕ → Prop) {a b : ℕ} (h : P a) : P (semireducibleId a) := by
  convert! h

example (P : ℕ → Prop) {a b : ℕ} (hab : b = a) (h : P a) : P (semireducibleId b) := by
  convert h
  guard_target =ₛ semireducibleId b = a
  exact hab

example (P : ℕ → Prop) {a b : ℕ} (hab : b = a) (h : P (semireducibleId a)) : P b := by
  convert! h

example (P : ℕ → Prop) {a b : ℕ} (hab : b = a) (h : P a) : P (semireducibleId b) := by
  convert h
  guard_target =ₛ semireducibleId b = a
  exact hab

example (P : ℕ → Prop) {a b : ℕ} (hab : b = a) (h : P (semireducibleId a)) : P b := by
  convert! h
-/

end Tests

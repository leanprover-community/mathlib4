import Mathlib.Tactic.Recall
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.setOption false
-- Remark: When the test is run by make/CI, this option is not set, so we set it here.
set_option pp.unicode.fun true
set_option autoImplicit true

/-
Motivating examples from the initial Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/recall.20command
-/

section
variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]
variable {E : Type _} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type _} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
recall HasFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' (nhds x ×ˢ pure x)
end

/--
error: value mismatch
  Complex.exp
has value
  id
but is expected to have value
  Complex.wrapped✝.1
-/
#guard_msgs in recall Complex.exp : ℂ → ℂ := id

/--
error: value mismatch
  Real.pi
has value
  0
but is expected to have value
  2 * Classical.choose Real.exists_cos_eq_zero
-/
#guard_msgs in recall Real.pi : ℝ := 0

/-
Other example tests
-/

recall id (x : α) : α := x

/--
info: Try this:
  [apply] recall id {α : Sort u} (a : α) : α
---
error: Type mismatch
  @id
has type
  {α : Sort u_1} → α → α → ℕ
of sort `Type u_1` but is expected to have type
  {α : Sort u} → α → α
of sort `Sort (imax (u + 1) u)`
-/
#guard_msgs in recall id (_x _y : α) : ℕ := 0

recall id (_x : α) : α

def foo := 22

recall foo := 22

recall foo : Nat

/--
error: value mismatch
  foo
has value
  23
but is expected to have value
  22
-/
#guard_msgs in recall foo := 23

recall Nat.add_comm (n m : Nat) : n + m = m + n

-- Caveat: the binder kinds are not checked
recall Nat.add_comm {n m : Nat} : n + m = m + n

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/recall.20command/near/376648750
recall add_assoc {G : Type _} [AddSemigroup G] (a b c : G) : a + b + c = a + (b + c)
recall add_assoc

/-- error: Unknown constant `nonexistent` -/
#guard_msgs in recall nonexistent

axiom bar : Nat
/-- error: constant 'bar' has no defined value -/
#guard_msgs in recall bar := bar

recall List.cons_append (a : α) (as bs : List α) : (a :: as) ++ bs = a :: (as ++ bs) := rfl

/-- Recalling `Nat.add_comm`. -/
recall Nat.add_comm (n m : Nat) : n + m = m + n

-- Test that the unused variable linter does not fire on `recall`.
#guard_msgs in
recall Eq.symm {α : Sort _} {a b : α} (h : a = b) : b = a

-- Test that `recall` works with different universe variable names (issue #37144).
universe u v
class RecallUnivTest (R : Type u) : Prop where
  test : True

set_option linter.unusedVariables false in
recall RecallUnivTest (R : Type v) : Prop

-- Test that `recall` works with `Type*`.
set_option linter.unusedVariables false in
recall RecallUnivTest (R : Type*) : Prop

-- Test that `recall` works inside namespaces (https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/recall.20doesn.27t.20work.20in.20namespaces/near/430877189)
namespace RecallTest
def myDef := 42
end RecallTest

namespace RecallTest
recall myDef : Nat
end RecallTest

-- Test that `recall` works with `open` namespaces.
open RecallTest in
recall myDef : Nat

/-
## `recall?` tests
-/

-- Test recall? with a simple function
/--
info: Try this:
  [apply] recall Nat.add_comm (n m : ℕ) : n + m = m + n
-/
#guard_msgs in recall? Nat.add_comm
-- Verify the suggestion is accepted:
recall Nat.add_comm (n m : ℕ) : n + m = m + n

-- Test recall? with a polymorphic function
/--
info: Try this:
  [apply] recall id {α : Sort u} (a : α) : α
-/
#guard_msgs in recall? id
-- Verify the suggestion is accepted:
recall id {α : Sort u} (a : α) : α

-- Test recall? with unknown constant
/-- error: Unknown constant `nonexistent` -/
#guard_msgs in recall? nonexistent

-- Test recall? with a simple def
/--
info: Try this:
  [apply] recall foo : ℕ
-/
#guard_msgs in recall? foo
-- Verify the suggestion is accepted:
recall foo : ℕ

-- Test recall? with instance implicit arguments
/--
info: Try this:
  [apply] recall add_assoc {G : Type u_1} [AddSemigroup G] (a b c : G) : a + b + c = a + (b + c)
-/
#guard_msgs in recall? add_assoc
-- Verify the suggestion is accepted:
recall add_assoc {G : Type u_1} [AddSemigroup G] (a b c : G) : a + b + c = a + (b + c)

/-
## Type mismatch suggestion tests
-/

-- Test that type mismatch on recall without value gives a suggestion
/--
info: Try this:
  [apply] recall Nat.add_comm (n m : ℕ) : n + m = m + n
---
error: Type mismatch
  Nat.add_comm
has type
  ∀ (n m : ℕ), n + m = m + m
but is expected to have type
  ∀ (n m : ℕ), n + m = m + n
-/
#guard_msgs in recall Nat.add_comm (n m : Nat) : n + m = m + m

import Std.Tactic.GuardMsgs
import Mathlib.Tactic.Recall
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Exponential

-- Remark: When the test is run by make/CI, this option is not set, so we set it here.
set_option pp.unicode.fun true

/-
Motivating examples from the initial Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/recall.20command
-/

section
variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
recall HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : Filter E) :=
  (fun x' => f x' - f x - f' (x' - x)) =o[L] fun x' => x' - x
end

/--
error: value mismatch
  Complex.exp
has value
  id
but is expected to have value
  fun z ↦ CauSeq.lim (Complex.exp' z)
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

recall Function.comp {α} {β} {δ} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

recall id (x : α) : α := x

/--
error: type mismatch
  id
has type
  {α : Sort u_1} → α → α → ℕ : Type u_1
but is expected to have type
  {α : Sort u} → α → α : Sort (imax (u + 1) u)
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

/-- error: unknown constant 'nonexistent' -/
#guard_msgs in recall nonexistent

axiom bar : Nat
/-- error: constant 'bar' has no defined value -/
#guard_msgs in recall bar := bar

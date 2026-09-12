module

public import Mathlib.Tactic.NormNum

/-!
Tests for the `norm_num_simproc` command itself.

The declarations it generates carry their own `public meta` modifiers, so the command works at a
use site that is not inside a `public meta section`. This file deliberately has no such section.
-/

namespace NormNumSimprocTest

open Qq Lean Mathlib.Meta.NormNum

public def wrap (n : ℕ) : ℕ := n

theorem isNat_wrap {x nx : ℕ} (h : IsNat x nx) : IsNat (wrap x) nx := h

/-- A toy `norm_num` extension, to check that the command generates usable declarations. -/
norm_num_simproc [simp, seval] evalWrap (wrap _) where
  eval {_ _} e := do
    let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
    let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
    let ⟨ex, p⟩ ← deriveNat x sℕ
    let pf : Q(IsNat (wrap $x) $ex) := q(isNat_wrap $p)
    return .isNat sℕ ex pf

example : wrap 21 = 21 := by norm_num
example : wrap 21 = 21 := by simp
example : wrap 21 = 21 := by grind

-- the extension still normalises its own operands, so `positivity` and friends keep working
example : 0 < wrap (20 + 1) := by positivity

end NormNumSimprocTest

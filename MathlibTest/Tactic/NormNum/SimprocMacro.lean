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

/-- A test evaluator for `wrap`. -/
norm_num_simproc evalWrap (wrap _) where
  eval {_ _} e := do
    guard ((← Meta.getTransparency) == .instances)
    let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
    let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
    let ⟨ex, p⟩ ← deriveNat x sℕ
    let pf : Q(IsNat (wrap $x) $ex) := q(isNat_wrap $p)
    return .isNat sℕ ex pf

example : wrap 21 = 21 := by norm_num
example : wrap 21 = 21 := by simp
example : wrap 21 = 21 := by simp only [evalWrap]

example : wrap 21 = 21 := by
  fail_if_success simp [-evalWrap]
  -- The default registration does not include `seval`.
  fail_if_success grind
  simp only [evalWrap]

run_cmd do
  let doc ← findDocString? (← getEnv) ``evalWrap
  unless doc.map (·.trimAscii.toString) == some "A test evaluator for `wrap`." do
    throwError "the user doc comment should document the simproc"

-- the extension still normalises its own operands, so `positivity` and friends keep working
example : 0 < wrap (20 + 1) := by positivity

attribute [-simp] evalWrap
attribute [-norm_num] evalWrap.normNumExt

-- An empty list still registers the extension and makes the simproc available by name.
norm_num_simproc [] evalWrapExplicit (wrap _) where
  eval := evalWrap.normNumExt.eval

example : wrap 21 = 21 := by
  fail_if_success simp
  fail_if_success grind
  norm_num

example : wrap 21 = 21 := by simp only [evalWrapExplicit]

attribute [-norm_num] evalWrapExplicit.normNumExt

section

local norm_num_simproc [simp, seval] evalWrapLocal (wrap _) where
  eval := evalWrap.normNumExt.eval

example : wrap 21 = 21 := by norm_num
example : wrap 21 = 21 := by simp
example : wrap 21 = 21 := by grind

end

example : wrap 21 = 21 := by
  fail_if_success (norm_num; done)
  fail_if_success simp
  fail_if_success grind
  simp only [evalWrapLocal]

namespace Scoped

scoped norm_num_simproc [simp, seval] evalWrapScoped (wrap _) where
  eval := evalWrap.normNumExt.eval

example : wrap 21 = 21 := by norm_num
example : wrap 21 = 21 := by simp
example : wrap 21 = 21 := by grind

end Scoped

example : wrap 21 = 21 := by
  fail_if_success (norm_num; done)
  fail_if_success simp
  fail_if_success grind
  simp only [Scoped.evalWrapScoped]

section

open scoped Scoped

example : wrap 21 = 21 := by norm_num
example : wrap 21 = 21 := by simp
example : wrap 21 = 21 := by grind

end

section

-- An explicit list replaces the default `simp` registration.
local norm_num_simproc [seval] evalWrapSeval (wrap _) where
  eval := evalWrap.normNumExt.eval

example : wrap 21 = 21 := by
  fail_if_success simp
  grind

example : wrap 21 = 21 := by norm_num

end

-- Failed extensions must undo assignments, even when `simp` succeeds for another reason.
norm_num_simproc [] evalLeak (wrap _) where
  eval {_ _} e := do
    let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
    discard <| Meta.isDefEq x (mkNatLit 5)
    failure

-- The failing simproc is intentionally not recorded as a used simp argument.
set_option linter.unusedSimpArgs false in
example : ∃ n : ℕ, wrap n + (1 + 1) = 5 := by
  apply Exists.intro
  simp only [evalLeak, Nat.reduceAdd]
  -- If the failed extension assigned the witness to 5, this would be impossible.
  exact (show wrap 3 + 2 = 5 from rfl)

end NormNumSimprocTest

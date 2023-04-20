import Mathlib.Data.Polynomial.Basic

open Polynomial

def p0: ℕ[X] :=
  ⟨⟨{}, Pi.single 0 0, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr p0 = "0" := by native_decide
example : reprStr (Option.some p0) = "some 0" := by native_decide

def p1 : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 37, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr p1 = "C 37 * X" := by native_decide
example : reprStr (Option.some p1) = "some (C 37 * X)" := by native_decide

def p2 : ℕ[X] :=
  ⟨⟨{0, 2}, Pi.single 0 57 + Pi.single 2 22,
    by intro; simp [Pi.single, Function.update_apply]; tauto⟩⟩
example : reprStr p2 = "C 57 + C 22 * X ^ 2" := by native_decide

-- test that parens are added inside `C`
def pu1 : (ULift.{1} ℕ)[X] :=
  ⟨⟨{1}, Pi.single 1 (ULift.up 37),
    by intro; simp [Pi.single, Function.update_apply, ←ULift.down_inj]⟩⟩
example : reprStr pu1 = "C (ULift.up 37) * X" := by native_decide

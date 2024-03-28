import Mathlib.Algebra.Polynomial.Basic

open Polynomial

def p0 : ℕ[X] :=
  ⟨⟨{}, Pi.single 0 0, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr p0 = "0" := by native_decide
example : reprStr (Option.some p0) = "some 0" := by native_decide
example : (reprPrec p0 65).pretty = "0" := by native_decide

def pX : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 1, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr pX = "X" := by native_decide
example : reprStr (Option.some pX) = "some X" := by native_decide

def pXsq : ℕ[X] :=
  ⟨⟨{2}, Pi.single 2 1, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr pXsq = "X ^ 2" := by native_decide
example : reprStr (Option.some pXsq) = "some (X ^ 2)" := by native_decide
example : (reprPrec pXsq 65).pretty = "X ^ 2" := by native_decide
example : (reprPrec pXsq 70).pretty = "X ^ 2" := by native_decide
example : (reprPrec pXsq 80).pretty = "(X ^ 2)" := by native_decide

def p1 : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 37, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr p1 = "C 37 * X" := by native_decide
example : reprStr (Option.some p1) = "some (C 37 * X)" := by native_decide
example : (reprPrec p1 65).pretty = "C 37 * X" := by native_decide
example : (reprPrec p1 70).pretty = "(C 37 * X)" := by native_decide

def p2 : ℕ[X] :=
  ⟨⟨{0, 2}, Pi.single 0 57 + Pi.single 2 22,
    by intro; simp [Pi.single, Function.update_apply]; tauto⟩⟩
example : reprStr p2 = "C 57 + C 22 * X ^ 2" := by native_decide
example : (reprPrec p2 65).pretty = "(C 57 + C 22 * X ^ 2)" := by native_decide

-- test that parens are added inside `C`
def pu1 : (ULift.{1} ℕ)[X] :=
  ⟨⟨{1}, Pi.single 1 (ULift.up 37),
    by intro; simp [Pi.single, Function.update_apply, ←ULift.down_inj]⟩⟩
example : reprStr pu1 = "C (ULift.up 37) * X" := by native_decide

import Mathlib.Algebra.Polynomial.Basic

open Polynomial

def p0 : ℕ[X] :=
  ⟨⟨{}, Pi.single 0 0, by intro; simp [Pi.single, Function.update_apply]⟩⟩
#guard reprStr p0 == "0"
#guard reprStr (Option.some p0) == "some 0"
#guard (reprPrec p0 65).pretty == "0"

def pX : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 1, by intro; simp [Pi.single, Function.update_apply]⟩⟩
#guard reprStr pX == "X"
#guard reprStr (Option.some pX) == "some X"

def pXsq : ℕ[X] :=
  ⟨⟨{2}, Pi.single 2 1, by intro; simp [Pi.single, Function.update_apply]⟩⟩
#guard reprStr pXsq == "X ^ 2"
#guard reprStr (Option.some pXsq) == "some (X ^ 2)"
#guard (reprPrec pXsq 65).pretty == "X ^ 2"
#guard (reprPrec pXsq 70).pretty == "X ^ 2"
#guard (reprPrec pXsq 80).pretty == "(X ^ 2)"

def p1 : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 37, by intro; simp [Pi.single, Function.update_apply]⟩⟩
#guard reprStr p1 == "C 37 * X"
#guard reprStr (Option.some p1) == "some (C 37 * X)"
#guard (reprPrec p1 65).pretty == "C 37 * X"
#guard (reprPrec p1 70).pretty == "(C 37 * X)"

def p2 : ℕ[X] :=
  ⟨⟨{0, 2}, Pi.single 0 57 + Pi.single 2 22,
    by intro; simp [Pi.single, Function.update_apply]; tauto⟩⟩
#guard reprStr p2 == "C 57 + C 22 * X ^ 2"
#guard (reprPrec p2 65).pretty == "(C 57 + C 22 * X ^ 2)"

-- test that parens are added inside `C`
def pu1 : (ULift.{1} ℕ)[X] :=
  ⟨⟨{1}, Pi.single 1 (ULift.up 37),
    by intro; simp [Pi.single, Function.update_apply, ←ULift.down_inj]⟩⟩
#guard reprStr pu1 == "C (ULift.up 37) * X"

/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.ZeroOne
import Qq

#align_import algebra.expr from "leanprover-community/mathlib"@"6b711d2ba5d470c040677ddda0c26b0d72283886"

/-! # Helpers to invoke functions involving algebra at tactic time

This file provides instances on `x y : Q($α)` such that `x + y = q($x + $y)`.

Porting note: This has been rewritten to use `Qq` instead of `Expr`.
-/
open Qq

/-- Produce a `One` instance for `Q($α)` such that `1 : Q($α)` is `q(1 : $α)`. -/
def Expr.instOne {u : Lean.Level} (α : Q(Type u)) (_ : Q(One $α)) : One Q($α) where
  one := q(1 : $α)
#align expr.has_one Expr.instOneₓ

/-- Produce a `Zero` instance for `Q($α)` such that `0 : Q($α)` is `q(0 : $α)`. -/
def Expr.instZero {u : Lean.Level} (α : Q(Type u)) (_ : Q(Zero $α)) : Zero Q($α) where
  zero := q(0 : $α)
#align expr.has_zero Expr.instZeroₓ

/-- Produce a `Mul` instance for `Q($α)` such that `x * y : Q($α)` is `q($x * $y)`. -/
def Expr.instMul {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) where
  mul x y := q($x * $y)
#align expr.has_mul Expr.instMulₓ

/-- Produce an `Add` instance for `Q($α)` such that `x + y : Q($α)` is `q($x + $y)`. -/
def Expr.instAdd {u : Lean.Level} (α : Q(Type u)) (_ : Q(Add $α)) : Add Q($α) where
  add x y := q($x + $y)
#align expr.has_add Expr.instAddₓ

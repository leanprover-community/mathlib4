/-
Copyright (c) 2021 Aurélien Saue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Saue
-/


import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic

open Lean Parser.Tactic Elab Command Elab.Tactic Meta


open Expr in
private def getAppFnAndArgsAux : Expr → Array Expr → Nat → Option (Name × Array Expr)
  | app f a _,   as, i => getAppFnAndArgsAux f (as.set! i a) (i-1)
  | const n _ _, as, i => some (n,as)
  | _,           as, _ => none

def Lean.Expr.getAppFnAndArgs (e : Expr) : Option (Name × Array Expr) :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppFnAndArgsAux e (mkArray nargs dummy) (nargs-1)


def spaces (n : Nat) : String := do
  let mut res := ""
  for i in [:n] do
    res := res ++ " "
  return res

open Expr in
def rip (k : Nat)(e: Expr) : IO Unit := do
  IO.print (spaces k)
  match e with
  | bvar x _        => println! "bvar {x}"
  | fvar x _        => println! "fvar {x}"
  | mvar _ _        => println! "mvar"
  | Expr.sort u _   => println! "sort {u}"
  | const n _ _     => println! "const {n}"
  | app a b _       =>
    println! "app"
    rip (k+2) a
    IO.print (spaces k)
    println! "to"
    rip (k+2) b
  | lam x ty e _    => do
    println! "lam {x}"
    rip (k+2) ty
    rip (k+2) e
  | forallE x ty e d => do
    println! "forallE {x} {d.hash}"
    rip (k+2) ty
    rip (k+2) e
  | letE _ _ _ _ _  => println! "letE"
  | lit _ _         => println! "lit"
  | mdata _ _ _     => println! "mdata"
  | proj _ _ _ _    => println! "proj"


def test {α : Type} [One α ] (x : α) : α :=  x



instance : Numeric Nat := ⟨id⟩
@[simp] theorem x (n : Nat ): Numeric.ofNat n = n := rfl

instance : CommSemiring Nat where
  mul_comm := Nat.mul_comm
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
  ofNat_add := by simp
  ofNat_mul := by simp
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow := Nat.pow
  npow_zero' := sorry
  npow_succ' := sorry
  one := 1
  zero := 0
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := Nat.mul
  nsmul_zero' := sorry
  nsmul_succ' := sorry
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

namespace Tactic
namespace Ring


/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache :=
  α : Expr

abbrev RingM := ReaderT Cache TacticM

def run (e : Expr) {α} (m : RingM α): TacticM α := do
  let ty ← inferType e
  ReaderT.run m ⟨ty⟩

/-- The normal form that `ring` uses is mediated by the function `horner a x n b := a * x ^ n + b`.
The reason we use a definition rather than the (more readable) expression on the right is because
this expression contains a number of typeclass arguments in different positions, while `horner`
contains only one `comm_semiring` instance at the top level. See also `horner_expr` for a
description of normal form. -/
@[reducible] def horner {α} [CommSemiring α] (a x : α) (n : ℕ) (b : α) := a * (x ^ n) + b

inductive HornerExpr : Type
| const (e : Expr) (coeff : ℕ) : HornerExpr
| xadd (e : Expr) (a : HornerExpr) (x : Expr) (n : Expr × ℕ) (b : HornerExpr) : HornerExpr

namespace HornerExpr

def e : HornerExpr → Expr
| (HornerExpr.const e _) => e
| (HornerExpr.xadd e _ _ _ _) => e

instance : Coe HornerExpr Expr := ⟨e⟩

def xadd' (a : HornerExpr) (x : Expr) (n : Expr × ℕ) (b : HornerExpr) : HornerExpr :=
  xadd (mkAppN (mkConst ``horner) #[a, x, n.1, b]) a x n b


def reflConv (e : HornerExpr) : (HornerExpr × Expr) := (e, mkApp (mkConst `Eq.refl) e)


end HornerExpr

open HornerExpr

theorem horner_atom {α} [CommSemiring α] (x : α) : horner 1 x 1 0 = x := by
  simp [horner]
  rw [← npow_eq_pow, npow_succ', npow_zero']
  simp
  done


def evalAtom (e : Expr) : RingM (HornerExpr × Expr) := do
  let one := const (← mkNumeral (← read).α 1) 1
  let zero := const (← mkNumeral (← read).α 0)  0
  return (xadd' one e (one,1) zero, ← mkAppM ``horner_atom #[e])

def eval (e : Expr) : RingM (HornerExpr × Expr) :=
  match e.getAppFnAndArgs with
  | some (`HAdd.hAdd, #[_,_,_,_,a,b]) => throwError "{a}  {b}"
  | _ =>
    match e.natLit? with
    | some n => (const e n).reflConv
    | _ => (evalAtom e)


elab "ring" : tactic => do
  let g ← getMainTarget
  -- (rip 0 g)
  println! (← PrettyPrinter.ppExpr Name.anonymous [] g)
  match g.getAppFnAndArgs with
  | some (`Eq, #[ty, e₁, e₂]) =>
    let ((e₁', p₁), (e₂', p₂)) ← run e₁ $ Prod.mk <$> eval e₁ <*> eval e₂
    if (← isDefEq e₁' e₂') then
      let p ← mkEqTrans p₁ (← mkEqSymm p₂)
      println! (← PrettyPrinter.ppExpr Name.anonymous [] p)
      ensureHasNoMVars p
      assignExprMVar (← getMainGoal) p

      replaceMainGoal []
  | _ => rip 0 g

def b := Eq.trans (Tactic.Ring.horner_atom 1) (Eq.symm (Tactic.Ring.horner_atom 1))
set_option pp.explicit true

example {α} [CommSemiring α] (x y : α) : (1 : α) = (1 : α) := by ring


#check Eq.trans (Tactic.Ring.horner_atom 1) (Eq.symm (Tactic.Ring.horner_atom 1))
#eval horner 1 1 1 0
-- set_option pp.all true

variable {α} [CommSemiring α]
#check (1 : α )
#check horner 1 1 1 0

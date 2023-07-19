/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions

/-!

# `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `natDegree f ≤ d` or `degree f ≤ d`,
tries to solve the goal.
It may leave a side-goal of the form `d' ≤ d`, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with equalities, instead of inequalities (i.e. implement `compute_degree`).
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree` and `natDegree` are equally supported.

##  Implementation details

We start with a goal of the form `natDegree f ≤ d` or `degree f ≤ d`.
Recurse into `f` breaking apart sums, products and powers.  Take care of numerals,
`C a, X (^ n), monomial a n` separately.
-/

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section leaf_lemmas
/-!
###  Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree_le` on (almost) all the leaves of its recursion.
-/
variable {R : Type _}

section semiring
variable [Semiring R]

theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem natDegree_nat_cast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

end semiring

variable [Ring R] in
theorem natDegree_int_cast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

end leaf_lemmas

section Tactic

open Lean

/-- `isDegLE e` checks whether `e` is an `Expr`ession representing an inequality whose LHS is
the `natDegree/degree` of a polynomial with coefficients in a semiring `R`.
If `e` represents
*  `natDegree f ≤ d`, then it returns `(true,  f)`;
*  `degree f ≤ d`,    then it returns `(false, f)`;
*  anything else, then it throws an error.
-/
def isDegLE (e : Expr) : CoreM (Bool × Expr) := do
  match e.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, _rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``degree, #[_R, _iSR, pol])    => return (false, pol)
      | (``natDegree, #[_R, _iSR, pol]) => return (true, pol)
      | (na, _) => throwError (m!"Expected an inequality of the form\n\n" ++
        f!"  'f.natDegree ≤ d'  or  'f.degree ≤ d',\n\ninstead, {na} appears on the LHS")
    |  (na, _)  => throwError m!"Expected an inequality instead of '{na}', '{e}'"

/--
`DegInfo` is a type whose terms encode the part of the syntax tree of a polynomial that currently
plays a role in the computation of its degree.
-/
inductive DegInfo where
  /-- `.rest` is the leaf usually associated to an `fvar`. -/
  | rest     : DegInfo
  /-- `.X` is the leaf associated to `X`. -/
  | X        : DegInfo
  /-- `.natCast` is a leaf associated to a `Nat`. -/
  | natCast  : DegInfo
  /-- `.intCast` is a leaf associated to an `Int`. -/
  | intCast  : DegInfo
  /-- `.ofNat0` is a leaf associated to the literal `0`. -/
  | ofNat0   : DegInfo
  /-- `.ofNat1` is a leaf associated to the literal `1`. -/
  | ofNat1   : DegInfo
  /-- `.ofNatN` is a leaf associated to a "generic" natural number. -/
  | ofNatN   : DegInfo
  /-- `.C` is the leaf associated to `C x`. -/
  | C        : DegInfo
  /-- `.monomial` is the leaf associated to `↑(monomial n) _`. -/
  | monomial : DegInfo
  /-- `.neg pol` is a node associated to `- pol`. -/
  | neg      : DegInfo → DegInfo
  /-- `.add f g` is a node associated to `f + g`. -/
  | add      : DegInfo → DegInfo → DegInfo
  /-- `.sub f g` is a node associated to `f - g`. -/
  | sub      : DegInfo → DegInfo → DegInfo
  /-- `.mul f g` is a node associated to `f * g`. -/
  | mul      : DegInfo → DegInfo → DegInfo
  /-- `.pow f` is a node associated to `f ^ n`. -/
  | pow      : DegInfo → DegInfo
  /-- `.err e` is a leaf for error-management. The `Expr`ession `e` is used to report an error. -/
  | err      : Expr → DegInfo
  deriving BEq, Inhabited, ToExpr

namespace DegInfo

def getArgs : DegInfo → List DegInfo
  | neg f    => [f]
  | add f g  => [f, g]
  | sub f g  => [f, g]
  | mul f g  => [f, g]
  | pow f    => [f]
  | _     => []

def getErr? : DegInfo → Option Expr
  | err e => some e
  | _ => none

def dict : DegInfo → Name × Name
  | rest     => (``le_rfl, ``le_rfl)
  | X        => (``natDegree_X_le,         ``degree_X_le)
  | natCast  => (``natDegree_nat_cast_le,  ``degree_nat_cast_le)
  | intCast  => (``natDegree_int_cast_le,  ``degree_int_cast_le)
  | ofNat0   => (``natDegree_zero_le,      ``degree_zero_le)
  | ofNat1   => (``natDegree_one_le,       ``degree_one_le)
  | ofNatN   => (``natDegree_nat_cast_le,  ``degree_nat_cast_le)
  | C        => (``natDegree_C_le,         ``degree_C_le)
  | monomial => (``natDegree_monomial_le,  ``degree_monomial_le)
  | neg ..   => (``natDegree_neg_le_of_le, ``degree_neg_le_of_le)
  | add ..   => (``natDegree_add_le_of_le, ``degree_add_le_of_le)
  | sub ..   => (``natDegree_sub_le_of_le, ``degree_sub_le_of_le)
  | mul ..   => (``natDegree_mul_le_of_le, ``degree_mul_le_of_le)
  | pow ..   => (``natDegree_pow_le_of_le, ``degree_pow_le_of_le)
  | err ..   => (.anonymous, .anonymous)

def ctorName : DegInfo → String
  | rest     => "rest"
  | X        => "X"
  | natCast  => "natCast"
  | intCast  => "intCast"
  | ofNat0   => "ofNat0"
  | ofNat1   => "ofNat1"
  | ofNatN   => "ofNatN"
  | C        => "C"
  | monomial => "monomial"
  | neg ..   => "neg"
  | add ..   => "add"
  | sub ..   => "sub"
  | mul ..   => "mul"
  | pow ..   => "pow"
  | err ..   => "err"

partial
def toDegInfo (pol : Expr) : DegInfo :=
match pol.numeral? with
  -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
  | some 0 => .ofNat0
  | some 1 => .ofNat1
  | some _ => .ofNatN
  | none => match pol.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, f, g]) => .add (toDegInfo f) (toDegInfo g)
    | (``HSub.hSub, #[_, _, _, _, f, g]) => .sub (toDegInfo f) (toDegInfo g)
    | (``HMul.hMul, #[_, _, _, _, f, g]) => .mul (toDegInfo f) (toDegInfo g)
    | (``HPow.hPow, #[_, _, _, _, f, _]) => .pow (toDegInfo f)
    | (``Neg.neg,   #[_, _, f]) => .neg (toDegInfo f)
    | (``Polynomial.X, _) => .X
    | (``Nat.cast, _) => .natCast
    | (``NatCast.natCast, _) => .natCast
    | (``Int.cast, _) => .intCast
    | (``IntCast.intCast, _) => .intCast
    -- deal with `monomial` and `C`
    | (``FunLike.coe, #[_, _, _, _, polFun, _]) => match polFun.getAppFnArgs with
      | (``Polynomial.monomial, _) => .monomial
      | (``Polynomial.C, _) => .C
      | _ => dbg_trace f!"{polFun.getAppFnArgs}"; .err polFun
    -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
    | _ => .rest

/-
def expand (di : DegInfo) (n : Nat := 0) (indent: String := "") (sep : String := "-|") : String :=
let args := di.getArgs.map (expand · (n + 1) (indent ++ sep))
(if n == 0 then "" else "\n") ++ indent ++ di.ctorName ++ match args with
  | [] => ""
  | [a]
-/

def expand (di : DegInfo) (n : Nat := 0) (indent: String := "") (sep : String := "-|") : String :=
let new := match di with
  | (.add f g)    =>
    let fe := expand f (n + 1) (indent ++ sep)
    let ge := expand g (n + 1) (indent ++ sep)
    fe ++ ge
  | (.sub f g) =>
    let fe := expand f (n + 1) (indent ++ sep)
    let ge := expand g (n + 1) (indent ++ sep)
    fe ++ ge
  | (.mul f g) =>
    let fe := expand f (n + 1) (indent ++ sep)
    let ge := expand g (n + 1) (indent ++ sep)
    fe ++ ge
  | (.pow f) => expand f (n + 1) (indent ++ sep)
  | (.neg f) => expand f (n+1) (indent ++ sep)
  | (.err f) => "or:\n" ++ String.replicate indent.length ' ' ++ s!"{f}"
  | _       => ""
(if n == 0 then "" else "\n") ++ indent ++ di.ctorName ++ new

instance : ToString DegInfo where
  toString := expand

end DegInfo

open DegInfo

/--  `getPolsName pol π` takes as input
*  the `Expr`ession `pol`, assuming that it represents a `Polynomial`;
*  the function `π : Name × Name → Name`, typically `π` equals `Prod.fst` for a goal of type
   `natDegree f ≤ d` or `π` equals `Prod.snd` for a goal of type `degree f ≤ d`.

If `pol` is an `.app`, then it returns the list of arguments of `pol` that also represent
`Polynomial`s, together with the `Name` of the theorem that `cDegCore` applies.

The only exception is when `pol` represents `↑(polFun _) : α → Polynomial _`,
and `polFun` is not `monomial` or `C`.
In this case, the output is data for error-reporting in `cDegCore`.
-/
def getPolsName (pol : DegInfo) (π : Name × Name → Name) : List DegInfo × Name :=
let lexp := match pol with
  | .neg f    => [f]
  | .add f g  => [f, g]
  | .sub f g  => [f, g]
  | .mul f g  => [f, g]
  | .pow f    => [f]
  | _         => []
(lexp, π (dict pol))

/-- `cDegCore (pol, mv) π` takes as input
*  a pair of an `Expr`ession `pol` and an `MVarId` `mv`, where
*  *  `pol` represents a polynomial;
*  *  `mv` represents a goal;
*  a function `π : Name × Name → Name`, typically `π` equals `Prod.fst` for a goal of type
   `natDegree f ≤ d` or `π` equals `Prod.snd` for a goal of type `degree f ≤ d`.

`cDegCore` assumes that `mv` has type `natDegree f ≤ ?_` or `degree f ≤ ?_`.
Note that the RHS of the inequality is a meta-variable: the exact value of `?_` is determined
along the way.
`cDegCore`  recurses into the shape of `pol` to produce a proof of `natDegree f ≤ d` or of
`degree f ≤ d`, where `d` is an appropriately constructed element of `ℕ` or `WithBot ℕ`.

Hopefully, the tactic should not really fail when the inputs are as specified.

The optional `db` flag is for debugging: if `db = true`, then the tactic prints useful information.
-/
partial
def cDegCore (polMV : DegInfo × MVarId) (π : Name × Name → Name) (db : Bool := false) :
    MetaM (List (Expr × MVarId)) := do
let (pol, mv) := polMV
--let polEx := ← (pol.getAppFn :: pol.getAppArgs.toList).mapM Meta.ppExpr
--if db then
--  logInfo (expand pol)
--  if pol.ctorName != "app" then logInfo m!"* pol.ctorName: {pol.ctorName}\n"
--  else logInfo m!"* getAppFnArgs\n{polEx}\n* pol head app\n{pol.getAppFnArgs.1}"
let (pols, na) := getPolsName pol π
--if na.isAnonymous then
--  throwError m!"'compute_degree_le' is undefined for {← Meta.ppExpr pols[0]!.getErr?.get!}"
let once := pols.zip (← mv.applyConst na)
return (← once.mapM fun x => cDegCore x π db).join

/-- Allows the syntax expressions
* `compute_degree_le`,
* `compute_degree_le !`,
* `compute_degree_le -debug`
* `compute_degree_le ! -debug`.
-/
syntax (name := computeDegreeLE) "compute_degree_le" "!"? "-debug"? : tactic

/--  Allows writing `compute_degree_le!` with no space preceding `!`. -/
macro "compute_degree_le!" dbg:"-debug"? : tactic => `(tactic| compute_degree_le ! $[-debug%$dbg]?)

open Elab.Tactic in
/--
`compute_degree_le` is a tactic to solve goals of the form `natDegree f ≤ d` or `degree f ≤ d`.

The tactic first replaces `natDegree f ≤ d` with `d' ≤ d`,
where `d'` is an internally computed guess for which the tactic proves the inequality
`natDegree f ≤ d'`.

Next, it applies `norm_num` to `d'`, in the hope of closing also the `d' ≤ d` goal.

The variant `compute_degree_le!` first applies `compute_degree_le`.
Then it uses `norm_num` on the whole inequality `d' ≤ d` and tries `assumption`.

There is also a "debug-mode", where the tactic prints some information.
This is activated by using `compute_degree_le -debug` or `compute_degree_le! -debug`.
-/
elab_rules : tactic | `(tactic| compute_degree_le $[!%$str]? $[-debug%$debug]?) => focus do
  let (isNatDeg?, lhs) := ← isDegLE (← getMainTarget)
  let π := if isNatDeg? then Prod.fst else Prod.snd
  -- * if the original goal is `natDegree f ≤ d`, then
  --   `le_goals = [⊢ natDegree f ≤ ?_,  ⊢ ?_ ≤ d,  ⊢ ℕ]`
  -- * if the original goal is `degree f ≤ d`, then
  --   `le_goals = [⊢ degree f ≤ ?_,     ⊢ ?_ ≤ d,  ⊢ WithBot ℕ]`
  let le_goals := ← (← getMainGoal).applyConst ``le_trans
  let di := toDegInfo (← instantiateMVars lhs)
  if debug.isSome then logInfo m!"{di}"
  let nfle_pf := ← cDegCore (di, le_goals[0]!) π (db := debug.isSome)
  setGoals [le_goals[1]!]
  if debug.isSome then logInfo m!"Computed proof:\n{nfle_pf}"
  if str.isSome then evalTactic (← `(tactic| norm_num <;> try assumption))
  else evalTactic (← `(tactic| conv_lhs => norm_num))

end Tactic

end Mathlib.Tactic.ComputeDegree

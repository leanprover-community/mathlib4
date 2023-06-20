/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions
import Lean

/-!

# `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `natDegree f ≤ d` or `degree f ≤ d`,
tries to solve the goal.  It may leave side-goals, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with equalities, instead of inequalities (i.e. implement `compute_degree`).
* Add functionality to deal with (some) exponents that are not closed natural numbers.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree` and `natDegree` are equally supported.

##  Implementation details

We start with a goal of the form `natDegree f ≤ d` or `degree f ≤ d`.
Recurse into `f` breaking apart sums, products and powers.  Take care of numerals,
`C a, X (^ n), monomial a n` separately.
-/

section Tactic

namespace Mathlib.Tactic.ComputeDegree

open Lean Meta Elab Tactic Expr Polynomial

/-- Return `max a b` using `Max.max`. This method assumes `a` and `b` have the same type. -/
def mkMax (a b : Expr) : MetaM Expr := mkAppM ``Max.max #[a, b]

/-- Return `a ^ b` using `HPow.hPow`. -/
def mkPow (a b : Expr) : MetaM Expr := mkAppM ``HPow.hPow #[a, b]

/-- `toNatDegree alt pol` takes a function `alt : Expr → MetaM Expr` and `pol : Expr` as inputs.
It assumes that `pol` represents a polynomial and guesses an `Expr` for its `natDegree`.
It errs on the side of assuming that there are no zeros, e.g. `natDegree X = 1`,
regardless of whether the base-ring is `nontrivial` or not.
Everything that is not obtained as an iterated sum, product or `Nat`-power of `C`onstants, `Nat`s,
`X`s, `monomials` gets its guess to the `natDegree` outsourced to the function `alt`.

Chances are that `alt` is the constant function that guesses `mkNatLit 0` for every `Expr`.
-/
partial
def toNatDegree (alt : Expr → MetaM Expr) (pol : Expr) : MetaM Expr :=
match pol.getAppFnArgs with
  --  we assign a `natDegree` to the `Nat`s, the `C`onstants and `X`
  | (``OfNat.ofNat, _) => return mkNatLit 0
  | (``Polynomial.C, _) => return mkNatLit 0
  | (``Polynomial.X, _) => return mkNatLit 1
  --  we assign a `natDegree` to the powers: `natDegree (a ^ b) = b * natDegree a`
  --  with special support for `b ∈ {0, 1}`
  | (``Neg.neg, #[_, _, a]) => do
    toNatDegree alt a
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, a, b]) => do
    mkMul b (← toNatDegree alt a)
  --  we assign a `natDegree` to a `mul`: `natDegree (a * b) = natDegree a + natDegree b`
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
    mkAdd (← toNatDegree alt a) (← toNatDegree alt b)
  --  we assign a `natDegree` to an `add`: `natDegree (a + b) = max (natDegree a) (natDegree b)`
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
    mkMax (← toNatDegree alt a) (← toNatDegree alt b)
  --  we assign a `natDegree` to a `sub`: `natDegree (a - b) = max (natDegree a) (natDegree b)`
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
    mkMax (← toNatDegree alt a) (← toNatDegree alt b)
  --  we assign a `natDegree` to an `↑(monomial n) _`: `natDegree (↑(monomial n) _) = n`
  --  falling back to `alt pol`, if the `FunLike.coe` was not a `monomial`.
  | (``FunLike.coe, #[_, _, _, _, n, _]) =>
    match n.getAppFnArgs with
      | (``monomial, #[_, _, n]) => return n
      | _ => alt pol
  --  everything else falls back to `alt pol`.
  | (_name, _args) => alt pol

/--
`CDL` inspects the goal and checks that it is of the form `natDegree f ≤ d` or `degree f ≤ d`,
failing otherwise.  It uses `Mathlib.Tactic.ComputeDegree.toNatDegree` to guess what the `natDegree`
of `f` is and checks that the guess is less than or equal to `d`, failing otherwise.
Finally, it follows the same pattern as `toNatDegree` to recurse into `f`, applying the relevant
theorems to peel off the computation of the degree, one operation at a time.
-/
partial
def CDL : TacticM Unit := do
  -- if there is no goal left, stop
  let _::_ := ← getGoals | pure ()
  match (← getMainTarget).getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``Polynomial.natDegree, #[_, _, pol]) =>
        -- compute the expected degree, guessing `0` whenever there is a doubt
        let guessDeg := ← toNatDegree (fun _ => return mkNatLit 0) pol
        let gdgNat := ← unsafe evalExpr Nat (.const `Nat []) guessDeg
        let rhsNat := ← unsafe evalExpr Nat (.const `Nat []) rhs
        -- check that the guessed degree really is at most the given degree
        let _ := ← (guard <| gdgNat ≤ rhsNat) <|>
          throwError m!"Should the degree be '{gdgNat}' instead of '{rhsNat}'?"
        let gDstx := ← guessDeg.toSyntax
        -- we begin by replacing the initial inequality with the possibly sharper
        -- `natDegree f ≤ guessDeg`.  This helps, since the shape of `guessDeg` is already
        -- tailored to the expressions that we will find along the way
        evalTactic (← `(tactic| refine le_trans ?_ (by norm_num : $gDstx ≤ _)))
        -- we recurse into the shape of the polynomial, using the appropriate theorems in each case
        match pol.getAppFnArgs with
          | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
            let fStx := ← f.toSyntax
            let gStx := ← g.toSyntax
            evalTactic (← `(tactic| refine (natDegree_add_le $fStx $gStx).trans ?_))
            evalTactic (← `(tactic| refine max_le_max ?_ ?_))
          | (``Neg.neg, #[R, _, f])  =>
            let RStx := ← R.toSyntax
            let fStx := ← f.toSyntax
            evalTactic (← `(tactic| refine (natDegree_neg ($fStx : $RStx)).le.trans ?_))
          | (``HSub.hSub, #[_, _, _, _, f, g])  =>
            let fStx := ← f.toSyntax
            let gStx := ← g.toSyntax
            evalTactic (← `(tactic| refine (natDegree_sub_le $fStx $gStx).trans ?_))
            evalTactic (← `(tactic| refine max_le_max ?_ ?_))
          | (``HMul.hMul, _)  =>
            evalTactic (← `(tactic| refine natDegree_mul_le.trans ?_))
            evalTactic (← `(tactic| refine add_le_add ?_ ?_))
          -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
          | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
            let cStx := ← c.toSyntax
            if polFun.isAppOf ``Polynomial.C then
              evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
            else if polFun.isAppOf ``Polynomial.monomial then
              evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
            else throwError m!"'compute_degree_le' is not implemented for {polFun}"
          | (``Polynomial.X, _)  =>
            evalTactic (← `(tactic| exact natDegree_X_le))
          | (``HPow.hPow, #[_, (.const ``Nat []), _, _, _, _]) => do
            evalTactic (← `(tactic| refine natDegree_pow_le.trans ?_))
            evalTactic (← `(tactic| refine Nat.mul_le_mul rfl.le ?_))
          -- deal with `natDegree (n : Nat)`
          | (``Nat.cast, #[_, _, n]) =>
            let nStx := ← n.toSyntax
            evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
          -- deal with `natDegree 0, 1, (n : Nat)`.
          -- I am not sure why I had to split `n = 0, 1, generic`.
          | (``OfNat.ofNat, #[_, n, _]) =>
            let nStx := ← n.toSyntax
            evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
              evalTactic (← `(tactic| exact natDegree_one.le)) <|>
              evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
          | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"
      -- if the goal is `degree f ≤ d`, then reduce to `natDegree f ≤ d`.
      | (``Polynomial.degree, _) =>
        evalTactic (← `(tactic| refine degree_le_natDegree.trans ?_))
        evalTactic (← `(tactic| refine Nat.cast_le.mpr ?_))
      | _ => throwError "Expected an inequality of the form 'f.natDegree ≤ d' or 'f.degree ≤ d'"
    | _ => throwError "Expected an inequality of the form 'f.natDegree ≤ d' or 'f.degree ≤ d'"
  CDL

/--
`compute_degree_le` attempts to close goals of the form `natDegree f ≤ d` and `degree f ≤ d`.
-/
elab (name := computeDegreeLE) "compute_degree_le" : tactic => focus CDL

end Mathlib.Tactic.ComputeDegree

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyZ.IntegerPolynomial
public import Mathlib.Algebra.Polynomial.Hex.Int

/-!
Elaboration-time interpretation of closed `Polynomial R` expressions as
executable `Hex.ZPoly` values, shared by the `isolate_roots` elaborator
(`HexRealRootsMathlib`) and the `factor_poly`/`irreducibility` `Polynomial ℤ`
extension (`HexBerlekampZassenhausMathlib`).

The interpreter matches the structural heads `X / C / numerals / + / - / * /
neg / ^ (Nat literal)` on the *raw* term (a `whnf` would unfold
`Polynomial.C`/`X`/numerals into their `Finsupp` normal form and defeat the
match) and unfolds named definitions one delta step at a time under a fuel
guard. Every entry point takes the calling tactic's name for error messages.
-/

public section

namespace Mathlib.Tactic.Polynomial.Hex

open Lean Meta

private meta unsafe def evalRatUnsafe (e : Expr) : MetaM (Except String Rat) :=
  try return .ok (← evalExpr Rat (mkConst ``Rat) e)
  catch ex => return .error (← ex.toMessageData.toString)

@[implemented_by evalRatUnsafe]
private meta opaque evalRatCore (e : Expr) : MetaM (Except String Rat)

/-- Evaluate a closed `Rat`-typed (or `ℚ`) expression to a `Rat` at elaboration
time. `Rat` is computable, so `2 ^ (-20)`, `1 / 1000`, `10 ^ (-2)` all reduce. -/
meta def evalRat (tactic : String) (e : Expr) : MetaM Rat := do
  match ← evalRatCore e with
  | .ok q => return q
  | .error msg =>
      throwError "{tactic}: failed to evaluate the rational{indentExpr e}\n{msg}"

/-- Extract a `Nat` literal from an `Expr` (numerals and raw literals). -/
meta def getNat (tactic : String) (e : Expr) : MetaM Nat := do
  match ← getNatValue? e with
  | some n => return n
  | none =>
    match (← whnfR e).getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) =>
      match ← getNatValue? n with
      | some k => return k
      | none => throwError "{tactic}: not a Nat literal{indentExpr e}"
    | _ => throwError "{tactic}: not a Nat literal{indentExpr e}"

/-- Interpret an integer scalar-coefficient leaf (`OfNat`, `Neg`, `+`, `-`, `*`,
`Int.ofNat`, `Nat.cast`, `Int.cast`, raw literals). Throws the dedicated
non-integer-coefficient error on anything else (e.g. a genuine `ℚ`/`ℝ`
non-integer). -/
meta partial def evalIntLit (tactic : String) (e : Expr) : MetaM Int := do
  match (← whnfR e).getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => return Int.ofNat (← getNat tactic n)
  | (``Neg.neg, #[_, _, a]) => return - (← evalIntLit tactic a)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return (← evalIntLit tactic a) * (← evalIntLit tactic b)
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return (← evalIntLit tactic a) + (← evalIntLit tactic b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return (← evalIntLit tactic a) - (← evalIntLit tactic b)
  | (``Int.ofNat, #[n]) => return Int.ofNat (← getNat tactic n)
  | (``Nat.cast, #[_, _, n]) => return Int.ofNat (← getNat tactic n)
  | (``Int.cast, #[_, _, z]) => evalIntLit tactic z
  | _ =>
    match ← getIntValue? e with
    | some z => return z
    | none => throwError "{tactic}: non-integer coefficient{indentExpr e}"

/-- Interpret a coefficient leaf of ring `R`. For `ℚ` (and `ℤ`), a leaf that is
not structurally an integer is evaluated to a `Rat` and accepted only when its
denominator is `1`; otherwise the dedicated non-integer-coefficient error fires.
For `ℝ` (not evaluable to `Rat`), only structurally integer leaves are accepted. -/
meta def evalCoeff (tactic : String) (isRat : Bool) (e : Expr) : MetaM Int := do
  try
    evalIntLit tactic e
  catch _ =>
    if isRat then
      let q ← evalRat tactic e
      if q.den == 1 then return q.num
      else throwError "{tactic}: non-integer coefficient{indentExpr e}"
    else
      throwError "{tactic}: non-integer coefficient{indentExpr e}"

/-- Recursive interpreter from a `Polynomial R` expression over
`X / C / numerals (OfNat) / + / - / * / ^ (Nat) / neg`, with named local defs
unfolded one delta step at a time under a fuel guard, to a `Hex.ZPoly` value.
`isRat` selects the `ℚ`-style non-integer rejection. -/
meta partial def parsePoly (tactic : String) (isRat : Bool) (fuel : Nat)
    (e : Expr) : MetaM Hex.ZPoly := do
  -- Match structural heads on the *raw* term first: `whnf` would unfold
  -- `Polynomial.C`/`X`/numerals into their `Finsupp` normal form and defeat the
  -- match. Only if no structural head applies do we unfold once (a named local
  -- def) under the fuel guard.
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return (← parsePoly tactic isRat fuel a) + (← parsePoly tactic isRat fuel b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return (← parsePoly tactic isRat fuel a) - (← parsePoly tactic isRat fuel b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return (← parsePoly tactic isRat fuel a) * (← parsePoly tactic isRat fuel b)
  | (``Neg.neg, #[_, _, a]) => return - (← parsePoly tactic isRat fuel a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) => do
      let base ← parsePoly tactic isRat fuel a
      let k ← getNat tactic n
      let mut acc : Hex.ZPoly := Hex.DensePoly.C 1
      for _ in [0:k] do acc := acc * base
      return acc
  | (``Polynomial.X, _) => return Hex.DensePoly.ofCoeffs #[(0 : Int), 1]
  | (``Polynomial.C, #[_, _, c]) => return Hex.DensePoly.C (← evalCoeff tactic isRat c)
  | (``OfNat.ofNat, #[_, n, _]) => return Hex.DensePoly.C (Int.ofNat (← getNat tactic n))
  | (``DFunLike.coe, args) =>
    -- `Polynomial.C c` elaborates to `⇑Polynomial.C c = DFunLike.coe … Polynomial.C c`.
    if args.size == 6 && args[4]!.getAppFn.isConstOf ``Polynomial.C then
      return Hex.DensePoly.C (← evalCoeff tactic isRat args[5]!)
    else
      throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"
  | _ =>
    -- Unfold a named def by one delta step under the fuel guard, else fail. Uses
    -- `unfoldDefinition?` rather than `whnf`, which would normalise past the
    -- structural `+/−/*` heads into the `Finsupp` form and defeat the match.
    if fuel == 0 then
      throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"
    else
      match ← unfoldDefinition? e with
      | some e' => parsePoly tactic isRat (fuel - 1) e'
      | none => throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"

end Mathlib.Tactic.Polynomial.Hex

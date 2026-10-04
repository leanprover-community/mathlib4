/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Tactic.Linarith.Datatypes

/-!
# Preparing comparisons for `linarith`

`linarith` searches for a linear combination of comparisons that yields a contradiction.
This module expands their expressions as polynomials and assigns a linear variable to each
distinct monomial. For example, `x * y` becomes a variable in the linear problem; the solver
does not need to reason about multiplication.

The parser recognizes numerals and polynomial operations, treating other subexpressions as
atoms. Atoms are identified up to definitional equality at the configured transparency.
This computation guides the search for a certificate; verification separately proves the
proposed contradiction. In particular, the parser can treat subtraction formally even on `Nat`.
-/

public meta section

open Lean Meta
open Lean.Grind.CommRing (Mon Poly)

namespace Mathlib.Tactic.Linarith

private abbrev ExprMap := List (Lean.Expr × Nat)

private abbrev ParseM := StateRefT ExprMap MetaM

/-- Look up an atomic expression at the configured transparency, allocating an index if needed. -/
private def atom (red : TransparencyMode) (e : Lean.Expr) :
    ParseM Lean.Grind.CommRing.Expr := do
  let atoms ← get
  if let some (_, i) ← atoms.findM? fun (a, _) ↦ withTransparency red (isDefEq e a) then
    return .var i
  let i := atoms.length + 1
  set ((e, i) :: atoms)
  return .var i

/-- Parse numerals, addition, subtraction, multiplication, negation, and powers with literal
natural exponents. Other subexpressions, including division and symbolic powers, become atoms.
Repeated atoms share a variable when they are definitionally equal at transparency `red`. -/
private partial def parseExpr (red : TransparencyMode) (e : Lean.Expr) :
    ParseM Lean.Grind.CommRing.Expr := do
  let e ← whnfR e
  if let some n := e.numeral? then return .num n
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← parseExpr red a) (← parseExpr red b)
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← parseExpr red a) (← parseExpr red b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← parseExpr red a) (← parseExpr red b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← parseExpr red a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    if let some n := n.numeral? then return .pow (← parseExpr red a) n else atom red e
  | _ => atom red e

private def polyEntries : Poly → List (Mon × Int)
  | .num 0 => []
  | .num n => [(.unit, n)]
  | .add n m p => (m, n) :: polyEntries p

/-- Replace monomials with linear variables. Descending indices are required by `Linexp.get`.
The first input from certificate verification is `-1 < 0`, assigning the constant index zero. -/
private def elimMonom (p : Poly) (map : Std.HashMap Mon Nat) :
    Std.HashMap Mon Nat × Linexp := Id.run do
  let mut map := map
  let mut out : Std.TreeMap Nat Int := Std.TreeMap.empty
  for (m, c) in polyEntries p do
    let i := match map[m]? with
      | some i => i
      | none => map.size
    map := map.insert m i
    out := out.insert i c
  return (map, out.toList.reverse)

/-- Compute the linear forms of proofs of comparisons `t R 0`, and the largest variable index.
The oracle uses formal polynomial arithmetic; the certificate verifier establishes soundness. -/
def linearFormsAndMaxVar (red : TransparencyMode) (pfs : List Lean.Expr) :
    MetaM (List Comp × Nat) := do
  (show ParseM (List Comp × Nat) from do
    let mut monoms : Std.HashMap Mon Nat := {}
    let mut comps := []
    for pf in pfs do
      let (iq, e) ← parseCompAndExpr (← inferType pf)
      let p := (← parseExpr red e).toPoly
      let (map, coeffs) := elimMonom p monoms
      monoms := map
      comps := ⟨iq, coeffs⟩ :: comps
    trace[linarith.detail] "monomial map: {repr monoms.toList}"
    return (comps.reverse, monoms.size - 1)).run' []

end Mathlib.Tactic.Linarith

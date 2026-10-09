/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.Hessenberg.Lemmas
public import Mathlib.Tactic.Hessenberg.Similarity
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.Ring.RingNF
public meta import Mathlib.Tactic.Hessenberg.Coeffs
public meta import Mathlib.Tactic.Hessenberg.Similarity
public meta import Mathlib.Tactic.Matrix.Parsing
public meta import Mathlib.Tactic.Ring.RingNF

/-!
# `eval_charpoly`

This module defines the `norm_charpoly` simproc and `eval_charpoly` tactic for normalizing
characteristic polynomials of matrix literals over `ℚ` through a `Matrix.Hessenberg.Similarity`
certificate checked by the kernel.
-/

public meta section

open Lean Meta Elab Qq

initialize registerTraceClass `Tactic.evalCharpoly

namespace Mathlib.Tactic.Hessenberg

/-- Evaluate the characteristic polynomial of the `n × n` matrix literal `A` over `ℚ` with rows
of entries `entries`.

The proof goes through a `Matrix.Hessenberg.Similarity` certificate of `A` and the evaluation by the
kernel of `coeffHessCharPoly` on its Hessenberg matrix, which give `A.charpoly = ofCoeffList cs`.
The result is the normal form of `ofCoeffList cs` under `ring_nf`. -/
def normalizeCharpoly (n : ℕ) (A : Q(Matrix (Fin $n) (Fin $n) ℚ))
    (entries : Array (Array Expr)) : MetaM Simp.Result := do
  let res ← mkHessenbergSimilarity n A entries
  have cert := res.cert
  have Harr := res.Harr
  have hH : Q(($cert).H.toArray = $Harr) := res.toArray_eq
  let cs := coeffHessCharPoly n res.red.H.flatten
  have csE : Q(List ℚ) := ← mkListLit q(ℚ) (← cs.mapM mkRatExpr)
  let hcs ← mkDecideProofQ q(coeffHessCharPoly $n $Harr = $csE)
  let p : Q(Polynomial ℚ) := q(Polynomial.ofCoeffList $csE)
  have pf : Q(Matrix.charpoly $A = $p) := q(charpoly_eq_ofCoeffList_of_eq $cert $hH $hcs)
  let thms ← [``Polynomial.ofCoeffList_cons, ``Polynomial.ofCoeffList_nil, ``map_neg, ``map_ofNat,
    ``map_one, ``map_zero].foldlM (·.addConst ·) ({} : SimpTheorems)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (fold, _) ← Simp.main p ctx (methods := Simp.mkDefaultMethodsCore {})
  -- the normal form of `ring_nf`
  let nf ← AtomM.recurse (← IO.mkRef {}) {} (wellBehavedDischarge := true) RingNF.evalExpr
    (RingNF.cleanup {}) fold.expr
  let r ← Simp.Result.mkEqTrans { expr := p, proof? := pf } fold
  r.mkEqTrans nf

/-- Core of the `norm_charpoly` simproc -/
def normCharpolyCore : Simp.Simproc := fun e => do
  let_expr Matrix.charpoly R _ _ _ _ A := e | return .continue
  let A ← instantiateMVars A
  let some (n, _, _, entries) ← Matrix.matchMatrixLit? A
    | trace[Tactic.evalCharpoly] "{A} is not a closed matrix literal"
      return .continue
  if ← isDefEq R q(ℚ) then
    return .done (← normalizeCharpoly n A entries)
  trace[Tactic.evalCharpoly] "expected the element type to be ℚ"
  return .continue

end Mathlib.Tactic.Hessenberg

/-- The `norm_charpoly` simproc evaluates the characteristic polynomial of matrix literals over `ℚ`.
The result is in the normal form of `ring_nf`. Terms that it cannot evaluate are skipped. -/
simproc_decl norm_charpoly (Matrix.charpoly _) := fun e => do
  try Mathlib.Tactic.Hessenberg.normCharpolyCore e
  catch _ => return .continue

/--
`eval_charpoly` evaluates the characteristic polynomial of matrix literals over `ℚ`.

```lean
example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by
  eval_charpoly
```
-/
elab (name := evalCharpoly) "eval_charpoly" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_charpoly]))
  catch _ =>
    throwError "`eval_charpoly` made no progress.\n\
      Additional information may be available using `set_option trace.Tactic.evalCharpoly true`."
  Tactic.evalTactic (← `(tactic| try ring1))

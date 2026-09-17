/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Hessenberg.CoeffList
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.Ring.RingNF

meta import Mathlib.Tactic.Hessenberg.CoeffList

/-!
# `eval_charpoly`: characteristic polynomials of matrix literals over `ℚ`

This module defines the `norm_charpoly` simproc and the `eval_charpoly` tactic, which evaluate the
characteristic polynomial of a matrix literal over `ℚ` through a `Matrix.Hessenberg.Similarity`
certificate checked by the kernel.
-/

public meta section

open Lean Meta Elab Qq

initialize registerTraceClass `Tactic.evalCharpoly

namespace Mathlib.Tactic.Hessenberg

/-- Rewrite the right-hand side `Polynomial.ofCoeffList cs` of `r`, for a list literal `cs`, to its
`ring_nf` normal form. -/
private def toRingNF (r : Simp.Result) : MetaM Simp.Result := do
  let thms ← [``Polynomial.ofCoeffList_cons, ``Polynomial.ofCoeffList_nil, ``map_neg, ``map_ofNat,
    ``map_one, ``map_zero].foldlM (·.addConst ·) ({} : SimpTheorems)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (fold, _) ← Simp.main r.expr ctx (methods := Simp.mkDefaultMethodsCore {})
  -- the normal form of `ring_nf`
  let nf ← AtomM.recurse (← IO.mkRef {}) {} (wellBehavedDischarge := true) RingNF.evalExpr
    (RingNF.cleanup {}) fold.expr
  (← r.mkEqTrans fold).mkEqTrans nf

/-- Evaluate the characteristic polynomial of the `n × n` matrix literal `A` over `ℚ` with rows
of entries `entries`, to the normal form of `ring_nf`. -/
private def normalizeCharpoly (n : ℕ) (A : Q(Matrix (Fin $n) (Fin $n) ℚ))
    (entries : Array (Array Expr)) : MetaM Simp.Result := do
  let ⟨_, cs, pf⟩ ← charpolyCoeffList n A entries
  toRingNF { expr := q(Polynomial.ofCoeffList $cs), proof? := pf }

/-- Core of the `norm_charpoly` simproc -/
private def normCharpolyCore : Simp.Simproc := fun e => do
  let_expr Matrix.charpoly R _ _ _ _ A := e | return .continue
  let A ← instantiateMVars A
  let some (n, _, _, entries) ← Matrix.matchMatrixLit? A
    | trace[Tactic.evalCharpoly] "not a closed matrix literal{indentExpr A}"
      return .continue
  unless ← isDefEq R q(ℚ) do
    trace[Tactic.evalCharpoly] "expected the element type to be ℚ, found {R}{indentExpr A}"
    return .continue
  return .done (← normalizeCharpoly n A entries)

end Mathlib.Tactic.Hessenberg

/-- The `norm_charpoly` simproc evaluates the characteristic polynomial of matrix literals over `ℚ`.
The result is in the normal form of `ring_nf`. Terms that it cannot evaluate are skipped. -/
simproc_decl norm_charpoly (Matrix.charpoly _) := fun e => do
  try Mathlib.Tactic.Hessenberg.normCharpolyCore e
  catch ex =>
    trace[Tactic.evalCharpoly] "{ex.toMessageData}"
    return .continue

/--
`eval_charpoly` evaluates the characteristic polynomial of matrix literals over `ℚ`.

```lean
example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by
  eval_charpoly
```

The element type must be `ℚ`.
Terms skipped can be viewed by using `set_option trace.Tactic.evalCharpoly true`.
-/
elab (name := evalCharpoly) "eval_charpoly" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_charpoly]))
  catch _ =>
    throwError "`eval_charpoly` made no progress.\n\
      Additional information may be available using `set_option trace.Tactic.evalCharpoly true`."
  Tactic.evalTactic (← `(tactic| try ring1))

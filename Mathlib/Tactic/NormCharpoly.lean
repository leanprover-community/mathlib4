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
# `eval_charpoly`: characteristic polynomials of matrix literals

This module defines the `norm_charpoly` simproc and the `eval_charpoly` tactic, which evaluate the
characteristic polynomial of a matrix literal over a commutative ring that embeds in `ℚ` (such as
`ℚ` itself and `ℤ`) via a `Matrix.Hessenberg.Similarity` certificate checked by the kernel.

## Implementation notes

The Hessenberg reduction algorithm used internally by the tactic divides by pivots, so the
`Matrix.Hessenberg.Similarity` certificate is constructed over `ℚ` and the characteristic polynomial
is pulled back to the coefficient ring `R` along the injective `algebraMap R ℚ`. Restricting to
rings that embed in `ℚ` is a pragmatic choice made to support `ℤ` and `ℚ` first.

## TODO

- Support `ℤ` directly by a fraction-free Hessenberg reduction.
- Support more general coefficient rings (such as `ZMod p`) by registering computational models
  per ring, as the Bareiss tactics do with `bareiss_ext`.
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

/-- Evaluate the characteristic polynomial of the `n × n` matrix literal `A` over the ring `S` with
rows of entries `entries`, to the normal form of `ring_nf`. -/
private def normalizeCharpoly {u : Level} (S : Q(Type u)) (r : CharpolyRing S) (n : ℕ)
    (A : Q(Matrix (Fin $n) (Fin $n) $S)) (entries : Array (Array Expr)) : MetaM Simp.Result := do
  let ⟨cs, pf⟩ ← charpolyCoeffList S r n A entries
  toRingNF { expr := q(Polynomial.ofCoeffList $cs), proof? := pf }

/-- Core of the `norm_charpoly` simproc -/
private def normCharpolyCore : Simp.Simproc := fun e => do
  let_expr Matrix.charpoly R cR _ _ _ A := e | return .continue
  let A ← instantiateMVars A
  let some (n, _, _, entries) ← Matrix.matchMatrixLit? A
    | trace[Tactic.evalCharpoly] "not a closed matrix literal{indentExpr A}"
      return .continue
  let ⟨_u, S⟩ ← getLevelQ' R
  have cS : Q(CommRing $S) := cR
  match ← inferCharpolyRing S cS with
  | .ok r => return .done (← normalizeCharpoly S r n A entries)
  | .error err =>
    trace[Tactic.evalCharpoly] "{err}{indentExpr A}"
    return .continue

end Mathlib.Tactic.Hessenberg

/-- The `norm_charpoly` simproc evaluates the characteristic polynomial of matrix literals over a
commutative ring `α` with `[Algebra α ℚ] [FaithfulSMul α ℚ]`, such as `ℚ` and `ℤ`. The result is in
the normal form of `ring_nf`. Terms that it cannot evaluate are skipped. -/
simproc_decl norm_charpoly (Matrix.charpoly _) := fun e => do
  try Mathlib.Tactic.Hessenberg.normCharpolyCore e
  catch ex =>
    trace[Tactic.evalCharpoly] "{ex.toMessageData}"
    return .continue

/--
`eval_charpoly` evaluates the characteristic polynomial of matrix literals over a commutative ring
`α` with `[Algebra α ℚ] [FaithfulSMul α ℚ]`, such as `ℚ` and `ℤ`.

```lean
example : Matrix.charpoly (R := ℤ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by
  eval_charpoly
```

Terms skipped can be viewed by using `set_option trace.Tactic.evalCharpoly true`.
-/
elab (name := evalCharpoly) "eval_charpoly" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_charpoly]))
  catch _ =>
    throwError "`eval_charpoly` made no progress.\n\
      Additional information may be available using `set_option trace.Tactic.evalCharpoly true`."
  Tactic.evalTactic (← `(tactic| try ring1))

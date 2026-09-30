/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Determinant.Echelon.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Bareiss
public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Tactic.Echelon.Bareiss
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.NormNum.Basic

/-!
# Determinants of matrix literals by echelon decomposition

`proveEchelonDet` evaluates the determinant of a square matrix literal with non-symbolic entries
through the certificate `Echelon.Decomposition A` of its echelon decomposition.

## Implementation notes

The determinant is the quotient of the diagonal products of `U` and `L`, up to the sign of the
row permutation. When the entries are integer numerals the quotient is computed on their values;
it is exact, the rational model's row scales dividing out. The `ℤ√d` model emits structured
literals and does not rescale, so its transform `L` keeps the diagonal of `U` shifted by one row
and the quotient is the last pivot itself.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Echelon Mathlib.Tactic.Matrix

initialize registerTraceClass `Tactic.evalDet

namespace Mathlib.Tactic.Determinant

/-- Rewrite `diagProd k c lit`, for `lit` the list literal of `rows` and `c` their number, to the
product `a₀ * (a₁ * (… * 1))` of the diagonal entries from column `k` on: one equation of
`diagProd` per row, applied by `mkAppM` so that the numerals unify at run time. -/
def proveDiagProd {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (k : ℕ) :
    List (List Q($α)) → MetaM (Q($α) × Expr)
  | [] => return ⟨q(1), ← mkAppM ``diagProd_zero #[mkNatLit k, (q([]) : Q(List (List $α)))]⟩
  | row :: rows => do
    let ⟨e, h⟩ ← proveDiagProd _cr (k + 1) rows
    have a : Q($α) := row.getD k q(0)
    have rowQ : Q(List $α) := mkListLitQ row
    have kQ : Q(ℕ) := mkNatLit k
    let hd := mkExpectedPropHint q(Eq.refl $a) q(List.getD $rowQ $kQ 0 = $a)
    return ⟨q($a * $e), ← mkAppM ``diagProd_succ_cons #[hd, h]⟩

/-- The numeral of a rational: an integer numeral, or `n / d`. -/
def mkRatNumeral {u : Level} (α : Q(Type u)) (v : ℚ) : MetaM Q($α) := do
  let n ← mkIntNumeral α v.num
  if v.den == 1 then return n
  have d : Q($α) := ← mkNumeral α v.den
  let _ ← synthInstanceQ q(Div $α)
  return q($n / $d)

/-- Prove the sign in the ring, `-(-(… 1))`, of a permutation of the shape `mkPerm` builds from
`k` swaps, `(swap a b).trans (… (refl _))`, one lemma per swap. -/
def provePermSign {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) {m : ℕ} :
    (k : ℕ) → (σ : Q(Equiv.Perm (Fin $m))) →
      MetaM ((s : Q($α)) × Q(((Equiv.Perm.sign $σ : ℤ) : $α) = $s))
  | 0, σ => do
    let_expr Equiv.refl _ := σ | throwError "expected the identity permutation in{indentExpr σ}"
    -- `σ` is the matched term, so the lemmas are stated about it by an unchecked retyping
    let h : Expr := q(intCast_sign_refl (n := Fin $m) (α := $α))
    have h : Q(((Equiv.Perm.sign $σ : ℤ) : $α) = 1) := h
    return ⟨q(1), h⟩
  | k + 1, σ => do
    let_expr Equiv.trans _ _ _ sw rest := σ | throwError "expected a swap in{indentExpr σ}"
    let_expr Equiv.swap _ _ a b := sw | throwError "expected a swap in{indentExpr σ}"
    have a : Q(Fin $m) := a
    have b : Q(Fin $m) := b
    have rest : Q(Equiv.Perm (Fin $m)) := rest
    let ⟨s, h⟩ ← provePermSign _cr k rest
    let hab : Q($a ≠ $b) ← mkDecideProofQ q($a ≠ $b)
    let h' : Expr := q(intCast_sign_swap_trans $h $hab)
    have h' : Q(((Equiv.Perm.sign $σ : ℤ) : $α) = -$s) := h'
    return ⟨q(-$s), h'⟩

/-- The value of the determinant read off the decomposition data: `1` for the empty matrix, `0` on
a pivot shortfall, the quotient `s * u / l` of the diagonal products when the entries of `L` and
`U` are integer numerals, and the last pivot with the sign `s` of the swaps otherwise. -/
def detValue {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (m : ℕ)
    (data : BareissData Expr) : MetaM Q($α) := do
  if m == 0 then return q(1)
  if data.pivot.size < m then return q(0)
  have zero : Q($α) := q(0)
  let diag (M : Array (Array Expr)) (k : ℕ) : Q($α) := (M.getD k #[]).getD k zero
  let positive := data.swaps.size % 2 == 0
  let product (M : Array (Array Expr)) : Option ℤ :=
    (List.range m).foldlM (fun acc k => (acc * ·) <$> (diag M k).int?) 1
  match product data.L, product data.U with
  | some l, some u => mkRatNumeral α ((if positive then 1 else -1) * u / l)
  | _, _ =>
    have p : Q($α) := diag data.U (m - 1)
    return if positive then p else q(-$p)

/-- Produce the Bareiss decomposition of the square matrix literal `A` with `entries`, its parsed
entries, and elaborate a proof of `A.det = v` for the value `v` read off the decomposition. -/
def proveEchelonDet {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (_id : Q(IsDomain $α))
    (m : ℕ) (A : Q(Matrix (Fin $m) (Fin $m) $α)) (entries : Array (Array Expr)) :
    MetaM ((v : Q($α)) × Q(($A).det = $v)) := do
  let r ← mkBareissDecomposition _cr A entries
  let certifier? := r.model.entryCertifier?
  -- the decomposition data as the expressions the certificate was built from
  let data ← r.data.mapM r.model.mkEntry
  have c := r.cert
  have cert : Q(Echelon.Decomposition $A) := c.decomp
  -- the diagonal products as `diagProd` on the row lists of `L` and `U`, which the views
  -- rebuild; the certified identity evaluates them. The views' `Zero` instance is scoped to the
  -- inner block, so that the quotations below keep resolving `Zero` through `_cr`.
  let (L, U) ← do
    let zα : Q(Zero $α) ← synthInstanceQ q(Zero $α)
    pure (MatrixViews.ofArray zα m m data.L, MatrixViews.ofArray zα m m data.U)
  have litL : Q(List (List $α)) := L.lit
  have litU : Q(List (List $α)) := U.lit
  have l : Q($α) := q(diagProd 0 $m $litL)
  have uu : Q($α) := q(diagProd 0 $m $litU)
  have hl : Q(∏ i, ofLists $m $m $litL i i = diagProd 0 $m $litL) := q(prod_diag_ofLists $m $litL)
  have hu : Q(∏ i, ofLists $m $m $litU i i = diagProd 0 $m $litU) := q(prod_diag_ofLists $m $litU)
  -- the sign of the certificate's permutation, rebuilt by `mkPerm` from the same swaps
  let σ ← mkPerm m data.swaps
  let ⟨s, hs⟩ ← provePermSign _cr data.swaps.size σ
  -- the identity `l * (s * v) = u` is decided, the kernel evaluating the products, or proved by
  -- the entry certifier on the products unfolded to the entries
  let certifyIdentity : (v : Q($α)) → MetaM Q($l * ($s * $v) = $uu) ← match certifier? with
    | none => pure fun v => mkDecideProofQ q($l * ($s * $v) = $uu)
    | some certifier => do
      let (eL, hL) ← proveDiagProd _cr 0 L.entries
      let (eU, hU) ← proveDiagProd _cr 0 U.entries
      have hL : Q($l = $eL) := hL
      have hU : Q($uu = $eU) := hU
      pure fun v => do
        let hv : Q($eL * ($s * $v) = $eU) ← certifier q($eL * ($s * $v) = $eU)
        return q((congrArg (· * ($s * $v)) $hL).trans (Eq.trans $hv (Eq.symm $hU)))
  -- the value, verified by the identity
  let v ← detValue _cr m data
  let hv ← certifyIdentity v
  -- the projections of `cert` reduce to the matrices the certificate built from `data`, which the
  -- views rebuilt, so the hypotheses transport by defeq
  have Um : Q(Matrix (Fin $m) (Fin $m) $α) := c.U
  have hU' : Q(($cert).L * ($A).submatrix ($cert).σ id = $Um) := c.mul_eq
  have hl' : Q(∏ i, ($cert).L i i = $l) := hl
  have hu' : Q(∏ i, $Um i i = $uu) := hu
  have hs' : Q(((Equiv.Perm.sign ($cert).σ : ℤ) : $α) = $s) := hs
  return ⟨v, q(Echelon.Decomposition.det_eq $cert $hU' $hl' $hu' $hs' $hv)⟩

/-- The `norm_det` branch for square matrix literals with non-symbolic entries over a domain the
echelon method handles: `none` where it does not apply or fails, leaving the term to the
fallback method. -/
def normDetEchelon? (e : Expr) : SimpM (Option Simp.Result) := do
  let_expr Matrix.det _ _ _ _ _ A := e | return none
  let A ← instantiateMVars A
  let some (m, _, R, entries) ← matchMatrixLit? A
    | trace[Tactic.evalDet] "not a closed matrix literal{indentExpr A}"
      return none
  let u ← getDecLevel R
  have α : Q(Type u) := R
  match ← inferBareissRing α with
  | .error err =>
    trace[Tactic.evalDet] "{err}{indentExpr A}"
    return none
  | .ok _cr =>
    have _id : Q(IsDomain $α) := ← synthInstanceQ q(IsDomain $α)
    have A : Q(Matrix (Fin $m) (Fin $m) $α) := A
    try
      let ⟨v, pf⟩ ← proveEchelonDet _cr _id m A entries
      -- normalise the value where `norm_num` evaluates it
      let ctx ← readThe Simp.Context
      let r : Simp.Result := { expr := v, proof? := some pf }
      let s ← try Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := false) (e := v)
        catch _ => pure { expr := v }
      return some (← r.mkEqTrans s)
    catch ex =>
      trace[Tactic.evalDet] "{ex.toMessageData}"
      return none

end Mathlib.Tactic.Determinant

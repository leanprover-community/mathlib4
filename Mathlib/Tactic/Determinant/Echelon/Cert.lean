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
row permutation. On the integer carrier the quotient is computed on the values, where it is exact
since the rational model's row scales divide out. The `ℤ√d` model computes on expressions and does
not rescale, so its transform `L` keeps the diagonal of `U` shifted by one row and the quotient is
the last pivot itself.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Echelon Mathlib.Tactic.Matrix

initialize registerTraceClass `Tactic.evalDet

namespace Mathlib.Tactic.Determinant

/-- The proof of `diagProd k c rows = a₀ * (a₁ * (… * 1))` on the literal `rows`, the product of
the diagonal entries from column `k` on, one `diagProd_succ_cons` per row. -/
def proveDiagProd {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (k c : Nat) (kQ cQ : Q(Nat))
    (rows : Q(List (List $α))) : MetaM ((e : Q($α)) × Q(diagProd $kQ $cQ $rows = $e)) :=
  match c with
  | 0 => do
    have : $cQ =Q 0 := ⟨⟩
    return ⟨q(1), q(diagProd_zero $kQ $rows)⟩
  | c + 1 => do
    let_expr List.cons _ row rowsTl := rows |
      throwError "proveDiagProd: {rows} is not a cons cell"
    have row : Q(List $α) := row
    have rowsTl : Q(List (List $α)) := rowsTl
    let_expr List.cons _ a suffix := dropListLitQ k row |
      throwError "proveDiagProd: {row} has no entry at {k}"
    have a : Q($α) := a
    have suffix : Q(List $α) := suffix
    have k₁Q : Q(Nat) := mkNatLitQ (k + 1)
    have c₁Q : Q(Nat) := mkNatLitQ c
    let ⟨e, h⟩ ← proveDiagProd rα (k + 1) c k₁Q c₁Q rowsTl
    have hd : List.drop $kQ $row =Q $a :: $suffix := ⟨⟩
    have : $rows =Q $row :: $rowsTl := ⟨⟩
    have : $cQ =Q $c₁Q + 1 := ⟨⟩
    have : $k₁Q =Q $kQ + 1 := ⟨⟩
    return ⟨q($a * $e), q(diagProd_succ_cons $hd $h)⟩

/-- The numeral of a rational: an integer numeral, or `n / d`. -/
def mkRatNumeral {u : Level} (α : Q(Type u)) (v : ℚ) : MetaM Q($α) := do
  let n ← mkIntNumeral α v.num
  if v.den == 1 then return n
  let d : Q($α) ← mkNumeral α v.den
  let _dα : Q(Div $α) ← synthInstanceQ q(Div $α)
  return q($n / $d)

/-- Prove the sign in the ring, `-(-(… 1))`, of a permutation of the shape `mkPerm` builds from
`k` swaps, `(swap a b).trans (… (refl _))`, one lemma per swap. -/
def provePermSign {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) {m : ℕ} :
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
    let ⟨s, h⟩ ← provePermSign rα k rest
    let hab : Q($a ≠ $b) ← mkDecideProofQ q($a ≠ $b)
    let h' : Expr := q(intCast_sign_swap_trans $h $hab)
    have h' : Q(((Equiv.Perm.sign $σ : ℤ) : $α) = -$s) := h'
    return ⟨q(-$s), h'⟩

/-- The value of the determinant read off the decomposition `data`, with `U` the entries of its
echelon form. It is `1` for the empty matrix and `0` on a pivot shortfall. On the integer
carrier it is the quotient `s * u / l` of the diagonal products of `U` and `L`, for `s` the sign
of the swaps. On the expression carrier it is the last pivot with the sign `s`. -/
def detValue {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (m : ℕ) (carrier : Carrier)
    (data : BareissData carrier.type) (U : List (List Q($α))) : MetaM Q($α) := do
  if m == 0 then return q(1)
  if data.pivot.size < m then return q(0)
  let positive := data.swaps.size % 2 == 0
  match carrier, data with
  | .int, data =>
    let product (M : Array (Array ℤ)) : ℤ :=
      (List.range m).foldl (fun acc k => acc * (M.getD k #[]).getD k 0) 1
    let diagL := product data.L
    let diagU := product data.U
    mkRatNumeral α ((if positive then 1 else -1) * diagU / diagL)
  | .expr, _ =>
    let p : Q($α) := (U.getD (m - 1) []).getD (m - 1) q(0)
    return if positive then p else q(-$p)

/-- Produce the Bareiss decomposition of the square matrix literal `A` with `entries`, its parsed
entries, and elaborate a proof of `A.det = v` for the value `v` read off the decomposition. -/
def proveEchelonDet {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (iα : Q(IsDomain $α))
    (m : ℕ) (A : Q(Matrix (Fin $m) (Fin $m) $α)) (entries : Array (Array Expr)) :
    MetaM ((v : Q($α)) × Q(($A).det = $v)) := do
  let r ← mkBareissDecomposition rα A entries
  let certifier? := r.model.entryCertifier?
  have c := r.cert
  have cert : Q(Echelon.Decomposition $A) := c.decomp
  -- the diagonal products as `diagProd` on the row literals of `L` and `U`, read off the
  -- certificate; the certified identity evaluates them
  let Lm ← whnfR q(($cert).L)
  let_expr ofLists _ _ _ _ litL := Lm |
    throwError "proveEchelonDet: expected the transform as an `ofLists` literal{indentExpr Lm}"
  have litL : Q(List (List $α)) := litL
  have litU : Q(List (List $α)) := c.U.lit
  have l : Q($α) := q(diagProd 0 $m $litL)
  have uu : Q($α) := q(diagProd 0 $m $litU)
  have hl : Q(∏ i, ofLists $m $m $litL i i = diagProd 0 $m $litL) := q(prod_diag_ofLists $m $litL)
  have hu : Q(∏ i, ofLists $m $m $litU i i = diagProd 0 $m $litU) := q(prod_diag_ofLists $m $litU)
  -- the sign of the certificate's permutation
  let σ : Q(Equiv.Perm (Fin $m)) ← whnfR q(($cert).σ)
  let ⟨s, hs⟩ ← provePermSign rα r.data.swaps.size σ
  -- the identity `l * (s * v) = u` is decided, the kernel evaluating the products, or proved by
  -- the entry certifier on the products unfolded to the entries
  let certifyIdentity : (v : Q($α)) → MetaM Q($l * ($s * $v) = $uu) ← match certifier? with
    | none => pure fun v => mkDecideProofQ q($l * ($s * $v) = $uu)
    | some certifier => do
      let ⟨eL, hL⟩ ← proveDiagProd rα 0 m q(0) q($m) litL
      let ⟨eU, hU⟩ ← proveDiagProd rα 0 m q(0) q($m) litU
      have hL : Q($l = $eL) := hL
      have hU : Q($uu = $eU) := hU
      pure fun v => do
        let hv : Q($eL * ($s * $v) = $eU) ← certifier q($eL * ($s * $v) = $eU)
        return q((congrArg (· * ($s * $v)) $hL).trans (Eq.trans $hv (Eq.symm $hU)))
  -- the value, verified by the identity
  let v ← detValue rα m r.carrier r.data c.U.entries
  let hv ← certifyIdentity v
  -- the projections of `cert` reduce to the `ofLists` matrices of `litL` and `litU`, so the
  -- hypotheses transport by defeq
  have Um : Q(Matrix (Fin $m) (Fin $m) $α) := c.U.matrix
  have hU' : Q(($cert).L * ($A).submatrix ($cert).σ id = $Um) := c.mul_eq
  have hl' : Q(∏ i, ($cert).L i i = $l) := hl
  have hu' : Q(∏ i, $Um i i = $uu) := hu
  have hs' : Q(((Equiv.Perm.sign ($cert).σ : ℤ) : $α) = $s) := hs
  return ⟨v, q(Echelon.Decomposition.det_eq $cert $hU' $hl' $hu' $hs' $hv)⟩

/-- The `norm_det` branch for square matrix literals with non-symbolic entries over a domain the
echelon method handles. It returns `none` where it does not apply, and terms it cannot evaluate are
left to Bird's method, since the fallback model accepts every ring and only the evaluation can tell
whether an entry is in its scope. -/
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
  | .ok rα =>
    let iα : Q(IsDomain $α) ← synthInstanceQ q(IsDomain $α)
    have A : Q(Matrix (Fin $m) (Fin $m) $α) := A
    try
      let ⟨v, pf⟩ ← proveEchelonDet rα iα m A entries
      -- normalise the value where `norm_num` evaluates it, and keep it as it is otherwise (a
      -- `ℤ√d` value)
      let ctx ← readThe Simp.Context
      let r : Simp.Result := { expr := v, proof? := some pf }
      let s ← try Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := false) (e := v)
        catch _ => pure { expr := v }
      return some (← r.mkEqTrans s)
    catch ex =>
      trace[Tactic.evalDet] "{ex.toMessageData}"
      return none

end Mathlib.Tactic.Determinant

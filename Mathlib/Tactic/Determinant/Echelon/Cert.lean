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
row permutation. The model computes it in its carrier by exact division. Where the division is not
exact, as under the rational model's row scaling, the value is the fraction of the two products in
`norm_num`'s normal form.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Echelon Mathlib.Tactic.Matrix

initialize registerTraceClass `Tactic.evalDet

namespace Mathlib.Tactic.Determinant

/-- The proof of `diagProd k c rows = a₀ * (a₁ * (… * 1))` on the literal `rows`, the product of
the diagonal entries from column `k` on, one `diagProd_add_one_cons` per row. -/
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
    let_expr List.cons _ entry suffix := dropListLitQ k row |
      throwError "proveDiagProd: {row} has no entry at {k}"
    have entry : Q($α) := entry
    have suffix : Q(List $α) := suffix
    have k₁Q : Q(Nat) := mkNatLitQ (k + 1)
    have c₁Q : Q(Nat) := mkNatLitQ c
    let ⟨e, h⟩ ← proveDiagProd rα (k + 1) c k₁Q c₁Q rowsTl
    have hdrop : List.drop $kQ $row =Q $entry :: $suffix := ⟨⟩
    have : $rows =Q $row :: $rowsTl := ⟨⟩
    have : $cQ =Q $c₁Q + 1 := ⟨⟩
    have : $k₁Q =Q $kQ + 1 := ⟨⟩
    return ⟨q($entry * $e), q(diagProd_add_one_cons $hdrop $h)⟩

/-- Prove the sign in the ring, `-(-(… 1))`, of a permutation of the shape `mkPerm` builds from
`k` swaps, `(swap a b).trans (… (refl _))`, one lemma per swap. -/
def provePermSign {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) {m : Nat} (k : Nat)
    (σ : Q(Equiv.Perm (Fin $m))) :
    MetaM ((s : Q($α)) × Q(((Equiv.Perm.sign $σ : Int) : $α) = $s)) :=
  match k with
  | 0 => do
    let_expr Equiv.refl _ := σ |
      throwError "provePermSign: expected the identity permutation in{indentExpr σ}"
    have : $σ =Q Equiv.refl (Fin $m) := ⟨⟩
    return ⟨q(1), q(intCast_sign_refl)⟩
  | k + 1 => do
    let_expr Equiv.trans _ _ _ sw rest := σ |
      throwError "provePermSign: expected a swap in{indentExpr σ}"
    let_expr Equiv.swap _ _ a b := sw |
      throwError "provePermSign: expected a swap in{indentExpr σ}"
    have a : Q(Fin $m) := a
    have b : Q(Fin $m) := b
    have rest : Q(Equiv.Perm (Fin $m)) := rest
    let ⟨s, h⟩ ← provePermSign rα k rest
    let hab : Q($a ≠ $b) ← mkDecideProofQ q($a ≠ $b)
    have : $σ =Q (Equiv.swap $a $b).trans $rest := ⟨⟩
    return ⟨q(-$s), q(intCast_sign_swap_trans $h $hab)⟩

/-- The value of the determinant read off the decomposition `data`, computed by `model`. It is `1`
for the empty matrix and `0` when there are fewer than `m` pivots. Otherwise it is `s * u / l`, for
`u` and `l` the diagonal products of `U` and `L` and `s` the sign of the swaps. The quotient is the
carrier's exact division when multiplying back recovers `s * u`, and a fraction in `α` otherwise,
in `norm_num`'s normal form where `norm_num` evaluates it. -/
def detValue {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (m : Nat) {V : Type}
    (model : Model V) (data : BareissData V) : MetaM Q($α) := do
  if m == 0 then return q(1)
  if data.pivot.size < m then return q(0)
  let ops := model.ops
  let diagProduct (M : Array (Array V)) : V :=
    (M.mapIdx fun k row ↦ row.getD k ops.zero).foldl ops.mul ops.one
  let diagL := diagProduct data.L
  let diagU := diagProduct data.U
  let num := if data.swaps.size % 2 == 0 then diagU else ops.sub ops.zero diagU
  let v := ops.divExact num diagL
  if ops.isZero (ops.sub (ops.mul v diagL) num) then
    return (← model.mkEntry v)
  let n : Q($α) ← model.mkEntry num
  let d : Q($α) ← model.mkEntry diagL
  let _dα : Q(Div $α) ← synthInstanceQ q(Div $α)
  let frac : Q($α) := q($n / $d)
  -- The products share the row scales and `diagL` may be negative, so the fraction is put in
  -- `norm_num`'s normal form where `norm_num` evaluates it.
  let some r ← try some <$> Mathlib.Meta.NormNum.derive frac catch _ => pure none | return frac
  return (← r.toSimpResult).expr

/-- Produce the Bareiss decomposition of the square matrix literal `A` with `entries`, its parsed
entries, and elaborate a proof of `A.det = v` for the value `v` read off the decomposition. -/
def proveEchelonDet {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (iα : Q(IsDomain $α))
    (m : Nat) (A : Q(Matrix (Fin $m) (Fin $m) $α)) (entries : Array (Array Expr)) :
    MetaM ((v : Q($α)) × Q(($A).det = $v)) := do
  let r ← mkBareissDecomposition rα A entries
  let cert := r.cert
  have decomp : Q(Echelon.Decomposition $A) := cert.decomp
  let Lm ← whnfR q(($decomp).L)
  let_expr ofLists _ _ _ _ litL := Lm |
    throwError "proveEchelonDet: expected the transform as an `ofLists` literal{indentExpr Lm}"
  have litL : Q(List (List $α)) := litL
  have litU : Q(List (List $α)) := cert.U.lit
  let ⟨diagL, hl⟩ ← proveDiagProd rα 0 m q(0) q($m) litL
  let ⟨diagU, hu⟩ ← proveDiagProd rα 0 m q(0) q($m) litU
  have hl : Q(∏ i, ofLists $m $m $litL i i = $diagL) :=
    q((prod_diag_ofLists $m $litL).trans $hl)
  have hu : Q(∏ i, ofLists $m $m $litU i i = $diagU) :=
    q((prod_diag_ofLists $m $litU).trans $hu)
  -- the sign of the certificate's permutation
  let σ : Q(Equiv.Perm (Fin $m)) ← whnfR q(($decomp).σ)
  let ⟨s, hs⟩ ← provePermSign rα r.data.swaps.size σ
  -- the value, verified by the identity `diagL * (s * v) = diagU` on the products unfolded to
  -- the entries, which the entry certifier proves or the kernel decides
  let v ← detValue rα m r.model r.data
  let hv : Q($diagL * ($s * $v) = $diagU) ←
    (r.model.entryCertifier?.getD mkDecideProofQ) q($diagL * ($s * $v) = $diagU)
  -- the projections of `decomp` reduce to the `ofLists` matrices of `litL` and `litU`, so the
  -- hypotheses transport by defeq
  let Um : Q(Matrix (Fin $m) (Fin $m) $α) := cert.U.matrix
  have hmul : Q(($decomp).L * ($A).submatrix ($decomp).σ id = $Um) := cert.mul_eq
  have hl' : Q(∏ i, ($decomp).L i i = $diagL) := hl
  have hu' : Q(∏ i, $Um i i = $diagU) := hu
  have hs' : Q(((Equiv.Perm.sign ($decomp).σ : Int) : $α) = $s) := hs
  return ⟨v, q(det_eq_of_decomposition $decomp $hmul $hl' $hu' $hs' $hv)⟩

/-- The `norm_det` branch for square matrix literals with non-symbolic entries over a domain the
echelon method handles. It returns `none` where it does not apply, and terms it cannot evaluate are
left to Bird's method, since the fallback model accepts every ring and only the evaluation can tell
whether an entry is in its scope. -/
def normDetEchelon? (A : Expr) : MetaM (Option Simp.Result) := do
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
      return some { expr := v, proof? := some pf }
    catch ex =>
      trace[Tactic.evalDet] "{ex.toMessageData}"
      return none

end Mathlib.Tactic.Determinant

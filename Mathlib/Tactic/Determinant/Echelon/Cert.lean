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
    let ⟨row, rowsTl, _⟩ ← unconsListLitQ rows
    let ⟨entry, suffix, _⟩ ← unconsListLitQ (dropListLitQ k row)
    have k₁Q : Q(Nat) := mkNatLitQ (k + 1)
    have c₁Q : Q(Nat) := mkNatLitQ c
    let ⟨e, h⟩ ← proveDiagProd rα (k + 1) c k₁Q c₁Q rowsTl
    have hdrop : List.drop $kQ $row =Q $entry :: $suffix := ⟨⟩
    have : $cQ =Q $c₁Q + 1 := ⟨⟩
    have : $k₁Q =Q $kQ + 1 := ⟨⟩
    return ⟨q($entry * $e), q(diagProd_add_one_cons $hdrop $h)⟩

/-- The permutation `(swap a₀ b₀).trans (… (refl _))` of the swaps `(a₀, b₀) :: …`, with a proof
of its sign in the ring, `-(-(… 1))`, one lemma per swap. -/
def provePermSign {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (m : Nat)
    (swaps : List (Nat × Nat)) :
    MetaM ((σ : Q(Equiv.Perm (Fin $m))) × (s : Q($α)) ×
      Q(((Equiv.Perm.sign $σ : Int) : $α) = $s)) :=
  match swaps with
  | [] => return ⟨q(Equiv.refl (Fin $m)), q(1), q(intCast_sign_refl)⟩
  | (i, j) :: rest => do
    let ⟨σ, s, h⟩ ← provePermSign rα m rest
    let a : Q(Fin $m) ← mkFinLitQ m i
    let b : Q(Fin $m) ← mkFinLitQ m j
    let hab : Q($a ≠ $b) ← mkDecideProofQ q($a ≠ $b)
    return ⟨q((Equiv.swap $a $b).trans $σ), q(-$s), q(intCast_sign_swap_trans $h $hab)⟩

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
  -- `L`'s literal, rebuilt from the data the certificate was built from
  let rowsL : List (List Q($α)) ← r.data.L.toList.mapM fun row ↦
    row.toList.mapM r.model.mkEntry
  let litL : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (rowsL.map mkListLitQ)
  have litU : Q(List (List $α)) := cert.U.lit
  let ⟨diagL, hl⟩ ← proveDiagProd rα 0 m q(0) q($m) litL
  let ⟨diagU, hu⟩ ← proveDiagProd rα 0 m q(0) q($m) litU
  -- the sign of the certificate's permutation, rebuilt from the swaps with the last one outermost
  let ⟨_, s, hs⟩ ← provePermSign rα m r.data.swaps.toList.reverse
  -- the value, verified by the identity `diagL * (s * v) = diagU` on the products unfolded to
  -- the entries, which the entry certifier proves or the kernel decides
  let v ← detValue rα m r.model r.data
  let hv : Q($diagL * ($s * $v) = $diagU) ←
    (r.model.entryCertifier?.getD mkDecideProofQ) q($diagL * ($s * $v) = $diagU)
  -- `decomp` is built from `r.data`, so `($decomp).L` and `($decomp).σ` are `ofLists m m litL`
  -- and the permutation `provePermSign` built by definition, which the kernel checks for `hL` and
  -- `hs'`. `hmul` is `cert.mul_eq` on the local names.
  let hrfl : Q(ofLists $m $m $litL = ofLists $m $m $litL) := q(rfl)
  have hL : Q(($decomp).L = ofLists $m $m $litL) := hrfl
  have hmul : Q(($decomp).L * ($A).submatrix ($decomp).σ id = ofLists $m $m $litU) :=
    cert.mul_eq
  have hs' : Q(((Equiv.Perm.sign ($decomp).σ : Int) : $α) = $s) := hs
  return ⟨v, q(det_eq_of_decomposition $decomp $hL $hmul $hl $hu $hs' $hv)⟩

/-- The `norm_det` branch for square matrix literals with non-symbolic entries over a domain the
echelon method handles. It returns `none` where it does not apply, and throws on a term it cannot
evaluate. -/
def normDetEchelon? (A : Expr) : MetaM (Option Simp.Result) := do
  let some (m, _, R, entries) ← matchMatrixLit? A | return none
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let .ok rα ← inferBareissRing α | return none
  let iα : Q(IsDomain $α) ← synthInstanceQ q(IsDomain $α)
  have A : Q(Matrix (Fin $m) (Fin $m) $α) := A
  let ⟨v, pf⟩ ← proveEchelonDet rα iα m A entries
  return some { expr := v, proof? := some pf }

end Mathlib.Tactic.Determinant

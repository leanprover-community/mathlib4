/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Tactic.Echelon.Bareiss
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.NormNum.Basic
public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Determinant.Echelon.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Bareiss
public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.NormNum.Basic

/-!
# Determinants of matrix literals by echelon decomposition

`proveEchelonDet` evaluates the determinant of a square matrix literal with non-symbolic entries
through the certificate `Echelon.Decomposition A L σ pivot` of its echelon decomposition.

## Implementation notes

The determinant is the quotient of the diagonal products of `U` and `L`, up to the sign of the
row permutation. The model computes it in its carrier by exact division. Where the division is not
exact, as under the rational model's row scaling, the value is the fraction of the two products in
`norm_num`'s normal form when possible.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Echelon Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Determinant

/-- Compute `diagProd k c rows` with a proof of the equality. -/
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

/-- Compute the sign of the permutation from the swaps with the corresponding proof. -/
def provePermSign {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (m : Nat)
    (swaps : List (Nat × Nat)) :
    MetaM ((σ : Q(Equiv.Perm (Fin $m))) × (s : Q($α)) ×
      Q(((Equiv.Perm.sign $σ : Int) : $α) = $s)) :=
  match swaps with
  | [] => return ⟨q(Equiv.refl (Fin $m)), q(1), q(intCast_sign_refl)⟩
  | (a, b) :: rest => do
    let ⟨σ, s, h⟩ ← provePermSign rα m rest
    let aQ : Q(Fin $m) ← mkFinLitQ m a
    let bQ : Q(Fin $m) ← mkFinLitQ m b
    let hab : Q($aQ ≠ $bQ) ← mkDecideProofQ q($aQ ≠ $bQ)
    return ⟨q((Equiv.swap $aQ $bQ).trans $σ), q(-$s), q(intCast_sign_swap_trans $h $hab)⟩

/-- The value of the determinant read off the decomposition `data`, computed by `s * u / l`,
where `u` and `l` are the diagonal products of `U` and `L` and `s` is the sign of the swaps.
-/
def detValue {u : Level} (α : Q(Type u)) (m : Nat) {V : Type} (model : Model α V)
    (data : BareissData V) : MetaM (Option Q($α)) := do
  let ops := model.ops
  -- In positive characteristic a missing pivot leaves a diagonal entry that is a nonzero multiple
  -- of the characteristic, so the quotient below would not read as zero.
  if data.pivot.size < m then return some (← model.mkEntry ops.zero)
  let diagProduct (M : Array (Array V)) : V :=
    (M.mapIdx fun k row ↦ row.getD k ops.zero).foldl ops.mul ops.one
  let diagL := diagProduct data.L
  let diagU := diagProduct data.U
  let num := if data.swaps.size % 2 == 0 then diagU else ops.sub ops.zero diagU
  -- Try the carrier's exact division first. It always succeeds when the model did not scale
  -- the rows, and can fail for one that did. The fallback constructs a fractional result to
  -- be returned. This requires a `DivisionRing` which exists in common cases of scaling.
  -- In the edge case where the instance doesn't exist this isn't applicable, and we accept
  -- the fallback to Bird determinant.
  let v := ops.divExact num diagL
  if ops.isZero (ops.sub (ops.mul v diagL) num) then
    return some (← model.mkEntry v)
  let n : Q($α) ← model.mkEntry num
  let d : Q($α) ← model.mkEntry diagL
  let some _dα ← synthInstanceQ? q(DivisionRing $α) | return none
  let frac : Q($α) := q($n / $d)
  -- Normalize `frac` when it is `norm_num` evaluable
  let some r ← try some <$> Meta.NormNum.derive frac catch _ => pure none |
    return some frac
  return some (← r.toSimpResult).expr

/-- Construct the value `v` and a proof that `A.det = v` by computing the echelon decomposition. -/
def proveEchelonDet {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) (iα : Q(IsDomain $α))
    (m : Nat) (A : Q(Matrix (Fin $m) (Fin $m) $α)) (entries : Array (Array Q($α))) :
    MetaM (Option ((v : Q($α)) × Q(($A).det = $v))) := do
  let r ← mkBareissDecomposition rα A entries
  let cert := r.cert
  let litL : Q(List (List $α)) := cert.L.lit
  let litU : Q(List (List $α)) := cert.U.lit
  let σ : Q(Equiv.Perm (Fin $m)) := cert.σ
  let pivot : Q(Fin $m → WithTop (Fin $m)) := cert.pivot
  have decomp : Q(Echelon.Decomposition $A (ofLists $m $m $litL) $σ $pivot) := cert.decomp
  let ⟨diagL, hl⟩ ← proveDiagProd rα 0 m q(0) q($m) litL
  let ⟨diagU, hu⟩ ← proveDiagProd rα 0 m q(0) q($m) litU
  let ⟨_, s, hs⟩ ← provePermSign rα m r.data.swaps.toList.reverse
  let some v ← detValue α m r.model r.data | return none
  let hv : Q($diagL * ($s * $v) = $diagU) ←
    (r.model.entryCertifier?.getD (decideCertifier α)).eq q($diagL * ($s * $v)) diagU
  have hmul : Q((ofLists $m $m $litL) * ($A).submatrix $σ id = ofLists $m $m $litU) :=
    cert.mul_eq
  have hs' : Q(((Equiv.Perm.sign $σ : Int) : $α) = $s) := hs
  return some ⟨v, q(det_eq_of_decomposition $decomp $hmul $hl $hu $hs' $hv)⟩

end Mathlib.Tactic.Determinant

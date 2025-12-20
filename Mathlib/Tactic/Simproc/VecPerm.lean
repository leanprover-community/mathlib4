import Mathlib.Data.List.Monad
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Util.Qq

/-! # The vecPerm simproc

The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.

-/

open Lean Elab Meta Simp Qq

namespace FinVec

private partial def mkList {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (vec : Q(Fin $n → $α)) : MetaM (Option <| List Q($α)) := do
  match n, vec with
  | ~q(Nat.succ $m), ~q(Matrix.vecCons $lastOut $prevVec) =>
    let some prevList ← mkList prevVec | return none
    return some <| lastOut :: prevList
  | ~q(0), ~q(Matrix.vecEmpty) => return some []

private partial def mkVec {u : Level} {α : Q(Type u)}
    (n : Q(ℕ)) (vec : Q(List $α)) : MetaM Q(Fin $n → $α) := do
  match n, vec with
  | ~q(Nat.succ $prev), ~q($head :: $rest) =>
    let prevVec ← mkVec prev rest
    return q(Matrix.vecCons $head $prevVec)
  | ~q(0), ~q([]) => return q(Matrix.vecEmpty)

private def permList {α : Type*} (vec : List α) (perm : List Nat) : List α :=
  perm.foldr (init := []) fun head current ↦
    match vec[head]? with
    | some entry =>  entry :: current
    | none => current

private def permAsList (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
    MetaM (Option <| List (Fin vn)) :=
  try
    let _ ← synthInstanceQ q(NeZero $n)
    let out ← (List.range vn).mapM fun idx ↦ do
      let idxQ := mkNatLitQ idx
      let idxQ : Q(Fin $n) := q(Fin.ofNat $n $idxQ)
      let outIdxQ : Q(Fin $n) := q($perm $idxQ)
      unsafe Lean.Meta.evalExpr (Fin vn) q(Fin $n) outIdxQ
    return some out
  catch _ =>
    return none


/--
The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.
This can be used to simplify expressions as follows:
```
example {a b c : Nat} : ![a, b, c] ∘ Equiv.swap 0 1 = ![b, a, c] := by
  simp only [vecPerm]
```
-/
simproc_decl vecPerm (_ ∘ _) := fun e ↦ do
  let ⟨_, ~q(Fin $n → $α), ~q($v ∘ $p)⟩ ← inferTypeQ' e | return .continue
  let ⟨_, ~q(Fin $n → $α), ~q($v)⟩ ← inferTypeQ' v| return .continue
  let some qp ← Qq.checkTypeQ p q(Fin $n → Fin $n) | return .continue
  let some unpermList ← mkList (α := α) (n:= n) v | return .continue
  let vn := unpermList.length
  let some permAsList ← permAsList n vn qp | return .continue
  let outAsList := permList unpermList permAsList
  let outAsListQ := outAsList.foldr (fun head list  ↦ q($head :: $list)) q([])
  let out ← mkVec n outAsListQ
  let pf ← mkAppM ``FinVec.etaExpand_eq #[e]
  let pf ← mkAppM ``Eq.symm #[pf]
  let result : Result := {expr := out, proof? := some pf}
  return Step.continue result

end FinVec

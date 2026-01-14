/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public meta import Mathlib.Data.List.Monad
public meta import Mathlib.Data.Fin.Tuple.Reflection
public meta import Mathlib.Util.Qq

/-! # The vecPerm simproc

The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.

-/

meta section

open Lean Elab Meta Simp Qq

namespace FinVec

/--
Takes an expression representing a vector `Fin n → α` and returns the corresponding
list `List α`. Fails if the vector is not constucted using `Matrix.vecCons` and `Matrix.vecEmpty`.
-/
partial def listOfVecQ {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (vec : Q(Fin $n → $α)) : MetaM (Option <| List Q($α)) := do
  match n, vec with
  | ~q(Nat.succ $m), ~q(Matrix.vecCons $lastOut $prevVec) =>
    return (← listOfVecQ prevVec).map (lastOut :: ·)
  | ~q(0), ~q(Matrix.vecEmpty) => return some []

/--
Takes an expression representing a list of elements of type `α` and outputs the corresponding
vector `Fin n → α`.
-/
partial def vecOfListQ {u : Level} {α : Q(Type u)}
    (n : Q(ℕ)) (vec : Q(List $α)) : MetaM Q(Fin $n → $α) := do
  match n, vec with
  | ~q(Nat.succ $prev), ~q($head :: $rest) =>
    return q(Matrix.vecCons $head $(← vecOfListQ prev rest))
  | ~q(0), ~q([]) => return q(Matrix.vecEmpty)

/--
Given a list `l` of elements of type `α` and a list `perm` of indices (as natural numbers), outputs
the list whose `i`th entry is `l[perm[i]]`. If `perm[i]` is out of bounds, we simply move
to the next `i`.
In the case where `perm ~ [0, ..., l.length-1]`, this is just computing the permutation of `l`
represented by `perm`.
-/
private def permList {α : Type*} (vec : List α) (perm : List Nat) : List α :=
  perm.foldr (init := []) fun head current ↦
    match vec[head]? with
    | some entry =>  entry :: current
    | none => current

/-- Given an expression representing a vector `perm : Fin n → Fin n`, computes the corresponding
list of term of type `Fin n`. This is meant to be used when `perm corresponds to a permutation
of `Fin n`, e.g. `perm = Equiv.swap 0 1`, etc. -/
def listOfVecFinQ (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
    MetaM (Option <| List Nat) :=
  withConfig (fun cfg ↦ { cfg with transparency := .default }) do
    try
      let mut out : List Nat := []
      let _ ← synthInstanceQ q(NeZero $n)
      for idx in List.range vn do
        let idxQ := mkNatLitQ idx
        let idxQ : Q(Fin $n) := q(Fin.ofNat $n $idxQ)
        let outIdxQ : Q(Nat) := q(($perm $idxQ : Nat))
        let outIdxExpr : Q(Nat) ← whnf outIdxQ
        let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
        out := out ++ [outIdx]
      return out
    -- TODO(Paul-Lez): support the `n = 0` case correctly
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
  let some unpermList ← listOfVecQ (α := α) (n:= n) v | return .continue
  let vn := unpermList.length
  let some permAsList ← listOfVecFinQ n vn qp | return .continue
  let outAsList := permList unpermList permAsList
  let outAsListQ := outAsList.foldr (fun head list  ↦ q($head :: $list)) q(([] : List $α))
  let out ← vecOfListQ n outAsListQ
  let pf ← mkAppM ``FinVec.etaExpand_eq #[e]
  let pf ← mkAppM ``Eq.symm #[pf]
  let result : Result := {expr := out, proof? := some pf}
  return Step.continue result

end FinVec

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

public meta section

open Lean Elab Meta Simp Qq

namespace FinVec

/--
Takes an expression representing a vector `Fin n → α` and returns the corresponding
list `List α`. Fails if the vector is not constucted using `Matrix.vecCons` and `Matrix.vecEmpty`.
-/
private partial def listOfVecQ {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (vec : Q(Fin $n → $α)) : MetaM (Option <| List Q($α)) := do
  match n, vec with
  | ~q(Nat.succ $m), ~q(Matrix.vecCons $lastOut $prevVec) =>
    let some prevList ← listOfVecQ prevVec | return none
    return some <| lastOut :: prevList
  | ~q(0), ~q(Matrix.vecEmpty) => return some []

/--
Takes an expression representing a list of elements of type `α` and outputs the corresponding
vector `Fin n → α`.
-/
private partial def vecOfListQ {u : Level} {α : Q(Type u)}
    (n : Q(ℕ)) (vec : Q(List $α)) : MetaM Q(Fin $n → $α) := do
  match n, vec with
  | ~q(Nat.succ $prev), ~q($head :: $rest) =>
    let prevVec ← vecOfListQ prev rest
    return q(Matrix.vecCons $head $prevVec)
  | ~q(0), ~q([]) => return q(Matrix.vecEmpty)

/--
Takes an expression representing a list of elements of type `α` and outputs the corresponding
vector `Fin n → α`.
-/
private partial def vecOfListQ' {α : Type*} (vec : List α) [Nonempty α] : Fin vec.length → α :=
  match vec with
  | head :: rest =>
    Matrix.vecCons head (vecOfListQ' rest)
  | [] => Matrix.vecEmpty

run_meta do
  let vec : Q(List Nat) := q([1, 2, 3])
  let out1 ← whnf q(vecOfListQ' $vec)
  let out2 ← vecOfListQ q(3) vec
  IO.println s!"{out2}"


/--
Given a list `l` of elements `α` and a list `perm` of indices (as natural numbers), outputs
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
private def listOfVecFinQ (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
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

def listOfVecFinQ' (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
    MetaM (Option <| List Nat) :=
  try
    let _ ← synthInstanceQ q(NeZero $n)
    let mut out : List Nat := []
    for idx in List.range vn do
      let idxQ := mkNatLitQ idx
      let idxQ : Q(Fin $n) := q(Fin.ofNat $n $idxQ)
      let outIdxQ : Q(Nat) := q(($perm $idxQ : Nat))
      let outIdxExpr : Q(Nat) ← whnf outIdxQ
      let some outIdx ← Lean.Meta.getNatValue? outIdxExpr |
        IO.println <| ← MessageData.toString s!"Expr is {← whnf outIdxExpr}"
        return none
      out := out ++ [outIdx]
    return some out
  catch _ =>
    return none

run_meta do
  let vec : Q(Fin 3 → Fin 3) := q(![1, 2, 3])
  let some out1 ← listOfVecFinQ' q(3) 3 vec | unreachable!
  let some out2 ← listOfVecFinQ q(3) 3 vec | unreachable!
  Lean.logInfo s!"{out1 == out2}"

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
  let some permAsList ← listOfVecFinQ' n vn qp | return .continue
  Lean.logInfo s!"{permAsList}"
  let outAsList := permList unpermList permAsList
  let outAsListQ := outAsList.foldr (fun head list  ↦ q($head :: $list)) q([])
  let out ← vecOfListQ n outAsListQ
  let pf ← mkAppM ``FinVec.etaExpand_eq #[e]
  let pf ← mkAppM ``Eq.symm #[pf]
  let result : Result := {expr := out, proof? := some pf}
  return Step.continue result

variable {α : Type*} (a b c d : α)

run_meta do
  let a : Q(Fin 3 → Fin 3) := q(![1, 2, 3])
  IO.println f!"{← listOfVecFinQ' q(3) 3 a}"

example : ![a, b, c] ∘ ![0, 1, 2] = ![b, a, c] := by
  simp only [vecPerm]

end FinVec

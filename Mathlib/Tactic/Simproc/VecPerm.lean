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

namespace Mathlib.Tactic.FinVec

open Lean Elab Meta Simp Qq

meta section

/--
Takes an expression representing a vector `Fin n → α` and returns the corresponding
list `List α`. Fails if the vector is not constucted using `Matrix.vecCons` and `Matrix.vecEmpty`.
-/
partial def listOfVecQ {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (vec : Q(Fin $n → $α)) : MetaM (List Q($α)) := do
  match n, vec with
  | ~q(Nat.succ $m), ~q(Matrix.vecCons $lastOut $prevVec) =>
    return lastOut :: (← listOfVecQ prevVec)
  | ~q(0), ~q(Matrix.vecEmpty) => return []
  | _, _ => throwError m!"Invalid inputs: {n} should represent a natural number litteral and {vec}
a function built using the vector notation."

/--
Takes an expression representing a list of elements of type `α` and outputs the corresponding
vector `Fin n → α`.
-/
def vecOfListQ {u : Level} {α : Q(Type u)}
    (n : ℕ) (vec : List Q($α)) : Option Q(Fin $n → $α) := do
  match n, vec with
  | n + 1, head :: rest =>
    return q(Matrix.vecCons $head $(← vecOfListQ n rest))
  | 0, [] => return q(Matrix.vecEmpty)
  | _, _ => none

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
    | some entry => entry :: current
    | none => current

/-- Given an expression representing a vector `perm : Fin n → Fin n`, computes the corresponding
list of term of type `Fin n`. This is meant to be used when `perm corresponds to a permutation
of `Fin n`, e.g. `perm = Equiv.swap 0 1`, etc. -/
def listOfVecFinQ (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
    MetaM (Option <| List Nat) :=
  withDefault do
    try
      let mut out : List Nat := []
      let _ ← synthInstanceQ q(NeZero $n)
      for idx in *...vn do
        let idxQ := mkNatLitQ idx
        let idxQ : Q(Fin $n) := q(Fin.ofNat $n $idxQ)
        let outIdxQ : Q(Nat) := q(($perm $idxQ : Nat))
        -- TODO(Paul-Lez): try to evaluate using the compiler? (probably better for performance)
        let outIdxExpr : Q(Nat) ← whnf outIdxQ
        let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
        out := out ++ [outIdx]
      return out
    -- TODO(Paul-Lez): support the `n = 0` case correctly
    catch _ =>
      return none

theorem eq_etaExpand {α : Type*} {m : ℕ} (v : Fin m → α) : v = FinVec.etaExpand v :=
  (FinVec.etaExpand_eq _).symm

end

public section

/--
The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.
This can be used to simplify expressions as follows:
```
example {a b c : Nat} : ![a, b, c] ∘ Equiv.swap 0 1 = ![b, a, c] := by
  simp only [vecPerm]
```
-/
simproc_decl vecPerm (_ ∘ (_ : Fin _ → Fin _)) := fun e ↦ do
  let ⟨_, ~q(Fin $n → $α), ~q(($v) ∘ ($p : _ → Fin $n'))⟩ ← inferTypeQ' e | return .continue
  let .defEq _ ← isDefEqQ q($n) q($n') | return .continue
  let unpermList ← listOfVecQ (α := α) (n := n) v
  let some permAsList ← listOfVecFinQ n unpermList.length p | return .continue
  let outAsList := permList unpermList permAsList
  let some out := vecOfListQ unpermList.length outAsList | return .continue
  let pf ← mkAppM ``FinVec.eq_etaExpand #[e]
  return Step.continue <| some { expr := out, proof? := pf }

end

end Mathlib.Tactic.FinVec

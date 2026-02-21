/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Util.Qq


/-! # The vecPerm simproc

The `vecPerm` simproc computes the new entries of a vector after applying a permutation to them.

-/

namespace Mathlib.Tactic.FinVec

open Lean Meta Qq

meta section

/--
Takes an expression representing a vector `Fin n → α` and returns the corresponding
list `List α`.
-/
partial def Matrix.matchVecConsPrefixQ {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (vec : Q(Fin $n → $α)) : MetaM (List Q($α) × (m : Q(Nat)) × Q(Fin $m → $α)) := do
  let (l, m, vec) ← Matrix.matchVecConsPrefix n vec
  let l ← l.mapM fun a ↦ do
    let some aQ ← checkTypeQ a q($α) | throwError m!"Expected {a} to have type {α}"
    return aQ
  let some vecQ ← checkTypeQ vec q(Fin $m → $α)
    | throwError m!"Expected {vec} to have type {q(Fin $m → $α)}"
  return (l, ⟨m, vecQ⟩)

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
the list whose `i`th entry is `l[perm[i]]`.
In the case where `perm ~ [0, ..., l.length-1]`, this is just computing the permutation of `l`
represented by `perm`.
-/
private def permList {α : Type*} (vec : List α) (perm : List Nat) : List α :=
  perm.foldr (init := []) fun head current ↦
    match vec[head]? with
    | some entry => entry :: current
    | none => current

/-- Helper function to produce a term of type `Fin m` given by `n` (and a proof that `n < m` via
`decide`.)
Note: this could be inlined below, but this seems to produce a strange Qq bug. -/
def mkFin (n m : Q(Nat)) : MetaM Q(Fin $m) := do
  return q(⟨$n, $(← mkDecideProofQ q($n < $m))⟩)

/-- Given an expression representing a vector `perm : Fin n → Fin n`, computes the corresponding
list of term of type `Fin n`. This is meant to be used when `perm` corresponds to a permutation
of `Fin n`, e.g. `perm = Equiv.swap 0 1`, etc. -/
def listOfVecFinQ (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
    SimpM (Option <| List Nat) := do
    try
      let mut out : List Nat := []
      let _ ← synthInstanceQ q(NeZero $n)
      for idx in *...vn do
        let idxQ := mkNatLitQ idx
        let idxQNew ← mkFin idxQ n
        let outIdxQ := q(($perm $idxQNew : Nat))
        let outIdxExpr := (← Lean.Meta.Simp.simp outIdxQ).expr
        let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
        out := out ++ [outIdx]
      return out
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
  simp [vecPerm, Equiv.swap_apply_def]
```
Note that for this simproc to work, simp needs to be able to simplify the individual applications
of the permutation, i.e. the user may need to provide additional simp lemmas.
-/
simproc_decl vecPerm (_ ∘ (_ : Fin _ → Fin _)) := fun e ↦ do
  let ⟨_, ~q(Fin $n → $α), ~q(($v) ∘ ($p : _ → Fin $n'))⟩ ← inferTypeQ' e | return .continue
  let .defEq _ ← isDefEqQ q($n) q($n') | return .continue
  let (unpermList, ⟨m, _⟩) ← Matrix.matchVecConsPrefixQ (α := α) (n := n) v
  unless ← isDefEq m q(0) do return .continue
  let some permAsList ← listOfVecFinQ n unpermList.length p | return .continue
  let outAsList := permList unpermList permAsList
  let out := PiFin.mkLiteralQ (n := outAsList.length) (outAsList[·]!)
  let pf ← mkAppM ``FinVec.eq_etaExpand #[e]
  return .continue <| some { expr := out, proof? := pf }

end

end Mathlib.Tactic.FinVec

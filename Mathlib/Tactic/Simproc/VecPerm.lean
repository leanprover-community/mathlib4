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
array `Array α`.
-/
partial def Matrix.matchVecConsPrefixQ {u : Level} {α : Q(Type u)} {n : Q(ℕ)}
    (vec : Q(Fin $n → $α)) : MetaM (Array Q($α) × (m : Q(Nat)) × Q(Fin $m → $α)) := do
  let (l, m, vec) ← Matrix.matchVecConsPrefix n vec
  let l ← l.toArray.mapM fun a ↦ do
    let some aQ ← checkTypeQ a q($α) | throwError m!"Expected {a} to have type {α}"
    return aQ
  let some vecQ ← checkTypeQ vec q(Fin $m → $α)
    | throwError m!"Expected {vec} to have type {q(Fin $m → $α)}"
  return (l, ⟨m, vecQ⟩)

/--
Given a list `l` of elements of type `α` and a list `perm` of indices (as natural numbers), outputs
the list whose `i`th entry is `l[perm[i]]`.
In the case where `perm ~ [0, ..., l.length-1]`, this is just computing the permutation of `l`
represented by `perm`.
-/
private def permList {α : Type*} [Inhabited α] (vec : Array α) (perm : Array Nat) : Array α :=
  perm.map (vec[·]!)

/-- Helper function to produce a term of type `Fin m` given by `n` (and a proof that `n < m` via
`decide`.)
Note: this could be inlined below, but this seems to produce a strange Qq bug. -/
def mkFin (n m : Q(Nat)) : MetaM Q(Fin $m) := do
  return q(⟨$n, $(← mkDecideProofQ q($n < $m))⟩)

/-- Given an expression representing a vector `perm : Fin n → Fin n`, computes the corresponding
list of term of type `Fin n`. This is meant to be used when `perm` corresponds to a permutation
of `Fin n`, e.g. `perm = Equiv.swap 0 1`, etc. -/
def arrayOfVecFinQ (n : Q(ℕ)) (vn : ℕ) (perm : Q(Fin $n → Fin $n)) :
    SimpM (Option <| Array Nat) := do
  let mut out : Array Nat := #[]
  for idx in *...vn do
    let idxQ := mkNatLitQ idx
    let idxQNew ← mkFin idxQ n
    let outIdxQ := q(($perm $idxQNew : Nat))
    let outIdxExpr ← Lean.Meta.Simp.dsimp outIdxQ
    let some outIdx ← Lean.Meta.getNatValue? outIdxExpr | return none
    out := out.push outIdx
  return out

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
Note that for this simproc to work, dsimp needs to be able to simplify the individual applications
of the permutation.
-/
simproc_decl vecPerm (_ ∘ (_ : Fin _ → Fin _)) := fun e ↦ do
  let ⟨_, ~q(Fin $n → $α), ~q(($v) ∘ ($p : _ → Fin $n'))⟩ ← inferTypeQ' e | return .continue
  let .defEq _ ← isDefEqQ q($n) q($n') | return .continue
  let (unperm, ⟨m, _⟩) ← Matrix.matchVecConsPrefixQ v
  unless ← isDefEq m q(0) do return .continue
  let some perm ← arrayOfVecFinQ n unperm.size p | return .continue
  let out := permList unperm perm
  let out := PiFin.mkLiteralQ (n := out.size) (out[·]!)
  let pf ← mkAppM ``FinVec.eq_etaExpand #[e]
  return .continue <| some { expr := out, proof? := pf }

end

end Mathlib.Tactic.FinVec

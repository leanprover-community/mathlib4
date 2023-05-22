/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Floris van Doorn
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Basic

/-!
## `norm_num` plugin for big operators

This file adds `norm_num` plugins for `finset.prod` and `finset.sum`.
-/

namespace Mathlib.Meta

open Lean hiding Rat mkRat
open Meta
open Qq

-- FIXME: docs
inductive Finset.ProveEmptyOrConsResult {α : Q(Type u)} (s : Q(Finset $α))
| empty (pf : Q($s = ∅))
| cons (a : Q($α)) (s' : Q(Finset $α)) (h : Q($a ∉ $s')) (pf : Q($s = Finset.cons $a $s' $h))

#print Finset.cons

def Finset.proveEmptyOrCons {α : Q(Type u)} :
  (s : Q(Finset $α)) → Option (Finset.ProveEmptyOrConsResult s) :=
fun s ↦
match Expr.getAppFnArgs s with
| (`EmptyCollection.emptyCollection, _) => .some (.empty (q(rfl) : Q($s = $s)))
| (`Finset.cons, #[α, a, s', h]) => .some (.cons a s' h (q(rfl) : Q($s = $s)))
| _ => .none

namespace NormNum

/-- If `a = b` and we can evaluate `b`, then we can evaluate `a`. -/
def Result.eq_trans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) : Result b → Result a
| .isBool true proof =>
  have a : Q(Prop) := a
  have b : Q(Prop) := b
  have eq : Q($a = $b) := eq
  have proof : Q($b) := proof
  Result.isTrue (x := a) q($eq ▸ $proof)
| .isBool false proof =>
  have a : Q(Prop) := a
  have b : Q(Prop) := b
  have eq : Q($a = $b) := eq
  have proof : Q(¬ $b) := proof
 Result.isFalse (x := a) q($eq ▸ $proof)
| .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
| .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
| .isRat inst q n d proof => Result.isRat inst q n d q($eq ▸ $proof)

protected lemma Finset.prod_empty {β α : Type _} [CommSemiring β] (s : Finset α) (f : α → β)
  (pf : s = ∅) : IsNat (s.prod f) 1 :=
⟨by simp [pf]⟩

protected lemma Finset.prod_cons {β α : Type _} [CommSemiring β] (a : α) (s s' : Finset α) (f : α → β)
  (h : a ∉ s') (pf : s = Finset.cons a s' h) : s.prod f = f a * s'.prod f :=
by simp [pf]

set_option trace.Tactic.norm_num true

@[norm_num @Finset.prod _ _ _ _ _]
partial def evalFinsetProd : NormNumExt where eval {u β} e := do
  dbg_trace "evalFinsetProd"
  let .app (.app (.app (.app (.app (.const `Finset.prod [_, v]) β') α) _) s) f ←
    whnfR e | failure
  dbg_trace "s: {s} f: {f}"
  guard <| ←withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS ← synthInstanceQ (q(CommSemiring $β) : Q(Type u)) <|>
    throwError "not a commutative semiring: {β}"
  dbg_trace "s: {s} f: {f}"
  let rec core : (s : Q(Finset $α)) → MetaM (Result (α := β) q(Finset.prod $s $f)) := fun s ↦
    match Finset.proveEmptyOrCons s with
    | .some (.empty pf) => do
      let n : Q(ℕ) := .lit (.natVal 1) -- Have to construct this expression manually, `q(1)` doesn't parse correctly.
      let pf : Q(IsNat (Finset.prod $s $f) $n) := q(@Finset.prod_empty $β $α $instCS $s $f $pf)
      let res := Result.isNat _ n pf
      dbg_trace "empty. res: {res.toRat}"
      pure res
    | .some (.cons a s' h pf) => do
      let fa : Q($β) := Expr.app f a
      let res_fa ← derive fa
      let res_prod_s' : Result q(Finset.prod $s' $f) ← core s'
      let instS : Q(Semiring $β) := q(($instCS).toSemiring)
      let res : Result _ ← evalMul.core q($fa * Finset.prod $s' $f) _ _ instS res_fa res_prod_s'
      let eq : Q(Finset.prod $s $f = $fa * Finset.prod $s' $f) := q(Finset.prod_cons $a $s $s' $f $h $pf)
      dbg_trace "cons. fa: {fa} res_fa: {res_fa.toRat} res_prod_s': {res_prod_s'.toRat}"
      pure (res.eq_trans eq)
    | .none => throwError "could not match {s}"
  core s

example : Finset.prod (Finset.cons 2 ∅ (Finset.not_mem_empty _)) (λ x => x) = 2 := by norm_num1
example : Finset.prod (Finset.cons 6 (Finset.cons 2 ∅ (Finset.not_mem_empty _)) sorry) (λ x => x) = 12 := by norm_num1

#print Finset.prod

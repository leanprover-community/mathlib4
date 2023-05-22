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
inductive Nat.UnifyZeroOrSuccResult (n : Q(ℕ))
| zero
| succ (n' : Q(ℕ))

def Nat.unifyZeroOrSucc (n : Q(ℕ)) : MetaM (Nat.UnifyZeroOrSuccResult n) := do
if ← isDefEq n q(0)
then return .zero
else do
  let n' : Q(ℕ) ← mkFreshExprMVar q(ℕ)
  if ← isDefEq n q(Nat.succ $n')
  then
    let (.some n') ← getExprMVarAssignment? n'.mvarId! | throwError "could not figure out value of `?n` from `{n} =?= nat.succ ?n`"
    pure (.succ n')
  else throwError "could not unify {n} with 0 or `nat.succ ?n`"


-- FIXME: docs
inductive Finset.ProveEmptyOrConsResult {α : Q(Type u)} (s : Q(Finset $α))
| empty (pf : Q($s = ∅))
| cons (a : Q($α)) (s' : Q(Finset $α)) (h : Q($a ∉ $s')) (pf : Q($s = Finset.cons $a $s' $h))

lemma Finset.insert_eq_cons {α : Type _} [DecidableEq α] (a : α) (s : Finset α) (h : a ∉ s) :
  insert a s = Finset.cons a s h :=
by ext; simp

lemma Finset.range_succ_eq_cons (n' : ℕ) :
  Finset.range (Nat.succ n') =
    Finset.cons n' (Finset.range n') Finset.not_mem_range_self :=
by rw [Finset.range_succ, Finset.insert_eq_cons]

def Finset.proveEmptyOrCons {α : Q(Type u)} :
  (s : Q(Finset $α)) → MetaM (Finset.ProveEmptyOrConsResult s) :=
fun s ↦
match Expr.getAppFnArgs s with
| (`EmptyCollection.emptyCollection, _) => pure (.empty (q(rfl) : Q($s = $s)))
| (`Finset.cons, #[α, a, s', h]) => pure (.cons a s' h (q(rfl) : Q($s = $s)))
| (`Finset.range, #[n]) => show MetaM (Finset.ProveEmptyOrConsResult q(Finset.range $n)) from do
  match ← Nat.unifyZeroOrSucc n with
  | .zero => pure (.empty (q(Finset.range_zero) : Q(Finset.range 0 = ∅)))
  | .succ n' => pure (.cons n' q(Finset.range $n') _ _)
| _ => throwError "could not match {s}"

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
  let rec core : (s : Q(Finset $α)) → MetaM (Result (α := β) q(Finset.prod $s $f)) := fun s ↦ do
    match ← Finset.proveEmptyOrCons s with
    | .empty pf => do
      let n : Q(ℕ) := .lit (.natVal 1) -- Have to construct this expression manually, `q(1)` doesn't parse correctly.
      let pf : Q(IsNat (Finset.prod $s $f) $n) := q(@Finset.prod_empty $β $α $instCS $s $f $pf)
      let res := Result.isNat _ n pf
      dbg_trace "empty. res: {res.toRat}"
      pure res
    | .cons a s' h pf => do
      let fa : Q($β) := Expr.app f a
      let res_fa ← derive fa
      let res_prod_s' : Result q(Finset.prod $s' $f) ← core s'
      let instS : Q(Semiring $β) := q(($instCS).toSemiring)
      let res : Result _ ← evalMul.core q($fa * Finset.prod $s' $f) _ _ instS res_fa res_prod_s'
      let eq : Q(Finset.prod $s $f = $fa * Finset.prod $s' $f) := q(Finset.prod_cons $a $s $s' $f $h $pf)
      dbg_trace "cons. fa: {fa} res_fa: {res_fa.toRat} res_prod_s': {res_prod_s'.toRat}"
      pure (res.eq_trans eq)
  core s

example : Finset.prod (Finset.cons 2 ∅ (Finset.not_mem_empty _)) (λ x => x) = 2 := by norm_num1
example : Finset.prod (Finset.cons 6 (Finset.cons 2 ∅ (Finset.not_mem_empty _)) sorry) (λ x => x) = 12 := by norm_num1

section big_operators

variable {α : Type _} [CommRing α]

open BigOperators

-- Lists:
example : ([1, 2, 1, 3]).sum = 7 := by norm_num only
example : (([1, 2, 1, 3] : List ℚ).map (fun i => i^2)).sum = 15 := by norm_num [-List.map]
example : (List.range 10).sum = 45 := by norm_num only
example : (List.finRange 10).sum = 45 := by norm_num only

-- Multisets:
example : (1 ::ₘ 2 ::ₘ 1 ::ₘ 3 ::ₘ {}).sum = 7 := by norm_num only
example : ((1 ::ₘ 2 ::ₘ 1 ::ₘ 3 ::ₘ {}).map (fun i => i^2)).sum = 15 := by norm_num only
example : (({1, 2, 1, 3} : Multiset ℚ).map (fun i => i^2)).sum = 15 := by
  norm_num [-Multiset.map_cons]
example : (Multiset.range 10).sum = 45 := by norm_num only
example : (↑[1, 2, 1, 3] : Multiset ℕ).sum = 7 := by norm_num only

-- Finsets:
example (f : ℕ → α) : ∏ i in Finset.range 0, f i = 1 := by norm_num1
example (f : Fin 0 → α) : ∏ i : Fin 0, f i = 1 := by norm_num1
example (f : Fin 0 → α) : ∑ i : Fin 0, f i = 0 := by norm_num1
example (f : ℕ → α) : ∑ i in (∅ : Finset ℕ), f i = 0 := by norm_num1
/-
example (f : Fin 3 → α) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by norm_num <;> ring
example (f : Fin 4 → α) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by norm_num <;> ring
example (f : ℕ → α) : ∑ i in {0, 1, 2}, f i = f 0 + f 1 + f 2 := by norm_num; ring
example (f : ℕ → α) : ∑ i in {0, 2, 2, 3, 1, 0}, f i = f 0 + f 1 + f 2 + f 3 := by norm_num; ring
example (f : ℕ → α) : ∑ i in {0, 2, 2 - 3, 3 - 1, 1, 0}, f i = f 0 + f 1 + f 2 := by norm_num; ring
-/
example : (∑ i in Finset.range 10, (i^2 : ℕ)) = 285 := by norm_num1
/-
example : (∑ i in Finset.Icc 5 10, (i^2 : ℕ)) = 355 := by norm_num
example : (∑ i in Finset.Ico 5 10, (i^2 : ℕ)) = 255 := by norm_num
example : (∑ i in Finset.Ioc 5 10, (i^2 : ℕ)) = 330 := by norm_num
example : (∑ i in Finset.Ioo 5 10, (i^2 : ℕ)) = 230 := by norm_num
example : (∑ i : ℤ in Finset.Ioo (-5) 5, i^2) = 60 := by norm_num
example (f : ℕ → α) : ∑ i in Finset.mk {0, 1, 2} dec_trivial, f i = f 0 + f 1 + f 2 :=
  by norm_num; ring
-/

-- Combined with other `norm_num` extensions:
example : ∏ i in Finset.range 9, Nat.sqrt (i + 1) = 96 := by norm_num1
example : ∏ i in {1, 4, 9, 16}, Nat.sqrt i = 24 := by norm_num1
example : ∏ i in Finset.Icc 0 8, Nat.sqrt (i + 1) = 96 := by norm_num1

-- Nested operations:
example : ∑ i : Fin 2, ∑ j : Fin 2, ![![0, 1], ![2, 3]] i j = 6 := by norm_num1

end big_operators


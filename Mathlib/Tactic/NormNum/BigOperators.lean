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
| zero (pf : $n =Q 0)
| succ (n' : Q(ℕ)) (pf : $n =Q Nat.succ $n')

def Nat.unifyZeroOrSucc (n : Q(ℕ)) : MetaM (Nat.UnifyZeroOrSuccResult n) := do
match ← isDefEqQ n q(0) with
| .defEq pf => return .zero pf
| .notDefEq => do
  let n' : Q(ℕ) ← mkFreshExprMVar q(ℕ)
  let ⟨(_pf : $n =Q Nat.succ $n')⟩ ← assertDefEqQ n q(Nat.succ $n')
  let (.some (n'_val : Q(ℕ))) ← getExprMVarAssignment? n'.mvarId! |
    throwError "could not figure out value of `?n` from `{n} =?= nat.succ ?n`"
  pure (.succ n'_val ⟨⟩)

-- FIXME: docs
inductive Finset.ProveEmptyOrConsResult {α : Q(Type u)} (s : Q(Finset $α))
| empty (pf : Q($s = ∅))
| cons (a : Q($α)) (s' : Q(Finset $α)) (h : Q($a ∉ $s')) (pf : Q($s = Finset.cons $a $s' $h))

def Finset.ProveEmptyOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Finset $α)) (t : Q(Finset $β)) :
    Finset.ProveEmptyOrConsResult s → Finset.ProveEmptyOrConsResult t
| .empty pf => .empty pf
| .cons a s' h pf => .cons a s' h pf

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
| (`Finset.range, #[(n : Q(ℕ))]) => do
  match ← Nat.unifyZeroOrSucc n with
  | .zero pf => do
    pure (.empty (q(Finset.range_zero) : Q(Finset.range 0 = ∅)))
  | .succ n' pf => pure <| (Finset.ProveEmptyOrConsResult.cons
      n'
      (q(Finset.range $n'))
      (q(@Finset.not_mem_range_self $n'))
      (q(Finset.range_succ_eq_cons $n'))).uncheckedCast (q(Finset.range (Nat.succ $n')) : Q(Finset ℕ)) s
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

protected lemma Finset.sum_empty {β α : Type _} [CommSemiring β] (f : α → β) :
    IsNat (Finset.sum ∅ f) 0 :=
  ⟨by simp⟩

protected lemma Finset.prod_empty {β α : Type _} [CommSemiring β] (f : α → β) :
    IsNat (Finset.prod ∅ f) 1 :=
  ⟨by simp⟩

partial def evalFinsetBigop {α : Q(Type u)} {β : Q(Type v)}
    (op : Q(Finset $α → ($α → $β) → $β))
    (f : Q($α → $β))
    (res_empty : Result q($op Finset.empty $f))
    (res_cons : {a : Q($α)} -> {s' : Q(Finset $α)} -> {h : Q($a ∉ $s')} ->
      Result (α := β) q($f $a) -> Result (α := β) q($op $s' $f) ->
      MetaM (Result (α := β) q($op (Finset.cons $a $s' $h) $f))) :
    (s : Q(Finset $α)) → MetaM (Result (α := β) q($op $s $f))
| s => do
  match ← Finset.proveEmptyOrCons s with
  | .empty pf => pure <| res_empty.eq_trans q(congr_fun (congr_arg _ $pf) _)
  | .cons a s' h pf => do
    let fa : Q($β) := Expr.app f a
    let res_fa ← derive fa
    let res_op_s' : Result q($op $s' $f) ← evalFinsetBigop op f res_empty @res_cons s'
    let res ← res_cons res_fa res_op_s'
    let eq : Q($op $s $f = $op (Finset.cons $a $s' $h) $f) := q(congr_fun (congr_arg _ $pf) _)
    dbg_trace "cons. fa: {fa} res_fa: {res_fa.toRat} res_op_s': {res_op_s'.toRat}"
    pure (res.eq_trans eq)

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
  let instS : Q(Semiring $β) := q(CommSemiring.toSemiring)
  let n : Q(ℕ) := .lit (.natVal 1) -- Have to construct this expression manually, `q(1)` doesn't parse correctly.
  let pf : Q(IsNat (Finset.prod ∅ $f) $n) := q(@Finset.prod_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.prod) f res_empty (fun {a s' h} res_fa res_prod_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res : Result _ ← evalMul.core q($fa * Finset.prod $s' $f) _ _ instS res_fa res_prod_s'
      let eq : Q(Finset.prod (Finset.cons $a $s' $h) $f = $fa * Finset.prod $s' $f) :=
        q(Finset.prod_cons $h)
      pure <| res.eq_trans eq)
    s

@[norm_num @Finset.sum _ _ _ _ _]
partial def evalFinsetSum : NormNumExt where eval {u β} e := do
  dbg_trace "evalFinsetSum"
  let .app (.app (.app (.app (.app (.const `Finset.sum [_, v]) β') α) _) s) f ←
    whnfR e | failure
  dbg_trace "s: {s} f: {f}"
  guard <| ←withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS ← synthInstanceQ (q(CommSemiring $β) : Q(Type u)) <|>
    throwError "not a commutative semiring: {β}"
  dbg_trace "s: {s} f: {f}"
  let n : Q(ℕ) := .lit (.natVal 0) -- Have to construct this expression manually, `q(0)` doesn't parse correctly.
  let pf : Q(IsNat (Finset.sum ∅ $f) $n) := q(@Finset.sum_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.sum) f res_empty (fun {a s' h} res_fa res_sum_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res : Result _ ← evalAdd.core q($fa + Finset.sum $s' $f) _ _ res_fa res_sum_s'
      let eq : Q(Finset.sum (Finset.cons $a $s' $h) $f = $fa + Finset.sum $s' $f) :=
        q(Finset.sum_cons $h)
      pure <| res.eq_trans eq)
    s

set_option trace.Tactic.norm_num true

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
example : (∏ i in Finset.range 4, ((i+1)^2 : ℕ)) = 576 := by norm_num1
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


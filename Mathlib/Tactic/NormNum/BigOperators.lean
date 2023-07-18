/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Floris van Doorn
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.List.FinRange

#align_import algebra.big_operators.norm_num from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# `norm_num` plugin for big operators

This file adds `norm_num` plugins for `Finset.prod` and `Finset.sum`.

The driving part of this plugin is `Mathlib.Meta.NormNum.evalFinsetBigop`.
We repeatedly use `Finset.proveEmptyOrCons` to try to find a proof that the given set is empty,
or that it consists of one element inserted into a strict subset, and evaluate the big operator
on that subset until the set is completely exhausted.

## See also

 * The `fin_cases` tactic has similar scope: splitting out a finite collection into its elements.

## Porting notes

This plugin is noticeably less powerful than the equivalent version in Mathlib 3: the design of
`norm_num` means plugins have to return numerals, rather than a generic expression.
In particular, we can't use the plugin on sums containing variables.
(See also the TODO note "To support variables".)

## TODOs

 * Support intervals: `Finset.Ico`, `Finset.Icc`, ...
 * To support variables, like in Mathlib 3, turn this into a standalone tactic that unfolds
   the sum/prod, without computing its numeric value (using the `ring` tactic to do some
   normalization?)
-/

namespace Mathlib.Meta

open Lean hiding Rat mkRat
open Meta
open Qq

/-- This represents the result of trying to determine whether the given expression `n : Q(ℕ)`
is either `zero` or `succ`. -/
inductive Nat.UnifyZeroOrSuccResult (n : Q(ℕ))
  /-- `n` unifies with `0` -/
  | zero (pf : $n =Q 0)
  /-- `n` unifies with `succ n'` for this specific `n'` -/
  | succ (n' : Q(ℕ)) (pf : $n =Q Nat.succ $n')

/-- Determine whether the expression `n : Q(ℕ)` unifies with `0` or `Nat.succ n'`.

We do not use `norm_num` functionality because we want definitional equality,
not propositional equality, for use in dependent types.

Fails if neither of the options succeed.
-/
def Nat.unifyZeroOrSucc (n : Q(ℕ)) : MetaM (Nat.UnifyZeroOrSuccResult n) := do
  match ← isDefEqQ n q(0) with
  | .defEq pf => return .zero pf
  | .notDefEq => do
    let n' : Q(ℕ) ← mkFreshExprMVar q(ℕ)
    let ⟨(_pf : $n =Q Nat.succ $n')⟩ ← assertDefEqQ n q(Nat.succ $n')
    let (.some (n'_val : Q(ℕ))) ← getExprMVarAssignment? n'.mvarId! |
      throwError "could not figure out value of `?n` from `{n} =?= Nat.succ ?n`"
    pure (.succ n'_val ⟨⟩)

/-- This represents the result of trying to determine whether the given expression
`s : Q(List $α)` is either empty or consists of an element inserted into a strict subset. -/
inductive List.ProveNilOrConsResult {α : Q(Type u)} (s : Q(List $α))
  /-- The set is Nil. -/
  | nil (pf : Q($s = []))
  /-- The set equals `a` inserted into the strict subset `s'`. -/
  | cons (a : Q($α)) (s' : Q(List $α)) (pf : Q($s = List.cons $a $s'))

/-- If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
def List.ProveNilOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(List $α)) (t : Q(List $β)) :
    List.ProveNilOrConsResult s → List.ProveNilOrConsResult t
  | .nil pf => .nil pf
  | .cons a s' pf => .cons a s' pf

/-- If `s = t` and we can get the result for `t`, then we can get the result for `s`.
-/
def List.ProveNilOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(List $α)}
    (eq : Q($s = $t)) :
    List.ProveNilOrConsResult t → List.ProveNilOrConsResult s
  | .nil pf => .nil q(Eq.trans $eq $pf)
  | .cons a s' pf => .cons a s' q(Eq.trans $eq $pf)

lemma List.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    List.range n = [] := by rw [pn.out, Nat.cast_zero, List.range_zero]

lemma List.range_succ_eq_map' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    List.range n = 0 :: List.map Nat.succ (List.range n') := by
  rw [pn.out, Nat.cast_id, pn', List.range_succ_eq_map]

/-- Either show the expression `s : Q(List α)` is Nil, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def List.proveNilOrCons {α : Q(Type u)} :
  (s : Q(List $α)) → MetaM (List.ProveNilOrConsResult s) :=
  fun s =>
  s.withApp fun e a =>
  match (e, e.constName, a) with
  | (_, `EmptyCollection.EmptyCollection, _) => pure (.nil (q(rfl) : Q((∅ : List $α) = [])))
  | (_, `List.nil, _) => pure (.nil (q(rfl) : Q(([] : List $α) = [])))
  | (_, `List.cons, #[_, a, s']) => pure (.cons a s' (q(rfl) : Q($s = $s)))
  | (_, `List.range, #[(n : Q(ℕ))]) => do
    let instAMO_nat : Q(AddMonoidWithOne ℕ) := q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨nn, pn⟩ ← NormNum.deriveNat n
    let nnL := nn.natLit!
    if nnL = 0 then
      let pn : Q(@NormNum.IsNat _ _ $n 0) := pn
      return .nil (q(List.range_zero' $pn) : Q(List.range $n = []))
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      let pn' : Q($nn = Nat.succ $n') := (q(Eq.refl $nn) : Expr)
      return (List.ProveNilOrConsResult.cons
        q(0)
        q(List.map Nat.succ (List.range $n'))
        q(List.range_succ_eq_map' $pn $pn')).uncheckedCast (q(List.range ($n)) : Q(List ℕ)) s
  | (_, `List.finRange, #[(n : Q(ℕ))]) => do
    match ← Nat.unifyZeroOrSucc n with -- We want definitional equality on `n`.
    | .zero _pf => do
      pure (.nil (q(List.finRange_zero) : Q(List.finRange 0 = [])))
    | .succ n' _pf => pure <| ((List.ProveNilOrConsResult.cons
        q(0 : Fin (Nat.succ $n'))
        (q(List.map Fin.succ (List.finRange $n')))
        (q(List.finRange_succ_eq_map $n'))).uncheckedCast
          (q(List.finRange (Nat.succ $n')) : Q(List (Fin (Nat.succ $n'))))
          s)
  | (.const `List.map [v, _], _, #[β, _, f, xxs]) => do
    have β : Q(Type v) := β
    have f : Q($β → $α) := f
    have xxs : Q(List $β) := xxs
    match ← List.proveNilOrCons xxs with
    | .nil pf => pure <| (.nil
      (q($pf ▸ List.map_nil) : Q(List.map $f $xxs = [])))
    | .cons x xs pf => pure <| (.cons q($f $x) q(List.map $f $xs)
      (q($pf ▸ List.map_cons $f $x $xs) : Q(List.map $f $xxs = $f $x :: List.map $f $xs)))
  | (_, fn, args) =>
    throwError "List.proveNilOrCons: unsupported List expression {s} ({fn}, {args})"

/-- This represents the result of trying to determine whether the given expression
`s : Q(Multiset $α)` is either empty or consists of an element inserted into a strict subset. -/
inductive Multiset.ProveZeroOrConsResult {α : Q(Type u)} (s : Q(Multiset $α))
  /-- The set is zero. -/
  | zero (pf : Q($s = 0))
  /-- The set equals `a` inserted into the strict subset `s'`. -/
  | cons (a : Q($α)) (s' : Q(Multiset $α)) (pf : Q($s = Multiset.cons $a $s'))

/-- If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
def Multiset.ProveZeroOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Multiset $α)) (t : Q(Multiset $β)) :
    Multiset.ProveZeroOrConsResult s → Multiset.ProveZeroOrConsResult t
  | .zero pf => .zero pf
  | .cons a s' pf => .cons a s' pf

/-- If `s = t` and we can get the result for `t`, then we can get the result for `s`.
-/
def Multiset.ProveZeroOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(Multiset $α)}
    (eq : Q($s = $t)) :
    Multiset.ProveZeroOrConsResult t → Multiset.ProveZeroOrConsResult s
  | .zero pf => .zero q(Eq.trans $eq $pf)
  | .cons a s' pf => .cons a s' q(Eq.trans $eq $pf)

lemma Multiset.insert_eq_cons {α : Type _} [DecidableEq α] (a : α) (s : Multiset α) :
    insert a s = Multiset.cons a s := by
  ext; simp

lemma Multiset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Multiset.range n = 0 := by rw [pn.out, Nat.cast_zero, Multiset.range_zero]

lemma Multiset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Multiset.range n = n' ::ₘ Multiset.range n' := by
  rw [pn.out, Nat.cast_id, pn', Multiset.range_succ]

/-- Either show the expression `s : Q(Multiset α)` is Zero, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def Multiset.proveZeroOrCons {α : Q(Type u)} :
  (s : Q(Multiset $α)) → MetaM (Multiset.ProveZeroOrConsResult s) :=
  fun s =>
  match Expr.getAppFnArgs s with
  | (`EmptyCollection.EmptyCollection, _) => pure (.zero (q(rfl) : Q((∅ : Multiset $α) = 0)))
  | (`Zero.zero, _) => pure (.zero (q(rfl) : Q((0 : Multiset $α) = 0)))
  | (`Multiset.cons, #[_, a, s']) => pure (.cons a s' (q(rfl) : Q($s = $s)))
  | (`Multiset.ofList, #[_, (val : Q(List $α))]) => do
    match ← List.proveNilOrCons val with
    | .nil pf => pure <| .zero (q($pf ▸ Multiset.coe_nil) : Q(($val : Multiset $α) = 0))
    | .cons a s' pf => do
      return (.cons a q($s')
        (q($pf ▸ Multiset.cons_coe $a $s') : Q(↑$val = Multiset.cons $a $s')))
  | (`Multiset.range, #[(n : Q(ℕ))]) => do
    let instAMO_nat : Q(AddMonoidWithOne ℕ) := q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨nn, pn⟩ ← NormNum.deriveNat n
    let nnL := nn.natLit!
    if nnL = 0 then
      let pn : Q(@NormNum.IsNat _ _ $n 0) := pn
      return .zero (q(Multiset.range_zero' $pn) : Q(Multiset.range $n = 0))
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      let pn' : Q($nn = Nat.succ $n') := (q(Eq.refl $nn) : Expr)
      return (Multiset.ProveZeroOrConsResult.cons
        n'
        q(Multiset.range $n')
        q(Multiset.range_succ' $pn $pn')).uncheckedCast (q(Multiset.range ($n)) : Q(Multiset ℕ)) s
  | (fn, args) =>
    throwError "Multiset.proveZeroOrCons: unsupported multiset expression {s} ({fn}, {args})"

/-- This represents the result of trying to determine whether the given expression
`s : Q(Finset $α)` is either empty or consists of an element inserted into a strict subset. -/
inductive Finset.ProveEmptyOrConsResult {α : Q(Type u)} (s : Q(Finset $α))
  /-- The set is empty. -/
  | empty (pf : Q($s = ∅))
  /-- The set equals `a` inserted into the strict subset `s'`. -/
  | cons (a : Q($α)) (s' : Q(Finset $α)) (h : Q($a ∉ $s')) (pf : Q($s = Finset.cons $a $s' $h))

/-- If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
def Finset.ProveEmptyOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Finset $α)) (t : Q(Finset $β)) :
    Finset.ProveEmptyOrConsResult s → Finset.ProveEmptyOrConsResult t
  | .empty pf => .empty pf
  | .cons a s' h pf => .cons a s' h pf

/-- If `s = t` and we can get the result for `t`, then we can get the result for `s`.
-/
def Finset.ProveEmptyOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(Finset $α)}
    (eq : Q($s = $t)) :
    Finset.ProveEmptyOrConsResult t → Finset.ProveEmptyOrConsResult s
  | .empty pf => .empty q(Eq.trans $eq $pf)
  | .cons a s' h pf => .cons a s' h q(Eq.trans $eq $pf)

lemma Finset.insert_eq_cons {α : Type _} [DecidableEq α] (a : α) (s : Finset α) (h : a ∉ s) :
    insert a s = Finset.cons a s h := by
  ext; simp

lemma Finset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Finset.range n = {} := by rw [pn.out, Nat.cast_zero, Finset.range_zero]

lemma Finset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Finset.range n = Finset.cons n' (Finset.range n') Finset.not_mem_range_self := by
  rw [pn.out, Nat.cast_id, pn', Finset.range_succ, Finset.insert_eq_cons]

lemma Finset.univ_eq_elems {α : Type _} [Fintype α] (elems : Finset α)
    (complete : ∀ x : α, x ∈ elems) :
    Finset.univ = elems := by
  ext x; simpa using complete x

/-- Either show the expression `s : Q(Finset α)` is empty, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def Finset.proveEmptyOrCons {α : Q(Type u)} :
  (s : Q(Finset $α)) → MetaM (Finset.ProveEmptyOrConsResult s) :=
  fun s =>
  match Expr.getAppFnArgs s with
  | (`EmptyCollection.emptyCollection, _) => pure (.empty (q(rfl) : Q($s = $s)))
  | (`Finset.cons, #[_, a, s', h]) => pure (.cons a s' h (q(rfl) : Q($s = $s)))
  | (`Finset.mk, #[_, (val : Q(Multiset $α)), (nd : Q(Multiset.Nodup $val))]) => do
    match ← Multiset.proveZeroOrCons val with
    | .zero pf => pure <| .empty (q($pf ▸ Finset.mk_zero) : Q(Finset.mk $val $nd = ∅))
    | .cons a s' pf => do
      let h : Q(Multiset.Nodup ($a ::ₘ $s')) := q($pf ▸ $nd)
      let nd' : Q(Multiset.Nodup $s') := q((Multiset.nodup_cons.mp $h).2)
      let h' : Q($a ∉ $s') := q((Multiset.nodup_cons.mp $h).1)
      return (.cons a q(Finset.mk $s' $nd') h'
        (q($pf ▸ Finset.mk_cons $h) : Q(Finset.mk $val $nd = Finset.cons $a ⟨$s', $nd'⟩ $h')))
  | (`Finset.range, #[(n : Q(ℕ))]) => do
    let instAMO_nat : Q(AddMonoidWithOne ℕ) := q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨nn, pn⟩ ← NormNum.deriveNat n
    let nnL := nn.natLit!
    if nnL = 0 then
      let pn : Q(@NormNum.IsNat _ _ $n 0) := pn
      return .empty (q(Finset.range_zero' $pn) : Q(Finset.range $n = {}))
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      let pn' : Q($nn = Nat.succ $n') := (q(Eq.refl $nn) : Expr)
      return (Finset.ProveEmptyOrConsResult.cons
        n'
        (q(Finset.range $n'))
        (q(@Finset.not_mem_range_self $n'))
        (q(Finset.range_succ' $pn $pn'))).uncheckedCast
          (q(Finset.range $n) : Q(Finset ℕ))
          s
  | (`Finset.univ, #[_, instFT]) => do
    match Expr.getAppFnArgs (← whnfI instFT) with
    | (`Fintype.mk, #[_, (elems : Q(Finset $α)), (complete : Q(∀ x : $α, x ∈ $elems))]) => do
      have _instFT : Q(Fintype $α) := instFT
      let res ← Finset.proveEmptyOrCons elems
      pure <| res.eq_trans (q(Finset.univ_eq_elems $elems $complete) : Q(Finset.univ = $elems))
    | e =>
      throwError "Finset.proveEmptyOrCons: could not determine elements of Fintype instance {e}"
  | (fn, args) =>
    throwError "Finset.proveEmptyOrCons: unsupported finset expression {s} ({fn}, {args})"

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

/-- Evaluate a big operator applied to a finset by repeating `proveEmptyOrCons` until
we exhaust all elements of the set. -/
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
      pure (res.eq_trans eq)

/-- `norm_num` plugin for evaluating products of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
@[norm_num @Finset.prod _ _ _ _ _]
partial def evalFinsetProd : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const `Finset.prod [_, v]) β') α) _) s) f ←
    whnfR e | failure
  guard <| ←withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS ← synthInstanceQ (q(CommSemiring $β) : Q(Type u)) <|>
    throwError "not a commutative semiring: {β}"
  let instS : Q(Semiring $β) := q(CommSemiring.toSemiring)
  -- Have to construct this expression manually, `q(1)` doesn't parse correctly:
  let n : Q(ℕ) := .lit (.natVal 1)
  let pf : Q(IsNat (Finset.prod ∅ $f) $n) := q(@Finset.prod_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.prod) f res_empty (fun {a s' h} res_fa res_prod_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res : Result _ ← evalMul.core q($fa * Finset.prod $s' $f) q((· * ·)) _ _ instS res_fa
        res_prod_s'
      let eq : Q(Finset.prod (Finset.cons $a $s' $h) $f = $fa * Finset.prod $s' $f) :=
        q(Finset.prod_cons $h)
      pure <| res.eq_trans eq)
    s

/-- `norm_num` plugin for evaluating sums of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
@[norm_num @Finset.sum _ _ _ _ _]
partial def evalFinsetSum : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const `Finset.sum [_, v]) β') α) _) s) f ←
    whnfR e | failure
  guard <| ←withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS ← synthInstanceQ (q(CommSemiring $β) : Q(Type u)) <|>
    throwError "not a commutative semiring: {β}"
  let n : Q(ℕ) := q(0)
  let pf : Q(IsNat (Finset.sum ∅ $f) $n) := q(@Finset.sum_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.sum) f res_empty (fun {a s' h} res_fa res_sum_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res : Result _ ← evalAdd.core q($fa + Finset.sum $s' $f) q((· + ·)) _ _ res_fa res_sum_s'
      let eq : Q(Finset.sum (Finset.cons $a $s' $h) $f = $fa + Finset.sum $s' $f) :=
        q(Finset.sum_cons $h)
      pure <| res.eq_trans eq)
    s

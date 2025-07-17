/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Floris van Doorn
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

## TODO

* Support intervals: `Finset.Ico`, `Finset.Icc`, ...
* To support variables, like in Mathlib 3, turn this into a standalone tactic that unfolds
  the sum/prod, without computing its numeric value (using the `ring` tactic to do some
  normalization?)
-/

namespace Mathlib.Meta

open Lean
open Meta
open Qq

variable {u v : Level}

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

set_option linter.unusedVariables false in
/-- Either show the expression `s : Q(List α)` is Nil, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def List.proveNilOrCons {u : Level} {α : Q(Type u)} (s : Q(List $α)) :
    MetaM (List.ProveNilOrConsResult s) :=
  s.withApp fun e a =>
  match (e, e.constName, a) with
  | (_, ``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.nil q(.refl []))
  | (_, ``List.nil, _) => haveI : $s =Q [] := ⟨⟩; pure (.nil q(rfl))
  | (_, ``List.cons, #[_, (a : Q($α)), (s' : Q(List $α))]) =>
    haveI : $s =Q $a :: $s' := ⟨⟩; pure (.cons a s' q(rfl))
  | (_, ``List.range, #[(n : Q(ℕ))]) =>
    have s : Q(List ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveNilOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI' : $nn =Q 0 := ⟨⟩
      return .nil q(List.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      have : $nn =Q .succ $n' := ⟨⟩
      return .cons _ _ q(List.range_succ_eq_map' $pn (.refl $nn))
  | (_, ``List.finRange, #[(n : Q(ℕ))]) =>
    have s : Q(List (Fin $n)) := s
    .uncheckedCast _ _ <$> show MetaM (ProveNilOrConsResult s) from do
    haveI' : $s =Q .finRange $n := ⟨⟩
    return match ← Nat.unifyZeroOrSucc n with -- We want definitional equality on `n`.
    | .zero _pf => .nil q(List.finRange_zero)
    | .succ n' _pf => .cons _ _ q(List.finRange_succ_eq_map $n')
  | (.const ``List.map [v, _], _, #[(β : Q(Type v)), _, (f : Q($β → $α)), (xxs : Q(List $β))]) => do
    haveI' : $s =Q ($xxs).map $f := ⟨⟩
    return match ← List.proveNilOrCons xxs with
    | .nil pf => .nil q(($pf ▸ List.map_nil : List.map _ _ = _))
    | .cons x xs pf => .cons q($f $x) q(($xs).map $f)
      q(($pf ▸ List.map_cons : List.map _ _ = _))
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

lemma Multiset.insert_eq_cons {α : Type*} (a : α) (s : Multiset α) :
    insert a s = Multiset.cons a s :=
  rfl

lemma Multiset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Multiset.range n = 0 := by rw [pn.out, Nat.cast_zero, Multiset.range_zero]

lemma Multiset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Multiset.range n = n' ::ₘ Multiset.range n' := by
  rw [pn.out, Nat.cast_id, pn', Multiset.range_succ]

/-- Either show the expression `s : Q(Multiset α)` is Zero, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def Multiset.proveZeroOrCons {α : Q(Type u)} (s : Q(Multiset $α)) :
    MetaM (Multiset.ProveZeroOrConsResult s) :=
  match s.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.zero q(rfl))
  | (``Zero.zero, _) => haveI : $s =Q 0 := ⟨⟩; pure (.zero q(rfl))
  | (``Multiset.cons, #[_, (a : Q($α)), (s' : Q(Multiset $α))]) =>
    haveI : $s =Q .cons $a $s' := ⟨⟩
    pure (.cons a s' q(rfl))
  | (``Multiset.ofList, #[_, (val : Q(List $α))]) => do
    haveI : $s =Q .ofList $val := ⟨⟩
    return match ← List.proveNilOrCons val with
    | .nil pf => .zero q($pf ▸ Multiset.coe_nil : Multiset.ofList _ = _)
    | .cons a s' pf => .cons a q($s') q($pf ▸ Multiset.cons_coe $a $s' : Multiset.ofList _ = _)
  | (``Multiset.range, #[(n : Q(ℕ))]) => do
    have s : Q(Multiset ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveZeroOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI' : $nn =Q 0 := ⟨⟩
      return .zero q(Multiset.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      haveI' : $nn =Q ($n').succ := ⟨⟩
      return .cons _ _ q(Multiset.range_succ' $pn rfl)
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

lemma Finset.insert_eq_cons {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (h : a ∉ s) :
    insert a s = Finset.cons a s h := by
  ext; simp

lemma Finset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Finset.range n = {} := by rw [pn.out, Nat.cast_zero, Finset.range_zero]

lemma Finset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Finset.range n = Finset.cons n' (Finset.range n') Finset.notMem_range_self := by
  rw [pn.out, Nat.cast_id, pn', Finset.range_succ, Finset.insert_eq_cons]

lemma Finset.univ_eq_elems {α : Type*} [Fintype α] (elems : Finset α)
    (complete : ∀ x : α, x ∈ elems) :
    Finset.univ = elems := by
  ext x; simpa using complete x

/-- Either show the expression `s : Q(Finset α)` is empty, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def Finset.proveEmptyOrCons {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (ProveEmptyOrConsResult s) :=
  match s.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.empty q(rfl))
  | (``Finset.cons, #[_, (a : Q($α)), (s' : Q(Finset $α)), (h : Q($a ∉ $s'))]) =>
    haveI : $s =Q .cons $a $s' $h := ⟨⟩
    pure (.cons a s' h q(.refl $s))
  | (``Finset.mk, #[_, (val : Q(Multiset $α)), (nd : Q(Multiset.Nodup $val))]) => do
    match ← Multiset.proveZeroOrCons val with
    | .zero pf => pure <| .empty (q($pf ▸ Finset.mk_zero) : Q(Finset.mk $val $nd = ∅))
    | .cons a s' pf => do
      let h : Q(Multiset.Nodup ($a ::ₘ $s')) := q($pf ▸ $nd)
      let nd' : Q(Multiset.Nodup $s') := q((Multiset.nodup_cons.mp $h).2)
      let h' : Q($a ∉ $s') := q((Multiset.nodup_cons.mp $h).1)
      return (.cons a q(Finset.mk $s' $nd') h'
        (q($pf ▸ Finset.mk_cons $h) : Q(Finset.mk $val $nd = Finset.cons $a ⟨$s', $nd'⟩ $h')))
  | (``Finset.range, #[(n : Q(ℕ))]) =>
    have s : Q(Finset ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveEmptyOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI : $nn =Q 0 := ⟨⟩
      return .empty q(Finset.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      haveI' : $nn =Q ($n').succ := ⟨⟩
      return .cons n' _ _ q(Finset.range_succ' $pn (.refl $nn))
  | (``Finset.univ, #[_, (instFT : Q(Fintype $α))]) => do
    haveI' : $s =Q .univ := ⟨⟩
    match (← whnfI instFT).getAppFnArgs with
    | (``Fintype.mk, #[_, (elems : Q(Finset $α)), (complete : Q(∀ x : $α, x ∈ $elems))]) => do
      let res ← Finset.proveEmptyOrCons elems
      pure <| res.eq_trans q(Finset.univ_eq_elems $elems $complete)
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

protected lemma Finset.sum_empty {β α : Type*} [CommSemiring β] (f : α → β) :
    IsNat (Finset.sum ∅ f) 0 :=
  ⟨by simp⟩

protected lemma Finset.prod_empty {β α : Type*} [CommSemiring β] (f : α → β) :
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
      let fa : Q($β) := Expr.betaRev f #[a]
      let res_fa ← derive fa
      let res_op_s' : Result q($op $s' $f) ← evalFinsetBigop op f res_empty @res_cons s'
      let res ← res_cons res_fa res_op_s'
      let eq : Q($op $s $f = $op (Finset.cons $a $s' $h) $f) := q(congr_fun (congr_arg _ $pf) _)
      pure (res.eq_trans eq)

attribute [local instance] monadLiftOptionMetaM in
/-- `norm_num` plugin for evaluating products of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
@[norm_num @Finset.prod _ _ _ _ _]
partial def evalFinsetProd : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const ``Finset.prod [v, _]) α) β') _) s) f ←
    whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS : Q(CommSemiring $β) ← synthInstanceQ q(CommSemiring $β) <|>
    throwError "not a commutative semiring: {β}"
  let instS : Q(Semiring $β) := q(CommSemiring.toSemiring)
  -- Have to construct this expression manually, `q(1)` doesn't parse correctly:
  let n : Q(ℕ) := .lit (.natVal 1)
  let pf : Q(IsNat (Finset.prod ∅ $f) $n) := q(@Finset.prod_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.prod) f res_empty (fun {a s' h} res_fa res_prod_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res ← evalMul.core q($fa * Finset.prod $s' $f) q(HMul.hMul) _ _ instS res_fa
        res_prod_s'
      let eq : Q(Finset.prod (Finset.cons $a $s' $h) $f = $fa * Finset.prod $s' $f) :=
        q(Finset.prod_cons $h)
      pure <| res.eq_trans eq)
    s

attribute [local instance] monadLiftOptionMetaM in
/-- `norm_num` plugin for evaluating sums of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
@[norm_num @Finset.sum _ _ _ _ _]
partial def evalFinsetSum : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const ``Finset.sum [v, _]) α) β') _) s) f ←
    whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS : Q(CommSemiring $β) ← synthInstanceQ q(CommSemiring $β) <|>
    throwError "not a commutative semiring: {β}"
  let n : Q(ℕ) := mkRawNatLit 0
  let pf : Q(IsNat (Finset.sum ∅ $f) $n) := q(@Finset.sum_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.sum) f res_empty (fun {a s' h} res_fa res_sum_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res ← evalAdd.core q($fa + Finset.sum $s' $f) q(HAdd.hAdd) _ _ res_fa res_sum_s'
      let eq : Q(Finset.sum (Finset.cons $a $s' $h) $f = $fa + Finset.sum $s' $f) :=
        q(Finset.sum_cons $h)
      pure <| res.eq_trans eq)
    s

end NormNum

end Meta

end Mathlib

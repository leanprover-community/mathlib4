import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Tactic.NormNum.BigOperators

namespace Mathlib.Meta

open Lean hiding Rat mkRat
open Meta
open Qq

structure EvalResult {α : Q(Type u)} (e : Q($α)) :=
(val : Q($α)) (pf : Q($e = $val))

def EvalResult.eq_trans {α : Q(Type u)} {e e' : Q($α)} (eq : Q($e = $e')) :
  EvalResult e' → EvalResult e
| ⟨val, pf⟩ => ⟨val, q(Eq.trans $eq $pf)⟩

/-
protected lemma Finset.sum_empty {β α : Type _} [CommSemiring β] (f : α → β) :
    IsNat (Finset.sum ∅ f) 0 :=
  ⟨by simp⟩

protected lemma Finset.prod_empty {β α : Type _} [CommSemiring β] (f : α → β) :
    IsNat (Finset.prod ∅ f) 1 :=
  ⟨by simp⟩
-/

/-- Evaluate a big operator applied to a finset by repeating `proveEmptyOrCons` until
we exhaust all elements of the set. -/
partial def Finset.evalBigop {α : Q(Type u)} {β : Q(Type v)}
    (op : Q(Finset $α → ($α → $β) → $β))
    (f : Q($α → $β))
    (evalF : (a : Q($α)) → MetaM (EvalResult (q($f $a) : Q($β))))
    (res_empty : EvalResult q($op Finset.empty $f))
    (res_cons : {a : Q($α)} -> {s' : Q(Finset $α)} -> {h : Q($a ∉ $s')} ->
      EvalResult (α := β) q($f $a) -> EvalResult (α := β) q($op $s' $f) ->
      MetaM (EvalResult (α := β) q($op (Finset.cons $a $s' $h) $f))) :
    (s : Q(Finset $α)) → MetaM (EvalResult (α := β) q($op $s $f))
| s => do
  match ← Finset.proveEmptyOrCons s with
  | .empty pf => pure <| res_empty.eq_trans q(congr_fun (congr_arg _ $pf) _)
  | .cons a s' h pf => do
    let res_fa ← evalF a
    let res_op_s' : EvalResult q($op $s' $f) ← Finset.evalBigop op f evalF res_empty @res_cons s'
    let res ← res_cons res_fa res_op_s'
    let eq : Q($op $s $f = $op (Finset.cons $a $s' $h) $f) := q(congr_fun (congr_arg _ $pf) _)
    pure (res.eq_trans eq)

@[to_additive]
theorem Finset.prod_cons {β : Type u} {α : Type v} {s : Finset α} {a : α} {f : α → β} [CommMonoid β]
  (h : ¬a ∈ s) : (Finset.prod (Finset.cons a s h) f) = f a * Finset.prod s f :=
_root_.Finset.prod_cons h


/-- `norm_num` plugin for evaluating sums of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
partial def Finset.evalSum {β : Q(Type u)} {α : Q(Type v)} {instACM : Q(AddCommMonoid $β)}
    (s : Q(Finset $α)) (f : Q($α → $β))
    (evalF : (a : Q($α)) → MetaM (EvalResult (q($f $a) : Q($β))))
    (evalAdd : {a b : Q($β)} → EvalResult a → EvalResult b → MetaM (EvalResult (α := β) q($a + $b))) :
    MetaM (EvalResult q(@Finset.sum $β $α $instACM $s $f)) := do
  let res ← Finset.evalBigop q(Finset.sum) f evalF _ (fun {a s' h} res_fa res_sum_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res : EvalResult _ ← evalAdd res_fa res_sum_s'
      let eq : Q(Finset.sum (Finset.cons $a $s' $h) $f = $fa + Finset.sum $s' $f) :=
        q(Finset.sum_cons $h)
      pure <| res.eq_trans eq)
    s
  pure res

partial def Matrix.evalDetFin {R : Q(Type u)} {n : Q(ℕ)} (_instCR : Q(CommRing $R))
    (M : Q(Matrix (Fin $n) (Fin $n) $R)) :
    MetaM (EvalResult q(Matrix.det $M)) := do
  match ← Nat.unifyZeroOrSucc n with
  | .zero _ => pure ⟨q(1), q(Matrix.det_fin_zero)⟩
  | .succ _n' _pf => do
    pure <| (← Finset.evalSum _ _).eq_trans q(Matrix.det_succ_row_zero $M)

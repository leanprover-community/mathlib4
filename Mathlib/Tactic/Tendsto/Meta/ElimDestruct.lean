/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tendsto.Meta.Defs
import Mathlib.Tactic.Tendsto.Meta.ConstSimp
import Qq

/-!
# TODO
-/

open Filter Asymptotics TendstoTactic Stream' Seq

namespace TendstoTactic

namespace ElimDestruct

section Const

@[PreMS_const]
theorem const_const (c : ℝ) : PreMS.const [] c = c := rfl

@[PreMS_const]
theorem one_const : PreMS.one [] = 1 := rfl

@[PreMS_const]
theorem neg_const (x : PreMS []) : (x.neg) = -x := by simp [PreMS.neg, PreMS.mulConst]

@[PreMS_const]
theorem add_const (x y : PreMS []) : (PreMS.add x y) = x + y := rfl

@[PreMS_const]
theorem mul_const (x y : PreMS []) : (PreMS.mul x y) = x * y := by simp [PreMS.mul]

@[PreMS_const]
theorem inv_const (x : PreMS []) : (PreMS.inv x) = x⁻¹ := rfl

@[PreMS_const]
theorem pow_const (x : PreMS []) (a : ℝ) : (PreMS.pow x a) = x^a := rfl

end Const

section Destruct

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

theorem const_destruct (c : ℝ) : destruct (PreMS.const (basis_hd :: basis_tl) c) =
    .some ((0, PreMS.const basis_tl c), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem monomial_zero_destruct : destruct (PreMS.monomial (basis_hd :: basis_tl) 0) =
    .some ((1, PreMS.one _), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem monomial_succ_destruct (m : ℕ) : destruct (PreMS.monomial (basis_hd :: basis_tl) (m + 1)) =
    .some ((0, PreMS.monomial basis_tl m), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem neg_destruct (ms : PreMS (basis_hd :: basis_tl)) : destruct ms.neg =
    match destruct ms with
    | none => none
    | some ((exp, coef), tl) => .some ((exp, coef.neg),
        PreMS.neg (basis := basis_hd :: basis_tl) tl) := by
  cases ms <;> simp

theorem add_destruct (x y : PreMS (basis_hd :: basis_tl)) : destruct (x + y) =
    match destruct x, destruct y with
    | none, none => none
    | none, some r => some r
    | some r, none => some r
    | some ((x_exp, x_coef), x_tl), some ((y_exp, y_coef), y_tl) =>
      if y_exp < x_exp then
        .some ((x_exp, x_coef), (PreMS.add x_tl y))
      else if x_exp < y_exp then
        .some ((y_exp, y_coef), (PreMS.add x y_tl))
      else
        .some ((x_exp, x_coef.add y_coef), (@PreMS.add (basis_hd :: basis_tl) x_tl y_tl)) := by
  rw [PreMS.add_unfold]
  simp [PreMS.add']
  cases x <;> cases y <;> simp
  split_ifs <;> simp <;> try rfl
  constructor <;> rfl

theorem mul_destruct (x y : PreMS (basis_hd :: basis_tl)) : destruct (x.mul y) =
    match destruct x, destruct y with
    | none, _ => none
    | _, none => none
    | some ((x_exp, x_coef), x_tl), some ((y_exp, y_coef), y_tl) =>
      .some ((x_exp + y_exp, x_coef.mul y_coef), ((PreMS.mulMonomial y_tl x_coef x_exp).add
      (PreMS.mul x_tl y))) := by
  cases' x with x_exp x_coef x_tl <;> cases' y with y_exp y_coef y_tl <;> simp
  rfl

theorem mulMonomial_destruct (b : PreMS (basis_hd :: basis_tl)) (m_coef : PreMS basis_tl)
    (m_exp : ℝ) : destruct (b.mulMonomial m_coef m_exp) =
    match destruct b with
    | none => none
    | some ((b_exp, b_coef), b_tl) =>
      some ((m_exp + b_exp, m_coef.mul b_coef),
          PreMS.mulMonomial (basis_hd := basis_hd) b_tl m_coef m_exp) := by
  cases b <;> simp

theorem apply_destruct (s : PreMS.LazySeries) (ms : PreMS (basis_hd :: basis_tl)) :
    destruct (s.apply ms) =
    match destruct s with
    | none => none
    | some (s_hd, s_tl) =>
       .some ((0, PreMS.const _ s_hd), (PreMS.LazySeries.apply s_tl ms).mul ms) := by
  cases s <;> simp

theorem inv_destruct (ms : PreMS (basis_hd :: basis_tl)) : destruct ms.inv =
    match destruct ms with
    | none => none
    | some ((exp, coef), tl) => destruct (PreMS.mulMonomial (basis_hd := basis_hd)
      (PreMS.invSeries.apply (PreMS.mulMonomial (PreMS.neg tl) coef.inv (-exp)))
      coef.inv (-exp)) := by
  cases ms
  · simp [PreMS.inv]
  · conv => lhs; unfold PreMS.inv
    simp only [Stream'.Seq.destruct_cons]

theorem pow_destruct (ms : PreMS (basis_hd :: basis_tl)) (a : ℝ) : destruct (ms.pow a) =
    match destruct ms with
    | none =>
      if a = 0 then
        .some ((0, PreMS.const basis_tl 1), @PreMS.nil basis_hd basis_tl)
      else
        .none
    | some ((exp, coef), tl) => destruct <| PreMS.mulMonomial (basis_hd := basis_hd)
      ((PreMS.powSeries a).apply (PreMS.mulMonomial tl coef.inv (-exp))) (coef.pow a)
      (exp * a) := by
  cases' ms with exp coef tl
  · simp [PreMS.pow]
    split_ifs
    · simp [PreMS.one, const_destruct]
    · simp
  · simp [PreMS.pow]

theorem invSeries_destruct : destruct PreMS.invSeries = .some (1, PreMS.invSeries) := by
  conv => lhs; rw [PreMS.invSeries_eq_cons_self]; simp

theorem powSeriesFrom_destruct (x : ℝ) (acc : ℝ) (n : ℕ) : destruct (PreMS.powSeriesFrom x acc n) =
    .some (acc, PreMS.powSeriesFrom x (acc * (x - n) / (n + 1)) (n + 1)) := by
  conv => lhs; rw [PreMS.powSeriesFrom_eq_cons]
  simp

theorem powSeries_destruct (x : ℝ) :
    destruct (PreMS.powSeries x) = .some (1, PreMS.powSeriesFrom x x 1) := by
  unfold PreMS.powSeries
  simp [powSeriesFrom_destruct]

end Destruct

open Lean Elab Meta Tactic Qq

-- TODO: already done?
def simpWith (pf : Expr) : SimpM Simp.Step := do
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit {expr := rhs, proof? := pf}

simproc elimDestruct (Stream'.Seq.destruct _) := fun e => do
  let (``Stream'.Seq.destruct, #[_, target]) := e.getAppFnArgs | return .continue
  let ⟨1, targetType, target⟩ := ← inferTypeQ target | return .continue
  match targetType with
  | ~q(PreMS.LazySeries) =>
    match target with
    | ~q(PreMS.invSeries) => simpWith q(invSeries_destruct)
    | ~q(PreMS.powSeriesFrom $x $acc $n) => simpWith q(powSeriesFrom_destruct $x $acc $n)
    | ~q(PreMS.powSeries $x) => simpWith q(powSeries_destruct $x)
    | _ => return .continue
  | ~q(PreMS $basis) =>
    let ~q(List.cons $basis_hd $basis_tl) := basis | return .continue
    match target with
    | ~q(PreMS.nil) =>
      return .done {
        expr := q(@Option.none (Seq1 (ℝ × PreMS $basis_tl))),
        proof? := q(@Stream'.Seq.destruct_nil (ℝ × (PreMS $basis_tl)))
      }
    | ~q(PreMS.cons $hd $tl) =>
      return .done {
        expr := q(Option.some ($hd, $tl)),
        proof? := q(Stream'.Seq.destruct_cons $hd $tl)
      }
    | ~q(PreMS.const _ $c) => simpWith q(@const_destruct $basis_hd $basis_tl $c)
    | ~q(PreMS.monomial _ $n) =>
      match (← getNatValue? n).get! with
      | 0 => simpWith q(@monomial_zero_destruct $basis_hd $basis_tl)
      | m + 1 => simpWith q(@monomial_succ_destruct $basis_hd $basis_tl $m)
    | ~q(PreMS.neg $arg) => simpWith q(neg_destruct $arg)
    | ~q(PreMS.add $arg1 $arg2) => simpWith q(add_destruct $arg1 $arg2)
    | ~q(PreMS.mul $arg1 $arg2) => simpWith q(mul_destruct $arg1 $arg2)
    | ~q(PreMS.mulMonomial $b $m_coef $m_exp) =>
      simpWith q(mulMonomial_destruct $b $m_coef $m_exp)
    | ~q(PreMS.LazySeries.apply $s $ms) => simpWith q(apply_destruct $s $ms)
    | ~q(PreMS.inv $arg) => simpWith q(inv_destruct $arg)
    | ~q(PreMS.pow $arg $exp) => simpWith q(pow_destruct $arg $exp)
    | _ => return .continue
  | _ => return .continue

-- TODO: rewrite without macro
syntax "elim_destruct" : tactic
macro_rules
| `(tactic| elim_destruct) =>
    `(tactic|
      repeat (
        norm_num1;
        first | simp only [elimDestruct, PreMS_const] | simp only [↓reduceIte, PreMS_const]
      ) <;> norm_num1
    )

end ElimDestruct

end TendstoTactic

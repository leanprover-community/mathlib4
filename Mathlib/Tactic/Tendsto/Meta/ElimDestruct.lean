/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
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
theorem mulConst_const (x : PreMS []) (c : ℝ) : (PreMS.mulConst x c) = x * c := rfl

@[PreMS_const]
theorem inv_const (x : PreMS []) : (PreMS.inv x) = x⁻¹ := rfl

@[PreMS_const]
theorem pow_const (x : PreMS []) (a : ℝ) : (PreMS.pow x a) = x^a := rfl

@[PreMS_const]
theorem extendBasisEnd_const (f : ℝ → ℝ) (x : PreMS []) : (PreMS.extendBasisEnd f x) =
    PreMS.const [f] x := rfl

@[PreMS_const]
theorem updateBasis_const (ms : PreMS []) (ex : BasisExtension []) :
    (PreMS.updateBasis ex ms) = PreMS.const _ ms := by
  cases ex with
  | nil =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
  | insert f ex_tl =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
    rw [updateBasis_const]

@[PreMS_const]
theorem updateBasis_const_real (ms : ℝ) (ex : BasisExtension []) :
    (PreMS.updateBasis ex ms) = PreMS.const _ ms := by
  cases ex with
  | nil =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
  | insert f ex_tl =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
    rw [updateBasis_const]

@[PreMS_const]
theorem BasisExtension.nil_getBasis : BasisExtension.nil.getBasis = [] := rfl

@[PreMS_const]
theorem log_const (x : PreMS []) (logBasis : LogBasis []) : (PreMS.log logBasis x) =
    Real.log x := rfl

@[PreMS_const]
theorem exp_const (x : PreMS []) : (PreMS.exp x) = Real.exp x := rfl

end Const

section Destruct

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

theorem const_destruct (c : ℝ) : destruct (PreMS.const (basis_hd :: basis_tl) c) =
    .some ((0, PreMS.const basis_tl c), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem one_destruct : destruct (PreMS.one (basis_hd :: basis_tl)) =
    .some ((0, PreMS.one basis_tl), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem monomial_rpow_zero_destruct (r : ℝ) :
     destruct (PreMS.monomial_rpow (basis_hd :: basis_tl) 0 r) =
    .some ((r, PreMS.one _), @PreMS.nil basis_hd basis_tl) := by
  rfl

theorem monomial_rpow_succ_destruct (m : ℕ) (r : ℝ) :
    destruct (PreMS.monomial_rpow (basis_hd :: basis_tl) (m + 1) r) =
    .some ((0, PreMS.monomial_rpow basis_tl m r), @PreMS.nil basis_hd basis_tl) := by
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

theorem mulConst_destruct (x : PreMS (basis_hd :: basis_tl)) (c : ℝ) : destruct (x.mulConst c) =
    match destruct x with
    | none => none
    | some ((exp, coef), tl) => .some ((exp, coef.mulConst c),
      (PreMS.mulConst (basis := basis_hd :: basis_tl) tl c)) := by
  cases x <;> simp

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

theorem log_destruct (ms : PreMS (basis_hd :: basis_tl))
    (logBasis : LogBasis (basis_hd :: basis_tl)) : destruct (ms.log logBasis) =
    match destruct ms with
    | none => none
    | some ((exp, coef), tl) =>
      match basis_tl with
      | [] => destruct (PreMS.add (basis := [basis_hd]) (PreMS.const _ (Real.log coef)) <|
          PreMS.logSeries.apply (PreMS.mulConst (basis := [basis_hd]) tl coef⁻¹))
      | List.cons basis_tl_hd basis_tl_tl =>
        let logC := PreMS.log logBasis.tail coef
        match logBasis with
        | .cons _ _ _ _ log_hd =>
          destruct (PreMS.add (basis := basis_hd :: basis_tl_hd :: basis_tl_tl)
            ((.cons (0, logC.add <| log_hd.mulConst exp) .nil)) <|
            PreMS.logSeries.apply (PreMS.mulMonomial tl coef.inv (-exp))) := by
  cases' ms with exp coef tl
  · simp [PreMS.log]
  cases' basis_tl with basis_tl_hd basis_tl_tl
  · simp [PreMS.log]
  cases' logBasis with _ _ _ _ log_hd
  conv => lhs; unfold PreMS.log; simp
  rfl

theorem exp_destruct (ms : PreMS (basis_hd :: basis_tl)) : destruct ms.exp =
    match destruct ms with
    | .none => .some ((0, PreMS.one basis_tl), @PreMS.nil basis_hd basis_tl)
    | .some ((exp, coef), tl) =>
      if exp < 0 then
        destruct (PreMS.expSeries.apply ms)
      else
        destruct ((PreMS.expSeries.apply tl).mulMonomial (basis_hd := basis_hd) coef.exp 0) := by
  cases' ms with exp coef tl
  · simp [PreMS.exp]
    rfl
  · simp [PreMS.exp]
    split_ifs with h_if <;> simp [h_if]

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

theorem logSeriesFrom_destruct (n : ℕ) :
    destruct (PreMS.logSeriesFrom n) = .some (-(-1)^n / n, PreMS.logSeriesFrom (n + 1)) := by
  rw [PreMS.logSeriesFrom_eq_cons]
  simp

theorem logSeries_destruct : destruct PreMS.logSeries = .some (0, PreMS.logSeriesFrom 1) := by
  simp [PreMS.logSeries, logSeriesFrom_destruct]

theorem expSeriesFrom_destruct (n : ℕ) : destruct (PreMS.expSeriesFrom n) =
    .some ((n.factorial : ℝ)⁻¹, PreMS.expSeriesFrom (n + 1)) := by
  rw [PreMS.expSeriesFrom_eq_cons]
  simp

theorem expSeries_destruct : destruct PreMS.expSeries = .some (1, PreMS.expSeriesFrom 1) := by
  simp [PreMS.expSeries, expSeriesFrom_destruct]

theorem extendBasisEnd_destruct (f : ℝ → ℝ) (ms : PreMS (basis_hd :: basis_tl)) :
    destruct (ms.extendBasisEnd f) =
    match destruct ms with
    | none => none
    | some ((exp, coef), tl) => some ((exp, coef.extendBasisEnd f),
        PreMS.extendBasisEnd (basis := basis_hd :: basis_tl) f tl) := by
  cases' ms <;> simp [PreMS.extendBasisEnd]

theorem updateBasis_keep_destruct (ms : PreMS (basis_hd :: basis_tl))
    (ex_tl : BasisExtension basis_tl) :
    destruct (ms.updateBasis (BasisExtension.keep basis_hd ex_tl)) =
    match destruct ms with
    | none => none
    | some ((exp, coef), tl) =>
      .some ((exp, PreMS.updateBasis ex_tl coef),
        PreMS.updateBasis (basis := basis_hd :: basis_tl)
          (BasisExtension.keep basis_hd ex_tl) tl) := by
  cases' ms with exp coef tl <;> simp [PreMS.updateBasis]

theorem updateBasis_insert_destruct (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ)
    (ex_tl : BasisExtension (basis_hd :: basis_tl)) :
    destruct (ms.updateBasis (BasisExtension.insert f ex_tl)) =
    .some ((0, PreMS.updateBasis ex_tl ms), PreMS.nil (basis_hd := basis_hd)) := by
  cases' ms with exp coef tl <;> simp [PreMS.updateBasis] <;> rfl

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
    | ~q(PreMS.logSeriesFrom $n) => simpWith q(logSeriesFrom_destruct $n)
    | ~q(PreMS.logSeries) => simpWith q(logSeries_destruct)
    | ~q(PreMS.expSeriesFrom $n) => simpWith q(expSeriesFrom_destruct $n)
    | ~q(PreMS.expSeries) => simpWith q(expSeries_destruct)
    | _ => return .continue
  | ~q(PreMS $basis) =>
    let basis' : Q(Basis) ← reduceBasis basis
    let _ : $basis =Q $basis' := ⟨⟩
    let ~q(List.cons $basis_hd $basis_tl) := basis' | return .continue
    match target.getAppFnArgs with
    | (``PreMS.extendBasisEnd, #[_, f, ms]) => -- crutch
      simpWith (← mkAppM ``extendBasisEnd_destruct #[f, ms])
    | (``PreMS.updateBasis, #[(oldBasis : Q(Basis)), (ex : Q(BasisExtension $oldBasis)),
        (ms : Q(PreMS $oldBasis))]) =>
      let oldBasis' : Q(Basis) ← reduceBasis oldBasis
      haveI : $oldBasis =Q $oldBasis' := ⟨⟩
      match oldBasis, ex with
      | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.keep _ $ex_tl) =>
        simpWith q(updateBasis_keep_destruct $ms $ex_tl)
      | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.insert $f $ex_tl) =>
        simpWith q(updateBasis_insert_destruct $ms $f $ex_tl)
    | _ =>
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
    | ~q(PreMS.one _) => simpWith q(@one_destruct $basis_hd $basis_tl)
    | ~q(PreMS.monomial_rpow _ $n $r) =>
      match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
      | 0 => simpWith q(@monomial_rpow_zero_destruct $basis_hd $basis_tl $r)
      | m + 1 => simpWith q(@monomial_rpow_succ_destruct $basis_hd $basis_tl $m $r)
    | ~q(PreMS.monomial _ $n) =>
      match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
      | 0 => simpWith q(@monomial_zero_destruct $basis_hd $basis_tl)
      | m + 1 => simpWith q(@monomial_succ_destruct $basis_hd $basis_tl $m)
    | ~q(PreMS.neg $arg) => simpWith q(neg_destruct $arg)
    | ~q(PreMS.add $arg1 $arg2) => simpWith q(add_destruct $arg1 $arg2)
    | ~q(PreMS.mul $arg1 $arg2) => simpWith q(mul_destruct $arg1 $arg2)
    | ~q(PreMS.mulMonomial $b $m_coef $m_exp) =>
      simpWith q(mulMonomial_destruct $b $m_coef $m_exp)
    | ~q(PreMS.mulConst $arg $c) => simpWith q(mulConst_destruct $arg $c)
    | ~q(PreMS.LazySeries.apply $s $ms) => simpWith q(apply_destruct $s $ms)
    | ~q(PreMS.inv $arg) => simpWith q(inv_destruct $arg)
    | ~q(PreMS.pow $arg $exp) => simpWith q(pow_destruct $arg $exp)
    | ~q(PreMS.log $logBasis $arg) => simpWith q(log_destruct $arg $logBasis)
    | ~q(PreMS.exp $arg) => simpWith q(exp_destruct $arg)
    | _ => return .continue
  | _ => return .continue

-- TODO: rewrite without macro?
syntax "elim_destruct" : tactic
macro_rules
| `(tactic| elim_destruct) =>
    `(tactic|
      repeat (
        norm_num1;
        first
        | simp only [elimDestruct, PreMS_const, LogBasis.tail]
        | simp only [↓reduceIte, PreMS_const]
        | simp only [LogBasis.insertLastLog, LogBasis.extendBasisEnd]
        | rewrite [updateBasis_const]
      ) <;> norm_num1
    )

end ElimDestruct

end TendstoTactic

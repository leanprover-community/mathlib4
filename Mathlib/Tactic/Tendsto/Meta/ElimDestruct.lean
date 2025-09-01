/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tendsto.Meta.Defs
import Mathlib.Tactic.Tendsto.Meta.ConstSimp
import Mathlib.Tactic.Tendsto.Meta.CompareReal

/-!
# TODO
-/

open Filter Asymptotics TendstoTactic Stream' Seq PreMS

namespace TendstoTactic

namespace ElimDestruct

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
    split_ifs with h_if <;> rfl

theorem cos_destruct (ms : PreMS (basis_hd :: basis_tl)) : destruct ms.cos =
    match destruct ms with
    | .none => .some ((0, PreMS.one basis_tl), @PreMS.nil basis_hd basis_tl)
    | .some ((exp, coef), tl) =>
      if exp < 0 then
        destruct (PreMS.cosSeries.apply ms)
      else
        destruct (
          PreMS.sub
          ((PreMS.cosSeries.apply tl).mulMonomial (basis_hd := basis_hd) coef.cos 0)
          ((PreMS.sinSeries.apply tl).mulMonomial (basis_hd := basis_hd) coef.sin 0)
        ) := by
  cases' ms with exp coef tl
  · simp [PreMS.cos]
    rfl
  · simp [PreMS.cos]
    split_ifs with h_if <;> rfl

theorem sin_destruct (ms : PreMS (basis_hd :: basis_tl)) : destruct ms.sin =
    match destruct ms with
    | .none => .none
    | .some ((exp, coef), tl) =>
      if exp < 0 then
        destruct (PreMS.sinSeries.apply ms)
      else
        destruct (
          PreMS.add
          ((PreMS.cosSeries.apply tl).mulMonomial (basis_hd := basis_hd) coef.sin 0)
          ((PreMS.sinSeries.apply tl).mulMonomial (basis_hd := basis_hd) coef.cos 0)
        ) := by
  cases' ms with exp coef tl
  · simp [PreMS.sin]
  · simp [PreMS.sin]
    split_ifs with h_if <;> rfl

theorem ofFnFrom_destruct (f : ℕ → ℝ) (n : ℕ) : destruct (PreMS.LazySeries.ofFnFrom f n) =
    .some ((f n), PreMS.LazySeries.ofFnFrom f (n + 1)) := by
  rw [PreMS.LazySeries.ofFnFrom_eq_cons, Seq.destruct_cons]

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

theorem logSeries_destruct : destruct PreMS.logSeries =
    .some (0, PreMS.LazySeries.ofFnFrom (fun n ↦ -(-1) ^ n / n) 1) := by
  simp [PreMS.logSeries, PreMS.LazySeries.ofFn]
  rw [PreMS.LazySeries.ofFnFrom_eq_cons, Seq.destruct_cons]
  congr
  simp

theorem expSeries_destruct : destruct PreMS.expSeries =
    .some (1, PreMS.LazySeries.ofFnFrom (fun n ↦ (↑n.factorial)⁻¹) 1) := by
  simp [PreMS.expSeries, PreMS.LazySeries.ofFn]
  rw [PreMS.LazySeries.ofFnFrom_eq_cons, Seq.destruct_cons]
  congr
  simp

theorem cosSeries_destruct : destruct PreMS.cosSeries =
    .some (1, PreMS.LazySeries.ofFnFrom (fun n ↦ if n % 2 = 0 then (-1 : ℝ) ^ (n / 2) * (n.factorial : ℝ)⁻¹ else 0) 1) := by
  simp [PreMS.cosSeries, PreMS.LazySeries.ofFn]
  rw [PreMS.LazySeries.ofFnFrom_eq_cons, Seq.destruct_cons]
  congr
  simp

theorem sinSeries_destruct : destruct PreMS.sinSeries =
    .some (0, PreMS.LazySeries.ofFnFrom (fun n ↦ if n % 2 = 1 then (-1) ^ ((n - 1) / 2) * (n.factorial : ℝ)⁻¹ else 0) 1) := by
  simp [PreMS.sinSeries, PreMS.LazySeries.ofFn]
  rw [PreMS.LazySeries.ofFnFrom_eq_cons, Seq.destruct_cons]
  rfl

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
    | ~q(PreMS.LazySeries.ofFnFrom $f $n) => simpWith q(ofFnFrom_destruct $f $n)
    | ~q(PreMS.invSeries) => simpWith q(invSeries_destruct)
    | ~q(PreMS.powSeriesFrom $x $acc $n) => simpWith q(powSeriesFrom_destruct $x $acc $n)
    | ~q(PreMS.powSeries $x) => simpWith q(powSeries_destruct $x)
    | ~q(PreMS.logSeries) => simpWith q(logSeries_destruct)
    | ~q(PreMS.expSeries) => simpWith q(expSeries_destruct)
    | ~q(PreMS.cosSeries) => simpWith q(cosSeries_destruct)
    | ~q(PreMS.sinSeries) => simpWith q(sinSeries_destruct)
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
    | ~q(PreMS.cos $arg) => simpWith q(cos_destruct $arg)
    | ~q(PreMS.sin $arg) => simpWith q(sin_destruct $arg)
    | _ => return .continue
  | _ => return .continue

-- #check Nat

#check reduceIte

-- simproc ↓ reduceNumIte (ite _ _ _) := fun e => do
--   let_expr f@ite α c i tb eb ← e | return .continue
--   let g_true :=  ← mkFreshExprMVar c
--   let res ← evalTacticAt (← `(tactic| compare_real)) e.mvarId!
--   if res.isEmpty then

--   let r ← Mathlib.Meta.NormNum.deriveSimp c
--   if r.expr.isTrue then
--     let pr    := mkApp (mkApp5 (mkConst ``ite_cond_eq_true f.constLevels!) α c i tb eb)
--       (← r.getProof)
--     return .visit { expr := tb, proof? := pr }
--   if r.expr.isFalse then
--     let pr    := mkApp (mkApp5 (mkConst ``ite_cond_eq_false f.constLevels!) α c i tb eb)
--       (← r.getProof)
--     return .visit { expr := eb, proof? := pr }
--   return .continue

universe u in
lemma ite_cond_eq_true' {α : Type u} (P : Prop) [Decidable P] (rhs tb eb : α) (hc : P)
    (h : tb = rhs) :
    ite P tb eb = rhs := by
  simp [hc, h]

universe u in
lemma ite_cond_eq_false' {α : Type u} (P : Prop) [Decidable P] (rhs tb eb : α) (hc : ¬ P)
    (h : eb = rhs) :
    ite P tb eb = rhs := by
  simp [hc, h]

-- TODO: rewrite this hack
elab "reduce_num_ite" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← getMainGoal
  let e ← getMainTarget
  let_expr Eq _ lhs rhs := e |
    -- dbg_trace f!"not an equality goal: {← ppExpr e}"
    throwError "not an equality goal"
  let_expr ite α c i tb eb := lhs |
    -- dbg_trace f!"not an ite lhs: {lhs}"
    throwError "not an ite lhs"
  -- dbg_trace ← ppExpr c
  let g_true ← mkFreshExprMVar c
  let res ← evalTacticAt (← `(tactic| compare_real)) g_true.mvarId!
  if res.isEmpty then
    let g_new ← mkFreshExprMVar (← mkAppM ``Eq #[tb, rhs])
    g.assign (← mkAppM ``ite_cond_eq_true' #[c, rhs, tb, eb, g_true, g_new])
    replaceMainGoal [g_new.mvarId!]
    return
  let g_false ← mkFreshExprMVar (← mkAppM ``Not #[c])
  let res ← evalTacticAt (← `(tactic| compare_real)) g_false.mvarId!
  if res.isEmpty then
    let g_new ← mkFreshExprMVar (← mkAppM ``Eq #[eb, rhs])
    g.assign (← mkAppM ``ite_cond_eq_false' #[c, rhs, tb, eb, g_false, g_new])
    replaceMainGoal [g_new.mvarId!]
    return
  throwError "reduce_num_ite can't neither prove the condition nor disprove it"

open Real in
example (p b : ℝ) (hb1 : 0 < b) (hb2 : b < 1) :
  let ε : ℝ := 1;
  let f := fun (x : ℝ) ↦
    (1 - 1 / (b * (log x)^(1 + ε)))^p *
    (1 + 1 / log (b * x + x / (log x)^(1 + ε))^(ε / 2)) -
    (1 + 1 / (log x)^(ε / 2));
    (if 0 * p + -2 + 0 + 0 < 0 * p + 0 + 0 + -(1 / 2) then 4 else 2) = 2 := by
  intro ε f
  -- reduce_num_ite

  have : (if 0 < 0 * p + 0 + 0 then 4 else 2) = ?_ := by
    reduce_num_ite
    exact Eq.refl _
  admit

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
        | reduce_num_ite
      ) <;>
      norm_num1
    )

end ElimDestruct

end TendstoTactic

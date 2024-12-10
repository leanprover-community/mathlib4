import Mathlib.Tactic.Tendsto.Multiseries.Main
import Mathlib.Tactic.Tendsto.Meta.Trimming
import Mathlib.Tactic.Tendsto.Meta.LeadingTerm

set_option linter.style.longLine false

open Filter Asymptotics TendstoTactic Stream'.Seq ElimDestruct

open Lean Elab Meta Tactic Qq

namespace TendstoTactic

def basis_wo : WellOrderedBasis [fun (x : ℝ) ↦ x] := by
  simp [WellOrderedBasis]
  exact fun ⦃U⦄ a ↦ a

partial def createMS (body : Expr) : TacticM MS := do
  let basis : Q(List (ℝ → ℝ)) := q([fun (x : ℝ) ↦ x])
  let basis_wo : Q(WellOrderedBasis $basis) := q(basis_wo)
  let zero_aux : Q(0 < List.length $basis) := q(by decide)
  match body.nat? with -- TODO: other numerals
  | .some n =>
    return MS.const basis body basis_wo
  | none =>
  if body.isBVar then
    if body.bvarIdx! != 0 then
      throwError "Unexpected bvarIdx in createMS: expected 0"
    let ms : MS := MS.monomial basis 0 zero_aux basis_wo
    return ms
  match body.getAppFnArgs with
  | (``Neg.neg, #[_, _, arg]) => return MS.neg (← createMS arg)
  | (``HAdd.hAdd, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMS arg1
    let ms2 ← createMS arg2
    -- if h_basis_eq : ms1.basis =Q ms2.basis then
    return MS.add ms1 ms2 ⟨⟩
  | (``HSub.hSub, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMS arg1
    let ms2 ← createMS arg2
    -- if h_basis_eq : ms1.basis =Q ms2.basis then
    return MS.sub ms1 ms2 ⟨⟩
  | (``HMul.hMul, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMS arg1
    let ms2 ← createMS arg2
    -- if h_basis_eq : ms1.basis =Q ms2.basis then
    return MS.mul ms1 ms2 ⟨⟩
  | (``Inv.inv, #[_, _, arg]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMS arg)
    return MS.inv ms h_trimmed
  | (``HDiv.hDiv, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMS arg1
    let ⟨ms2, h_trimmed⟩ ← trimMS (← createMS arg2)
    -- if h_basis_eq : ms1.basis =Q ms2.basis then
    return MS.div ms1 ms2 h_trimmed ⟨⟩
  | _ => throwError f!"Unsupported body in createMS: {body}"


def computeTendsto (f : Q(ℝ → ℝ)) : TacticM ((limit : Q(Filter ℝ)) × Q(Tendsto $f atTop $limit)) := do
  match f with
  | .lam _ _ b _ =>
    let ms ← createMS b
    let ⟨ms_trimmed, h_trimmed⟩ ← trimPartialMS ms

    let hf_eq ← mkFreshExprMVarQ q($ms.F = $f)
    hf_eq.mvarId!.applyRfl

    let ~q(List.cons $basis_hd $basis_tl) := ms_trimmed.basis | throwError "Unexpected basis in computeTendsto"
    -- I don't how to avoid Expr here.
    let h_tendsto : Expr ← match ms_trimmed.val with
    | ~q(PreMS.nil) =>
      pure (q(PreMS.nil_tendsto_zero $ms_trimmed.h_approx) : Expr)
    | ~q(PreMS.cons $hd $tl) =>
      let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms_trimmed.val
      let ~q(⟨$coef, $exps⟩) := leading | throwError "Unexpected leading in computeTendsto"
      let h_tendsto ← match ← getFirstIs exps with
      | .pos h_exps =>
        match ← compareReal coef with
        | .neg h_coef =>
          pure (q(PreMS.tendsto_bot_of_FirstIsPos $ms_trimmed.h_wo $ms_trimmed.h_approx $h_trimmed.get! $ms_trimmed.h_basis $h_leading_eq $h_exps $h_coef) : Expr)
        | .pos h_coef =>
          pure (q(PreMS.tendsto_top_of_FirstIsPos $ms_trimmed.h_wo $ms_trimmed.h_approx $h_trimmed.get! $ms_trimmed.h_basis $h_leading_eq $h_exps $h_coef) : Expr)
        | .zero _ => throwError "Unexpected zero coef with FirstIsPos"
      | .neg h_exps =>
        pure (q(PreMS.tendsto_zero_of_FirstIsNeg $ms_trimmed.h_wo $ms_trimmed.h_approx $h_leading_eq $h_exps) : Expr)
      | .zero h_exps =>
        pure (q(PreMS.tendsto_const_of_AllZero $ms_trimmed.h_wo $ms_trimmed.h_approx $h_trimmed.get! $ms_trimmed.h_basis $h_leading_eq $h_exps) : Expr)
    | _ => throwError "Unexpected result of trimMS"

    let ⟨0, t, h_tendsto⟩ ← inferTypeQ h_tendsto | throwError "Unexpected h_tendsto's universe level"
    let ~q(@Tendsto ℝ ℝ $g atTop $limit) := t | throwError "Unexpected h_tendsto's type"
    haveI' : $g =Q $ms.F := ⟨⟩

    let res := q(Eq.subst (motive := fun x ↦ Tendsto x atTop $limit) $hf_eq $h_tendsto)
    return ⟨limit, res⟩
  | _ => throwError "Function should be lambda"

elab "compute_asymptotics" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let target : Q(Prop) ← getMainTarget
    let ~q(@Filter.Tendsto ℝ ℝ $f atTop $targetLimit) := target | throwError "The goal must me in the form Tendsto (fun x ↦ ...) atTop ..."
    let ⟨1, fType, f⟩ ← inferTypeQ f | throwError "Unexpected universe level of function in compute_asymptotics"
    let ~q(ℝ → ℝ) := fType | throwError "Only real functions are supported"
    let ⟨limit, h_tendsto⟩ ← computeTendsto f
    let result : Q(Prop) ← inferType h_tendsto
    if !(← isDefEq target result) then
      match targetLimit, limit with
      | ~q(nhds $a), ~q(nhds $b) =>
        let h_eq : Q($b = $a) ← mkFreshExprMVarQ q($b = $a)
        (← getMainGoal).assign q(Eq.subst (motive := fun x ↦ Filter.Tendsto $f atTop (nhds (X := ℝ) x)) $h_eq $h_tendsto)
        setGoals (← evalTacticAt (← `(tactic| try norm_num1)) h_eq.mvarId!)
      | _ =>
        throwError m!"I've proved that {← ppExpr (← inferType h_tendsto)}. Is this what you expect?"
    else
      (← getMainGoal).assign h_tendsto

end TendstoTactic

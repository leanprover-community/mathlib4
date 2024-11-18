import Mathlib.Tactic.Tendsto.Multiseries.Main
import Mathlib.Tactic.Tendsto.Meta.Trimming
import Mathlib.Tactic.Tendsto.Meta.LeadingTerm

set_option linter.style.longLine false

open Filter Asymptotics TendstoTactic Stream' Seq

open Lean Elab Meta Tactic Qq

lemma PreMS.nil_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {F : ℝ → ℝ}
    (h : PreMS.Approximates (@PreMS.nil basis_hd basis_tl) F) : Tendsto F atTop (nhds 0) := by
  apply PreMS.Approximates_nil at h
  exact h.tendsto

def basis_wo : MS.WellOrderedBasis [fun (x : ℝ) ↦ x] := by
  simp [MS.WellOrderedBasis]
  exact fun ⦃U⦄ a ↦ a

partial def createMS (body : Expr) : MetaM MS := do
  let basis : Q(List (ℝ → ℝ)) := q([fun (x : ℝ) ↦ x])
  let basis_wo : Q(MS.WellOrderedBasis $basis) := q(basis_wo)
  let zero_aux : Q(0 < List.length $basis) := q(by decide)
  match body.nat? with
  | .some n =>
    return MS.const basis body basis_wo
  | none =>
  if body.isBVar then
    if body.bvarIdx! != 0 then
      throwError "strange bvarIdx"
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
  | _ => throwError f!"unsupported body : {body}"

elab "compute_asymptotics" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    match goalType.getAppFnArgs with
    | (``Filter.Tendsto, #[α, β, f, l₁, l₂]) =>
      if α != (mkConst ``Real) then
        throwError "Only real functions are supported"
      if β != (mkConst ``Real) then
        throwError "Only real functions are supported"
      -- dbg_trace f!"\n{l₁.getAppFn}"
      -- dbg_trace f!"\n{mkConst ``Filter.atTop}"
      -- if l₁.getAppFn != (mkConst ``Filter.atTop) then
      --   throwError "Only Filter.atTop limits are supported"
      -- dbg_trace f!"f := {f}"
      match f with
      | .lam _ _ b _ =>
        let ms ← createMS b
        let (ms_trimmed, h_trimmed) ← trimMS ms
        let h_trimmed : Q(PreMS.Trimmed $ms_trimmed.val) := h_trimmed
        let ms_fvar : FVarId ← liftMetaTacticAux fun mvarId => do
          let mvarIdNew ← mvarId.define `ms q(PreMS $ms.basis) ms_trimmed.val
          let (fvar, mvarIdNew) ← mvarIdNew.intro1P
          return (fvar, [mvarIdNew])

        let hf_eq_fvar ← Lean.Elab.Tactic.withMainContext do
          let f : Q(ℝ → ℝ) := f
          let hf_eq_target : Q(Prop) := q($f = $ms.F)
          let hf_eq_expr ← mkFreshExprMVar hf_eq_target
          hf_eq_expr.mvarId!.applyRfl

          return ← liftMetaTacticAux fun mvarId => do
            let mvarIdNew ← mvarId.assert `hf_eq hf_eq_target hf_eq_expr
            let (fvar, mvarIdNew) ← mvarIdNew.intro1P
            return (fvar, [mvarIdNew])

        -- rw [hf_eq]
        Lean.Elab.Tactic.withMainContext do
          let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
          let hf_eq_decl := ctx.get! hf_eq_fvar
          let r ← (← getMainGoal).rewrite (← getMainTarget) (hf_eq_decl.toExpr)
          let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
          replaceMainGoal (mvarId' :: r.mvarIds)

        -- clear hf_eq
        let g ← getMainGoal
        replaceMainGoal [← g.clear hf_eq_fvar]

        match ms_trimmed.basis with
        | ~q(List.cons $basis_hd $basis_tl) =>
          match ms_trimmed.val with
          | ~q(PreMS.nil) =>
            let h_tendsto : Expr := ← mkAppM ``PreMS.nil_tendsto_zero #[ms_trimmed.h_approx]
            (← getMainGoal).assign h_tendsto
            return
          | ~q(PreMS.cons $hd $tl) =>
            let (leading, h_leading_eq) ← getLeadingTermWithProof ms_trimmed.val
            let h_leading_eq_fvar : FVarId ← liftMetaTacticAux fun mvarId => do
              let mvarIdNew ← mvarId.assert `h_leading q(PreMS.leadingTerm $ms_trimmed.val = $leading) h_leading_eq
              let (fvar, mvarIdNew) ← mvarIdNew.intro1P
              return (fvar, [mvarIdNew])

            let h_tendsto ← Lean.Elab.Tactic.withMainContext do
              let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
              let h_leading_eq_decl := ctx.get! h_leading_eq_fvar
              let h_leading_eq_expr := h_leading_eq_decl.toExpr
              match leading with
              | ~q(MS.Term.mk $coef $exps) =>
                let coef_comp ← compareReal coef
                match coef_comp with
                | .zero h_coef =>
                  return ← mkAppM ``PreMS.tendsto_zero_of_zero_coef #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_coef]
                | .neg h_coef =>
                  match ← getFirstIs exps with
                  | .pos h_exps =>
                    return ← mkAppM ``PreMS.tendsto_bot_of_FirstIsPos #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_exps, h_coef]
                  | .neg h_exps =>
                    return ← mkAppM ``PreMS.tendsto_zero_of_FirstIsNeg #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_exps]
                  | .zero h_exps =>
                    return ← mkAppM ``PreMS.tendsto_const_of_AllZero #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_exps]
                | .pos h_coef =>
                  match ← getFirstIs exps with
                  | .pos h_exps =>
                    return ← mkAppM ``PreMS.tendsto_top_of_FirstIsPos #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_exps, h_coef]
                  | .neg h_exps =>
                    return ← mkAppM ``PreMS.tendsto_zero_of_FirstIsNeg #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_exps]
                  | .zero h_exps =>
                    return ← mkAppM ``PreMS.tendsto_const_of_AllZero #[ms_trimmed.h_wo, ms_trimmed.h_approx, h_trimmed, ms_trimmed.h_basis, h_leading_eq_expr, h_exps]
              | _ => throwError "strange leading"
            (← getMainGoal).assign h_tendsto

            -- let kek_fvar : FVarId ← liftMetaTacticAux fun mvarId => do
            --   let mvarIdNew ← mvarId.assert `h_tendsto (← inferType h_tendsto) h_tendsto
            --   let (fvar, mvarIdNew) ← mvarIdNew.intro1P
            --   return (fvar, [mvarIdNew])

          | _ => throwError "strange ms"
        | _ => throwError "strange basis"
      | _ => throwError "function should be lambda"
    | _ =>
      dbg_trace f!"no"

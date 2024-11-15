import Mathlib.Tactic.Tendsto.Main
import Mathlib.Tactic.Tendsto.LazyComp.Extract

open Filter Asymptotics TendstoTactic Stream' Seq

open Lean Elab Meta Tactic Qq


partial def createMsWithBasis (body : Expr) : MetaM (Expr × Expr × Expr) := do
  let basis : Q(List (ℝ → ℝ)) := q([fun (x : ℝ) ↦ x])
  let basis_wo : Q(MS.WellOrderedBasis $basis) := ← mkSorry q(MS.WellOrderedBasis $basis) true
  let zero_aux : Q(0 < List.length $basis) := ← mkSorry q(0 < List.length $basis) true
  if body.isBVar then
    if body.bvarIdx! != 0 then
      throwError "strange bvarIdx"
    let ms_expr := mkApp4 (mkConst ``MS.monomial) basis (mkNatLit 0) zero_aux basis_wo
    return (ms_expr, basis, basis_wo)
  match body.getAppFnArgs with
  | (``Neg.neg, #[_, _, arg]) =>
    let ms_expr := mkApp (mkConst ``MS.neg) (← createMsWithBasis arg).1
    return (ms_expr, basis, basis_wo)
  | _ => throwError f!"unsupported body {body}"

elab "compute_asymptotics" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"
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
      dbg_trace f!"f := {f}"
      match f with
      | .lam _ _ b _ =>
        dbg_trace b
        let (ms_expr, basis, h_basis_wo) ← createMsWithBasis b
        let kek ← extractMS basis (mkApp (mkConst ``MS.val) ms_expr)
        -- let (ms_trimmed, h_trimmed) ← trimMS ms_expr
        let ms_fvar : FVarId ← liftMetaTacticAux fun mvarId => do
          let mvarIdNew ← mvarId.define `ms (mkConst ``MS) ms_expr
          let (fvar, mvarIdNew) ← mvarIdNew.intro1P
          return (fvar, [mvarIdNew])

        -- let h_trimmed_fvar : FVarId ← Lean.Elab.Tactic.withMainContext do
        --   let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
        --   let ms_decl := ctx.get! ms_fvar
        --   let ms := ms_decl.toExpr -- Find the expression of the declaration.

        --   return ← liftMetaTacticAux fun mvarId => do
        --     let mvarIdNew ← mvarId.define `h_trimmed (mkApp (mkConst ``MS.Trimmed) ms) h_trimmed
        --     let (fvar, mvarIdNew) ← mvarIdNew.intro1P
        --     return (fvar, [mvarIdNew])

        let hf_eq_fvar ← Lean.Elab.Tactic.withMainContext do
          let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
          let ms_decl := ctx.get! ms_fvar
          let ms_expr := ms_decl.toExpr -- Find the expression of the declaration.

          let hf_eq_target ← mkAppOptM ``Eq #[.none, f, mkApp (mkConst ``MS.F) ms_expr]
          let hf_eq_expr ← mkFreshExprMVar hf_eq_target
          hf_eq_expr.mvarId!.applyRfl

          return ← liftMetaTacticAux fun mvarId => do
            let mvarIdNew ← mvarId.assert `hf_eq hf_eq_target (.mvar hf_eq_expr.mvarId!)
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
      | _ => throwError "function should be lambda"
    | _ =>
      dbg_trace f!"no"

section destruct_lemmas

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

-- theorem monomial_destruct {n : ℕ} (hn : n < (basis_hd)) : destruct (PreMS.monomial (basis_hd :: basis_tl) n) = sorry := by
--   unfold PreMS.monomial


theorem neg_head (ms : PreMS (basis_hd :: basis_tl)) : head ms.neg =
    match head ms with
    | none => none
    | some (exp, coef) => .some (exp, coef.neg) := by
  sorry

end destruct_lemmas

def b1 : ℝ → ℝ := id


example :
  let f := fun (y : ℝ) ↦ -y;
  Tendsto f atTop atBot := by
  simp
  compute_asymptotics

example :
  let f := -b1;
  Tendsto f atTop atBot := by
  extract_lets f
  -- Step 1. Syntactically create series
  let basis := [b1]
  have h_basis_wo : MS.WellOrderedBasis basis := by
    simp [MS.WellOrderedBasis, basis, b1]
    sorry
  let ms1 : MS := MS.monomial basis 0 (by simp [basis]) h_basis_wo
  let ms2 := ms1.neg
  -- Step 1 + eps. Find basis explicitly
  have h_basis : ms2.basis = ?_ := by
    reduce
    exact Eq.refl _
  -- Step 2. Prove the connection and reduce the problem to series
  have h_eq : ms2.F = f := by
    rfl
  rw [← h_eq]
  -- Step 3. Trim
  have h_trimmed : ms2.Trimmed := by sorry
  -- Step 4. Compute leading term
  have h_leading : ms2.leadingTerm = ?_ := by
    unfold MS.leadingTerm
    -- change ms2.basis with [fun a ↦ a] -- Not implemented
    conv =>
      lhs
      change @PreMS.leadingTerm [fun a ↦ a] (ms2.val : PreMS [fun a ↦ a])
    unfold PreMS.leadingTerm
    conv =>
      lhs; arg 3
      unfold ms2 -- unfold seires expression
      change head ms1.val.neg -- push .val to left
      -- apply destruct lemma
      rw [neg_head]
      arg 2
      -- at leaves:
      unfold ms1 MS.monomial
      dsimp only -- TODO
      dsimp [PreMS.monomial] -- TODO
      rw [Stream'.Seq.head_cons] -- TODO
      -- simp head
      arg 1; arg 2 -- TODO
      unfold PreMS.one PreMS.const -- TODO
    conv =>
      lhs; arg 3
      dsimp only
      -- simp head
      arg 1; arg 2
      unfold PreMS.neg PreMS.mulConst; norm_num
    conv =>
      lhs
      dsimp only
    have h_pre : (-1 : PreMS []).leadingTerm = ?_ := by
      -- recursively
      unfold PreMS.leadingTerm
      exact Eq.refl _
    rw [h_pre]
    dsimp only
    exact Eq.refl _
  -- Step 5. Find limit
  have h_limit : MS.Term.findLimit { coef := -1, exps := [1] } [fun a ↦ a] (by rfl) h_basis_wo = ?_ := by
    unfold MS.Term.findLimit
    dsimp only
    norm_num -- to solve all comparissons
    exact Eq.refl _
  -- Step 6. Reduce target to leadingTerm.toFun and finish using found limit
  rw [IsEquivalent.tendsto_atBot_iff (MS.IsEquivalent_leadingTerm ms2 h_basis_wo h_trimmed)]
  rw [h_leading]
  generalize_proofs _ p at h_limit
  exact p

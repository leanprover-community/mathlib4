/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ComputeAsymptotics.Lemmas
import Mathlib.Tactic.ComputeAsymptotics.Meta.Exp
import Mathlib.Tactic.ComputeAsymptotics.Meta.Log
import Mathlib.Tactic.ComputeAsymptotics.Meta.Trimming
import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareMS

/-!
# TODO
-/

open Filter Topology Asymptotics Stream'.Seq

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

theorem init_basis_wo : WellFormedBasis [fun (x : ℝ) ↦ x] :=
  WellFormedBasis.single _ (fun _ a ↦ a)

theorem monomial_rpow_Approximates_inv (basis : Basis) (ms : PreMS basis) (f : ℝ → ℝ)
    (h_approx : ms.Approximates (f ^ (-1 : ℝ))) :
    ms.Approximates (f⁻¹) := by
  convert h_approx
  ext t
  simp [Real.rpow_neg_one]

/-- Implemetation of `createMS` in `BasisM`. -/
partial def createMSImp (body : Expr) : BasisM MS := do
  if body.isBVar then
    if body.bvarIdx! != 0 then
      throwError "Unexpected bvarIdx in createMS: expected 0"
    return ← BasisM.monomial (← get).n_id
  match body.getAppFnArgs with
  | (``Neg.neg, #[_, _, arg]) => return MS.neg (← createMSImp arg)
  | (``HAdd.hAdd, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.add ms1' ms2
    else
      return MS.add ms1 ms2
  | (``HSub.hSub, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.sub ms1' ms2
    else
      return MS.sub ms1 ms2
  | (``HMul.hMul, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.mul ms1' ms2
    else
      return MS.mul ms1 ms2
  | (``Inv.inv, #[_, _, (arg : Q(ℝ))]) =>
    if arg.isBVar then
      if arg.bvarIdx! != 0 then
        throwError "Unexpected bvarIdx in createMS: expected 0"
      let res ← BasisM.monomial_rpow (← get).n_id q(-1)
      return {res with
        f := .lam .anonymous q(ℝ) q($arg⁻¹) .default
        h_approx := ← mkAppM ``monomial_rpow_Approximates_inv
          #[res.basis, res.val, q(id : ℝ → ℝ), res.h_approx]
      }
    else
      let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
      return MS.inv ms h_trimmed
  | (``HDiv.hDiv, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ⟨ms2, h_trimmed⟩ ← trimMS (← createMSImp arg2)
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.div ms1' ms2 h_trimmed
    else
      return MS.div ms1 ms2 h_trimmed
  | (``HPow.hPow, #[_, t, _, _, (arg : Q(ℝ)), exp]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
    if !exp.hasLooseBVars then
      if t == q(ℕ) then
        return MS.npow ms exp h_trimmed
      else if t == q(ℤ) then
        return MS.zpow ms exp h_trimmed
      else if t == q(ℝ) then
        let .some h_pos ← getLeadingTermCoefPos ms.val
          | throwError f!"Cannot prove that argument of rpow is eventually positive: {← ppExpr arg}"
        return MS.rpow ms exp h_trimmed h_pos
      else
        throwError f!"Unexpected type in pow: {← ppExpr t}. Only ℕ, ℤ and ℝ are supported."
    else
      if t == q(ℝ) then
        let .some h_pos ← getLeadingTermCoefPos ms.val
          | throwError f!"Cannot prove that argument of rpow is eventually positive: {← ppExpr arg}"
        let exp : Q(ℝ) := exp
        let res ← createMSImp q(Real.exp ((Real.log $arg) * $exp))
        return {res with
          f := .lam .anonymous q(ℝ) q($arg ^ $exp) .default
          h_approx := ← mkAppM ``PreMS.exp_Approximates_pow_of_pos #[ms.h_basis, ms.h_wo,
            ms.h_approx, h_trimmed, h_pos, res.h_approx]
        }
      else
        throwError
          f!"Unexpected type in pow: {← ppExpr t}. Only ℝ is supported for non-constant exponents"
  | (``Real.log, #[arg]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
    return ← createLogMS arg ms h_trimmed
  | (``Real.exp, #[arg]) =>
    let ⟨ms, h_trimmed?⟩ ← trimPartialMS (← createMSImp arg)
    return ← createExpMS ms h_trimmed?
  | (``Real.cos, #[arg]) =>
    let ⟨ms, _⟩ ← trimPartialMS (← createMSImp arg)
    let leading ← getLeadingTerm ms.val
    let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in createExpMS"
    let .wrong h_nonpos ← getFirstIsPos exps |
      throwError f!"Cannot prove that argument of cos is eventually bounded: {← ppExpr arg}"
    return MS.cos ms h_nonpos
  | (``Real.sin, #[arg]) =>
    let ⟨ms, _⟩ ← trimPartialMS (← createMSImp arg)
    let leading ← getLeadingTerm ms.val
    let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in createExpMS"
    let .wrong h_nonpos ← getFirstIsPos exps |
      throwError f!"Cannot prove that argument of sin is eventually bounded: {← ppExpr arg}"
    return MS.sin ms h_nonpos
  | _ =>
    if body.hasLooseBVars then
      throwError f!"Unsupported body in createMS: {body}"
    else
      return ← BasisM.const body

/-- Given a body of a function, returns the MS approximating it. -/
def createMS (body : Expr) : TacticM MS := do
  return (← (createMSImp body).run {
    basis := q([fun (x : ℝ) ↦ x])
    logBasis := q(LogBasis.single _)
    h_basis := q(init_basis_wo)
    h_logBasis := q(LogBasis.single_WellFormed _)
    n_id := q(⟨0, by simp⟩)
  }).fst

/-- Given a function `f`, returns the limit and the proof that `f` tends to it at `atTop`. -/
def computeTendsto (f : Q(ℝ → ℝ)) :
    TacticM ((limit : Q(Filter ℝ)) × Q(Tendsto $f atTop $limit)) := do
  match f with
  | .lam _ _ b _ =>
    let ms ← createMS b
    let ⟨ms_trimmed, h_trimmed?⟩ ← trimPartialMS ms
    let hf_eq ← mkFreshExprMVarQ q($ms.f = $f)
    hf_eq.mvarId!.applyRfl

    let ~q(List.cons $basis_hd $basis_tl) := ms_trimmed.basis
      | throwError "Unexpected basis in computeTendsto"
    -- I don't know how to avoid Expr here.
    let h_tendsto : Expr ← match ms_trimmed.val with
    | ~q(PreMS.nil) =>
      pure (q(PreMS.nil_tendsto_zero $ms_trimmed.h_approx) : Expr)
    | ~q(PreMS.cons $hd $tl) =>
      let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms_trimmed.val
      let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendsto"
      let h_tendsto ← match ← getFirstIs exps with
      | .pos h_exps =>
        match ← compareReal coef with
        | .neg h_coef =>
          pure (q(PreMS.tendsto_bot_of_FirstIsPos $ms_trimmed.h_wo $ms_trimmed.h_approx
            $h_trimmed?.get! $ms_trimmed.h_basis $h_leading_eq $h_exps $h_coef) : Expr)
        | .pos h_coef =>
          pure (q(PreMS.tendsto_top_of_FirstIsPos $ms_trimmed.h_wo $ms_trimmed.h_approx
            $h_trimmed?.get! $ms_trimmed.h_basis $h_leading_eq $h_exps $h_coef) : Expr)
        | .zero _ => panic! "Unexpected zero coef with FirstIsPos"
      | .neg h_exps =>
        pure (q(PreMS.tendsto_zero_of_FirstIsNeg $ms_trimmed.h_wo $ms_trimmed.h_approx
          $h_leading_eq $h_exps) : Expr)
      | .zero h_exps =>
        pure (q(PreMS.tendsto_const_of_AllZero $ms_trimmed.h_wo $ms_trimmed.h_approx
          $h_trimmed?.get! $ms_trimmed.h_basis $h_leading_eq $h_exps) : Expr)
    | _ => panic! "Unexpected result of trimMS"

    let ⟨0, t, h_tendsto⟩ ← inferTypeQ h_tendsto
      | panic! "Unexpected h_tendsto's universe level"
    let ~q(@Tendsto ℝ ℝ $g atTop $limit) := t | panic! "Unexpected h_tendsto's type"
    haveI' : $g =Q $ms.f := ⟨⟩
    -- let res := h_tendsto -- also works, decide later
    let res := q(Eq.subst (motive := fun x ↦ Tendsto x atTop $limit) $hf_eq $h_tendsto)
    return ⟨limit, res⟩
  | _ => throwError "Function should be lambda"

/-- Given a function `f` and a filter `source`, for which we would like to know
the limit at `source`,
returns the lemma name with the list of functions. One then need to find limits of these
functions and apply the lemma to the found proofs to get the proof for `f` at `source`. -/
def convertFilter (f : Q(ℝ → ℝ)) (source : Q(Filter ℝ)) :
    MetaM (Option Name × List (Q(ℝ → ℝ))) := do
  match source with
  | ~q(atTop) => return (.none, [f])
  | ~q(atBot) => return (.some ``tendsto_bot_of_tendsto_top, [q(fun x ↦ $f (-x))])
  | ~q(𝓝[>] $c) => return (.some ``tendsto_nhds_right_of_tendsto_top, [q(fun x ↦ $f ($c + x⁻¹))])
  | ~q(𝓝[<] $c) => return (.some ``tendsto_nhds_left_of_tendsto_top, [q(fun x ↦ $f ($c - x⁻¹))])
  | ~q(𝓝[≠] $c) => return (.some ``tendsto_nhds_punctured_of_tendsto_top,
    [q(fun x ↦ $f ($c - x⁻¹)), q(fun x ↦ $f ($c + x⁻¹))])
  | _ => throwError f!"Unexpected source filter: {← ppExpr source}"

/-- Computes limits of functions `ℝ → ℝ`. The goal must be in the form
`Tendsto (fun x ↦ body) source target`.
It works on wide class of function, that is constructed by arithmetic operations, powers, `exp` and
`log` operations. -/
elab "compute_asymptotics" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let target : Q(Prop) ← getMainTarget
    let ~q(@Filter.Tendsto ℝ ℝ $f $filter $targetLimit) := target
      | throwError "The goal must me in the form Tendsto (fun x ↦ ...) ... ..."
    let (convertLemma?, convertedFs) ← convertFilter f filter
    let proofs : List Expr ← convertedFs.mapM fun f => do
      let ⟨1, fType, f⟩ ← inferTypeQ f
        | throwError "Unexpected universe level of function in compute_asymptotics"
      let ~q(ℝ → ℝ) := fType | throwError "Only real functions are supported"
      let ⟨limit, h_tendsto⟩ ← computeTendsto f
      if !(← isDefEq limit targetLimit) then
        match targetLimit, limit with
        | ~q(𝓝 $a), ~q(𝓝 $b) =>
          let h_eq : Q($b = $a) ← mkFreshExprMVarQ q($b = $a)
          let extraGoals ← evalTacticAt
            (← `(tactic| norm_num)) h_eq.mvarId!
          if ← extraGoals.anyM (fun g ↦ do pure (← g.getType).isFalse) then
            throwError m!"The tactic proved that the function tends to {← ppExpr limit}, " ++
              m!"not {← ppExpr targetLimit}."
          appendGoals extraGoals
          pure q(Eq.subst
            (motive := fun x ↦ Filter.Tendsto $f atTop (𝓝 x)) $h_eq $h_tendsto)
        | _ =>
          throwError m!"The tactic proved that the function tends to {← ppExpr limit}, " ++
            m!"not {← ppExpr targetLimit}."
      else
        pure h_tendsto
    let pf ← match convertLemma? with
    | .none => pure proofs[0]!
    | .some convertLemma => do
      match filter with
      | ~q(𝓝[<] $c) =>
        pure <| ← mkAppM convertLemma (f :: c :: proofs).toArray
      | ~q(𝓝[>] $c) =>
        pure <| ← mkAppM convertLemma (f :: c :: proofs).toArray
      | ~q(𝓝[≠] $c) =>
        pure <| ← mkAppM convertLemma (f :: c :: proofs).toArray
      | _ =>
        pure <| ← mkAppM convertLemma (f :: proofs).toArray
    (← getMainGoal).assign pf

end ComputeAsymptotics

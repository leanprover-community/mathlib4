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

-- TODO: move
theorem Approximates_sqrt_of_pow {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_approx : ms.Approximates (f ^ (1 / 2 : ℝ))) :
    ms.Approximates (Real.sqrt ∘ f) := by
  convert h_approx
  ext t
  simp [Real.sqrt_eq_rpow]

/-- Implemetation of `createMS` in `BasisM`. -/
partial def createMSImp (x body : Q(ℝ)) : BasisM MS := do
  if body == x then
    return ← BasisM.monomial (← get).n_id
  match body.getAppFnArgs with
  | (``Neg.neg, #[_, _, arg]) => return MS.neg (← createMSImp x arg)
  | (``HAdd.hAdd, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp x arg1
    let ms2 ← createMSImp x arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.add ms1' ms2
    else
      return MS.add ms1 ms2
  | (``HSub.hSub, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp x arg1
    let ms2 ← createMSImp x arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.sub ms1' ms2
    else
      return MS.sub ms1 ms2
  | (``HMul.hMul, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp x arg1
    let ms2 ← createMSImp x arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.mul ms1' ms2
    else
      return MS.mul ms1 ms2
  | (``Inv.inv, #[_, _, (arg : Q(ℝ))]) =>
    if arg == x then
      let res ← BasisM.monomial_rpow (← get).n_id q(-1)
      return {res with
        f := ← mkLambdaFVars #[x] q($arg⁻¹)
        h_approx := ← mkAppM ``monomial_rpow_Approximates_inv
          #[res.basis, res.val, q(id : ℝ → ℝ), res.h_approx]
      }
    else
      let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp x arg)
      return MS.inv ms h_trimmed
  | (``HDiv.hDiv, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp x arg1
    let ⟨ms2, h_trimmed⟩ ← trimMS (← createMSImp x arg2)
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.div ms1' ms2 h_trimmed
    else
      return MS.div ms1 ms2 h_trimmed
  | (``HPow.hPow, #[_, t, _, _, (arg : Q(ℝ)), exp]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp x arg)
    if !exp.hasAnyFVar (fun fvarId ↦ fvarId == x.fvarId!) then
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
        let res ← createMSImp x q(Real.exp ((Real.log $arg) * $exp))
        return {res with
          f := ← mkLambdaFVars #[x] q($arg ^ $exp)
          h_approx := ← mkAppM ``PreMS.exp_Approximates_pow_of_pos #[ms.h_basis, ms.h_wo,
            ms.h_approx, h_trimmed, h_pos, res.h_approx]
        }
      else
        throwError
          f!"Unexpected type in pow: {← ppExpr t}. Only ℝ is supported for non-constant exponents"
  | (``Real.log, #[arg]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp x arg)
    return ← createLogMS arg ms h_trimmed
  | (``Real.exp, #[arg]) =>
    let ⟨ms, h_trimmed?⟩ ← trimPartialMS (← createMSImp x arg)
    return ← createExpMS ms h_trimmed?
  | (``Real.cos, _) =>
    throwError "Cosine is not supported (but will be soon)"
  | (``Real.sin, _) =>
    throwError "Sine is not supported (but will be soon)"
  | (``Real.sqrt, #[(arg : Q(ℝ))]) =>
    let res ← createMSImp x q($arg ^ (1 / 2 : ℝ))
    return {res with
      f := ← mkLambdaFVars #[x] q(Real.sqrt $arg)
      h_approx := ← mkAppM ``Approximates_sqrt_of_pow #[res.h_approx]
    }
  | _ =>
    if body.hasAnyFVar (fun fvarId ↦ fvarId == x.fvarId!) then
      throwError f!"Unsupported body in createMS: {body}"
    else
      return ← BasisM.const body

/-- Given a body of a function, returns the MS approximating it. -/
def createMS (x body : Q(ℝ)) : TacticM MS := do
  return (← (createMSImp x body).run {
    basis := q([fun (x : ℝ) ↦ x])
    logBasis := q(LogBasis.single _)
    h_basis := q(init_basis_wo)
    h_logBasis := q(LogBasis.single_WellFormed _)
    n_id := q(⟨0, by simp⟩)
  }).fst

/-- Given a function `f`, returns the limit and the proof that `f` tends to it at `atTop`. -/
def computeTendstoAtTop (f : Q(ℝ → ℝ)) :
    TacticM ((limit : Q(Filter ℝ)) × Q(Tendsto $f atTop $limit)) := do
  -- dbg_trace ← ppExpr f
  lambdaBoundedTelescope f 1 fun args body => do
    let #[x] := args | throwError ("Function must me in the form fun x ↦ ...\n" ++
      "Calling `eta_expand` before `compute asymptotics might help.")
    let ms ← createMS x body
    let ⟨ms_trimmed, h_trimmed?⟩ ← trimPartialMS ms
    let ~q(List.cons $basis_hd $basis_tl) := ms_trimmed.basis
      | panic! "Unexpected basis in computeTendstoAtTop"
    -- I don't know how to avoid Expr here.
    let h_tendsto : Expr ← match ms_trimmed.val with
    | ~q(PreMS.nil) =>
      pure (q(PreMS.nil_tendsto_zero $ms_trimmed.h_approx) : Expr)
    | ~q(PreMS.cons $hd $tl) =>
      let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms_trimmed.val
      let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendstoAtTop"
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
    let res := h_tendsto
    return ⟨limit, res⟩

/-- Given a function `f`, returns the limit and the proof that `f` tends to it at `source`. -/
def computeTendsto (f : Q(ℝ → ℝ)) (source : Q(Filter ℝ)) :
    TacticM ((limit : Q(Filter ℝ)) × Q(Filter.Tendsto $f $source $limit)) := do
  match source with
  | ~q(atTop) =>
    let ⟨limit, h_tendsto⟩ ← computeTendstoAtTop q($f)
    return ⟨q($limit), q($h_tendsto)⟩
  | ~q(atBot) =>
    let ⟨limit, h_tendsto⟩ ← computeTendstoAtTop q(fun x ↦ $f (-x))
    return ⟨q($limit), q(tendsto_bot_of_tendsto_top $f $h_tendsto)⟩
  | ~q(𝓝[<] $c) =>
    let ⟨limit, h_tendsto⟩ ← computeTendstoAtTop q(fun x ↦ $f ($c - x⁻¹))
    return ⟨q($limit), q(tendsto_nhds_left_of_tendsto_top $f $c $h_tendsto)⟩
  | ~q(𝓝[>] $c) =>
    let ⟨limit, h_tendsto⟩ ← computeTendstoAtTop q(fun x ↦ $f ($c + x⁻¹))
    return ⟨q($limit), q(tendsto_nhds_right_of_tendsto_top $f $c $h_tendsto)⟩
  | ~q(𝓝[≠] $c) =>
    let ⟨limit_left, h_tendsto_left⟩ ← computeTendstoAtTop q(fun x ↦ $f ($c - x⁻¹))
    let ⟨limit_right, h_tendsto_right⟩ ← computeTendstoAtTop q(fun x ↦ $f ($c + x⁻¹))
    if !(← isDefEq limit_left limit_right) then
      match limit_left, limit_right with
      | ~q(𝓝 $a), ~q(𝓝 $b) =>
        let h_eq : Q($a = $b) ← mkFreshExprMVarQ q($a = $b)
        let extraGoals ← evalTacticAt
          (← `(tactic| norm_num)) h_eq.mvarId!
        if ← extraGoals.anyM (fun g ↦ do pure (← g.getType).isFalse) then
          throwError m!"The tactic proved that the function {← ppExpr f} tends to " ++
            m!"{← ppExpr limit_left} from the left, and {← ppExpr limit_right} from the right, "
            ++ "and they are not equal."
        appendGoals extraGoals
        return ⟨q($limit_left), q(tendsto_nhds_punctured_of_tendsto_top_nhds_of_eq
          $f $c $h_tendsto_left $h_tendsto_right $h_eq)⟩
      | _ => panic! "function tends to different limits from left and right"
    else
      haveI : $limit_left =Q $limit_right := ⟨⟩
      return ⟨q($limit_left),
        q(tendsto_nhds_punctured_of_tendsto_top $f $c $h_tendsto_left $h_tendsto_right)⟩
  | _ => throwError f!"Unexpected source filter: {← ppExpr source}"

/-- Proves that `f` tends to `target` at `source`. -/
def proveTendsto (f : Q(ℝ → ℝ)) (source target : Q(Filter ℝ)) :
    TacticM Q(Filter.Tendsto $f $source $target) := do
  let ⟨limit, h_tendsto⟩ ← computeTendsto f source
  if !(← isDefEq limit target) then
    match target, limit with
    | ~q(𝓝 $a), ~q(𝓝 $b) =>
      let h_eq : Q($b = $a) ← mkFreshExprMVarQ q($b = $a)
      let extraGoals ← evalTacticAt
        (← `(tactic| norm_num)) h_eq.mvarId!
      if ← extraGoals.anyM (fun g ↦ do pure (← g.getType).isFalse) then
        throwError m!"The tactic proved that the function {← ppExpr f} tends " ++
          m!"to {← ppExpr limit}, not {← ppExpr target}."
      appendGoals extraGoals
      pure q(Eq.subst
        (motive := fun x ↦ Filter.Tendsto $f $source (𝓝 x)) $h_eq $h_tendsto)
    | _ =>
      throwError m!"The tactic proved that the function {← ppExpr f} tends to {← ppExpr limit}, " ++
        m!"not {← ppExpr target}."
  else
    pure h_tendsto

/-- Result type of `proveTendstoInf`. -/
inductive ProveTendstoInfResult (source : Q(Filter ℝ)) (f : Q(ℝ → ℝ))
| top (h : Q(Tendsto $f $source atTop))
| bot (h : Q(Tendsto $f $source atBot))

/-- Proves that `f` tends either to `atTop` or to `atBot` at `source`.
Panics if `f` tends to a finite limit. -/
def proveTendstoInf (source : Q(Filter ℝ)) (f : Q(ℝ → ℝ)) :
    TacticM (ProveTendstoInfResult source f) := do
  let ⟨limit, h_tendsto⟩ ← computeTendsto f source
  match limit with
  | ~q(atTop) => return .top q($h_tendsto)
  | ~q(atBot) => return .bot q($h_tendsto)
  | _ =>
    throwError f!"proveTendstoInf proved that the function {← ppExpr f} tends " ++
      f!"to finite limit: {← ppExpr limit}"

/-- Proves that `f` is little `o` of `g` at `source`. -/
def proveIsLittleO (source : Q(Filter ℝ)) (f g : Q(ℝ → ℝ)) : TacticM Q($f =o[$source] $g) := do
  match ← proveTendstoInf q($source) q(fun x ↦ $g x / $f x) with
  | .top h_tendsto => return q(isLittleO_of_tendsto_top $h_tendsto)
  | .bot h_tendsto => return q(isLittleO_of_tendsto_bot $h_tendsto)

/-- Proves that `f` is big `O` of `g` at `source`. -/
def proveIsBigO (source : Q(Filter ℝ)) (f g : Q(ℝ → ℝ)) : TacticM Q($f =O[$source] $g) := do
  let ⟨limit, h_tendsto⟩ ← computeTendsto q(fun x ↦ $g x / $f x) source
  match limit with
  | ~q(atTop) => return q(isBigO_of_tendsto_top $h_tendsto)
  | ~q(atBot) => return q(isBigO_of_tendsto_bot $h_tendsto)
  | ~q(𝓝 $c) =>
    let h_ne : Q($c ≠ 0) ← mkFreshExprMVarQ q($c ≠ 0)
    let extraGoals ← evalTacticAt
      (← `(tactic| norm_num)) h_ne.mvarId!
    appendGoals extraGoals
    return q(isBigO_of_tendsto_nhds $h_tendsto $h_ne)

/-- Proves that `f` is equivalent to `g` at `source`. -/
def proveIsEquivalent (source : Q(Filter ℝ)) (f g : Q(ℝ → ℝ)) : TacticM Q($f ~[$source] $g) := do
  let pf ← proveTendsto q(fun x ↦ $f x / $g x) source q(𝓝 1)
  return q(isEquivalent_of_tendsto_one $pf)

/-- Computes limits of functions `ℝ → ℝ`. It is able to close `Tendsto`, `IsLittleO`, `IsBigO` and
`IsEquivalent` goals.

It works on wide class of function, that is constructed by arithmetic operations, powers, `exp` and
`log` operations. -/
elab "compute_asymptotics" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← getMainGoal
    let target : Q(Prop) ← getMainTarget
    match target with
    | ~q(@Tendsto ℝ ℝ $f $source $target) =>
      goal.assign (← proveTendsto f source target)
    | ~q(@IsLittleO ℝ ℝ ℝ _ _ $source $f $g) =>
      goal.assign (← proveIsLittleO source f g)
    | ~q(@IsBigO ℝ ℝ ℝ _ _ $source $f $g) =>
      goal.assign (← proveIsBigO source f g)
    | ~q(@IsEquivalent ℝ ℝ _ $source $f $g) =>
      goal.assign (← proveIsEquivalent source f g)
    | _ =>
      throwError "unsupported goal"

elab (name := computeLimit)
    "compute_limit " f:(term) " at " source:(term) " with " name:(ident) : tactic => do
  focus do
  withMainContext do
    let f : Q(ℝ → ℝ) ← Term.elabTerm f q(ℝ → ℝ)
    let source : Q(Filter ℝ) ← Term.elabTerm source q(Filter ℝ)
    let ⟨limit, h_tendsto⟩ ← computeTendsto f source
    let goalNew ← (← getMainGoal).assert name.getId q(Tendsto $f $source $limit) h_tendsto
    let (_, goalNew) ← goalNew.intro1P
    replaceMainGoal [goalNew]

end ComputeAsymptotics

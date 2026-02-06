/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Lemmas
public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareMS
public import Mathlib.Tactic.ComputeAsymptotics.Meta.ConvertDomain
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Exp
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Log
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Trimming

/-!
# TODO
-/

public meta section

open Filter Topology Asymptotics

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

theorem init_basis_wo : WellFormedBasis [fun (x : ℝ) ↦ x] :=
  WellFormedBasis.single _ (fun _ a ↦ a)

theorem monomialRpow_toFun_eq_inv (basis : Basis) (n : Fin (List.length basis)) :
    (@MultiseriesExpansion.monomialRpow basis n (-1)).toFun =ᶠ[atTop] basis[n]⁻¹ := by
  apply EventuallyEq.of_eq
  ext
  simp [Real.rpow_neg_one]

/-- Implemetation of `createMS` in `BasisM`. -/
partial def createMSImp (x body : Q(ℝ)) : BasisM MS := do
  if !body.hasAnyFVar (fun fvarId ↦ fvarId == x.fvarId!) then
    return ← BasisM.const body
  if body == x then
    return ← BasisM.monomial (← get).n_id
  match body.getAppFnArgs with
  | (``id, #[_, arg]) => return ← createMSImp x arg
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
      let res ← BasisM.monomialRpow (← get).n_id q(-1)
      let f : Q(ℝ → ℝ) := ← mkLambdaFVars #[x] q($arg⁻¹)
      return ← res.replaceFun q($f) <|
        ← mkAppM ``monomialRpow_toFun_eq_inv #[res.basis, (← get).n_id]
    else
      let ⟨ms, _, h_trimmed⟩ ← trimMS (← createMSImp x arg)
      return MS.inv ms h_trimmed
  | (``HDiv.hDiv, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp x arg1
    let ⟨ms2, _, h_trimmed⟩ ← trimMS (← createMSImp x arg2)
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.div ms1' ms2 h_trimmed
    else
      return MS.div ms1 ms2 h_trimmed
  | (``HPow.hPow, #[_, t, _, _, (arg : Q(ℝ)), exp]) =>
    let ⟨ms, _, h_trimmed⟩ ← trimMS (← createMSImp x arg)
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
        let g : Q(ℝ → ℝ) ← mkLambdaFVars #[x] q($arg ^ $exp)
        let ~q($basis_hd :: $basis_tl) := res.basis | panic! "Unexpected basis in createMS pow"
        let ⟨_, h_msF⟩ ← Normalization.getFun q($ms.val)
        let ⟨_, h_resF⟩ ← Normalization.getFun q($res.val)
        let h : Q(($res.val).toFun =ᶠ[atTop] $g) := ← mkAppM ``MultiseriesExpansion.pow_eq_exp_toFun
          #[ms.h_basis, ms.h_wo, ms.h_approx, h_trimmed, h_pos, h_msF, h_resF]
        return ← res.replaceFun q($g) q($h)
      else
        throwError
          f!"Unexpected type in pow: {← ppExpr t}. Only ℝ is supported for non-constant exponents"
  | (``Real.log, #[arg]) =>
    let ⟨ms, _, h_trimmed⟩ ← trimMS (← createMSImp x arg)
    return ← createLogMS arg ms h_trimmed
  | (``Real.exp, #[arg]) =>
    let ⟨ms, _, h_trimmed?⟩ ← trimPartialMS (← createMSImp x arg)
    return ← createExpMS ms h_trimmed?
  | (``Real.cos, _) =>
    throwError "Cosine is not supported (but will be soon)"
  | (``Real.sin, _) =>
    throwError "Sine is not supported (but will be soon)"
  | (``Real.sqrt, #[(arg : Q(ℝ))]) =>
    let res ← createMSImp x q($arg ^ (1 / 2 : ℝ))
    let g : Q(ℝ → ℝ) ← mkLambdaFVars #[x] q(Real.sqrt $arg)
    let ⟨_, h_resF⟩ ← Normalization.getFun q($res.val)
    let h : Q(($res.val).toFun =ᶠ[atTop] $g) :=
      ← mkAppM ``MultiseriesExpansion.sqrt_of_pow_toFun #[h_resF]
    return ← res.replaceFun q($g) q($h)
  | _ => throwError f!"Unsupported body in createMS: {body}"

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
  lambdaBoundedTelescope f 1 fun args body => do
    let #[x] := args | throwError ("Function must me in the form fun x ↦ ...\n" ++
      "Calling `eta_expand` before `compute asymptotics might help.")
    let ms ← createMS x body
    let ⟨ms_trimmed, _, h_trimmed?⟩ ← trimPartialMS ms
    let ~q(List.cons $basis_hd $basis_tl) := ms_trimmed.basis
      | panic! "Unexpected basis in computeTendstoAtTop"
    -- I don't know how to avoid Expr here.
    let h_tendsto : Expr ← match ms_trimmed.val with
    | ~q(MultiseriesExpansion.mk .nil $f) =>
      pure (q(MultiseriesExpansion.nil_tendsto_zero $ms_trimmed.h_approx) : Expr)
    | ~q(MultiseriesExpansion.mk (.cons $exp $coef $tl) $f) =>
      let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms_trimmed.val
      let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendstoAtTop"
      let h_tendsto ← match ← getFirstIs exps with
      | .pos h_exps =>
        match ← compareReal q($coef) with
        | .neg h_coef =>
          pure q(MultiseriesExpansion.tendsto_bot_of_FirstIsPos (f := $f)
            $ms_trimmed.h_wo $ms_trimmed.h_approx $h_trimmed?.get! $ms_trimmed.h_basis
            $h_leading_eq $h_exps $h_coef rfl)
        | .pos h_coef =>
          pure q(MultiseriesExpansion.tendsto_top_of_FirstIsPos (f := $f)
            $ms_trimmed.h_wo $ms_trimmed.h_approx $h_trimmed?.get! $ms_trimmed.h_basis
            $h_leading_eq $h_exps $h_coef rfl)
        | .zero _ => panic! "Unexpected zero coef with FirstIsPos"
      | .neg h_exps =>
        pure q(MultiseriesExpansion.tendsto_zero_of_FirstIsNeg (f := $f) $ms_trimmed.h_wo
          $ms_trimmed.h_approx $h_leading_eq $h_exps rfl)
      | .zero h_exps =>
        pure (q(MultiseriesExpansion.tendsto_const_of_AllZero (f := $f) $ms_trimmed.h_wo
          $ms_trimmed.h_approx $h_trimmed?.get! $ms_trimmed.h_basis $h_leading_eq $h_exps rfl) :
            Expr)
    | _ => panic! "Unexpected result of trimMS"
    let ⟨0, t, h_tendsto⟩ ← inferTypeQ h_tendsto
      | panic! "Unexpected h_tendsto's universe level"
    let ~q(@Tendsto ℝ ℝ $g atTop $limit) := t | panic! "Unexpected h_tendsto's type"
    return ⟨limit, h_tendsto⟩

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

/-- Proves that `f : ℝ → ℝ` tends to `target` at `source`. -/
def proveTendstoReal (f : Q(ℝ → ℝ)) (source target : Q(Filter ℝ)) :
    TacticM Q(Filter.Tendsto $f $source $target) := do
  let ⟨limit, h_tendsto⟩ ← computeTendsto f source
  if !(← isDefEq limit target) then
    match target, limit with
    | ~q(𝓝 $a), ~q(𝓝 $b) =>
      let h_eq : Q($b = $a) ← mkFreshExprMVarQ q($b = $a)
      let extraGoals ← evalTacticAt (← `(tactic| norm_num)) h_eq.mvarId!
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

/-- Proves that `f : α → ℝ` tends to `target` at `source`. -/
partial def proveTendstoRealCodomain {α : Q(Type)} (f : Q($α → ℝ)) (source : Q(Filter $α))
    (target : Q(Filter ℝ)) :
    TacticM Q(Filter.Tendsto $f $source $target) := do
  match α with
  | ~q(ℝ) => proveTendstoReal q($f) q($source) q($target)
  | _ =>
    let ⟨cast, source', h_source, f', _⟩ ← ConvertDomain.convertFunDomain q($f) q($source)
    let pf ← proveTendstoRealCodomain q($f') q($source') q($target)
    return q(ConvertDomain.tendsto_cast_domain $f' $source $source' $target $cast $h_source $pf)

/-- Proves that `f : α → β` tends to `target` at `source`. -/
partial def proveTendsto {α β : Q(Type)} (f : Q($α → $β)) (source : Q(Filter $α))
    (target : Q(Filter $β)) :
    TacticM Q(Filter.Tendsto $f $source $target) := do
  -- TODO: Qq match against `β` doesn't work
  if ← isDefEq β q(ℝ) then
    haveI : $β =Q ℝ := ⟨⟩
    proveTendstoRealCodomain q($f) q($source) q($target)
  else
    let ⟨cast, target', h_convert⟩ ← ConvertDomain.convertTendstoTarget q($f) q($source) q($target)
    let f' : Q($α → ℝ) := q(fun x ↦ $cast ($f x))
    let h_goal ← mkFreshExprMVarQ q(Filter.Tendsto $f' $source $target')
    let [newGoal] ← evalTacticAt (← `(tactic| push_cast)) h_goal.mvarId!
      | panic! "proveTendsto: Unexpected number of goals after push_cast"
    let t : Q(Prop) ← inferType (.mvar newGoal)
    let ~q(@Filter.Tendsto.{0, 0} $α'' ℝ $f'' $source'' $target'') := t
      | panic! "proveTendsto: Unexpected newGoal type"
    newGoal.assign (← proveTendstoRealCodomain q($f'') q($source'') q($target''))
    return q($h_convert $h_goal)

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

/-- Proves that `f : ℝ → ℝ` is little-i of `g : ℝ → ℝ` at `source`. -/
def proveIsLittleOReal (source : Q(Filter ℝ)) (f g : Q(ℝ → ℝ)) : TacticM Q($f =o[$source] $g) := do
  match ← proveTendstoInf q($source) q(fun x ↦ $g x / $f x) with
  | .top h_tendsto => return q(isLittleO_of_tendsto_top $h_tendsto)
  | .bot h_tendsto => return q(isLittleO_of_tendsto_bot $h_tendsto)

/-- Proves that `f : α → ℝ` is little-o of `g : α → ℝ` at `source`. -/
partial def proveIsLittleORealCodomain {α : Q(Type)} (source : Q(Filter $α)) (f g : Q($α → ℝ)) :
    TacticM Q($f =o[$source] $g) := do
  match α with
  | ~q(ℝ) => return (← proveIsLittleOReal q($source) q($f) q($g))
  | _ =>
    let ⟨castf, source', h_source, f', _⟩ ← ConvertDomain.convertFunDomain q($f) q($source)
    let ⟨castg, _, _, g', _⟩ ← ConvertDomain.convertFunDomain q($g) q($source)
    haveI : $castf =Q $castg := ⟨⟩; do
    let pf ← proveIsLittleOReal q($source') q($f') q($g')
    return q(ConvertDomain.IsLittleO_cast_domain $f' $g' $source $source' $castg $pf $h_source)

/-- Proves that `f : α → β` is little-o of `g : α → γ` at `source`. -/
def proveIsLittleO {α β γ : Q(Type)} (source : Q(Filter $α)) (f : Q($α → $β)) (g : Q($α → $γ))
    (β_norm : Q(NormedAddCommGroup $β)) (γ_norm : Q(NormedAddCommGroup $γ)) :
    TacticM Q($f =o[$source] $g) := do
  let ⟨castf, h_castf⟩ ← ConvertDomain.getLawfulCodomainCast β β_norm
  let ⟨castg, h_castg⟩ ← ConvertDomain.getLawfulCodomainCast γ γ_norm
  let f' : Q($α → ℝ) := q(fun x ↦ $castf ($f x))
  let g' : Q($α → ℝ) := q(fun x ↦ $castg ($g x))
  let h_goal ← mkFreshExprMVarQ q($f' =o[$source] $g')
  let [newGoal] ← evalTacticAt (← `(tactic| push_cast)) h_goal.mvarId!
    | panic! "proveIsLittleO: Unexpected number of goals after push_cast"
  let t : Q(Prop) ← inferType (.mvar newGoal)
  let ~q(@IsLittleO.{0, 0, 0} $α'' ℝ ℝ _ _ $source'' $f'' $g'') := t
    | panic! "proveIsLittleO: Unexpected newGoal type"
  haveI : $α'' =Q $α := ⟨⟩; do
  newGoal.assign (← proveIsLittleORealCodomain q($source) q($f'') q($g''))
  assumeInstancesCommute
  return q(ConvertDomain.IsLittleO_cast_codomain $f $g $source $castf $castg
    $h_castf $h_castg $h_goal)

/-- Proves that `f : ℝ → ℝ` is big-o of `g : ℝ → ℝ` at `source`. -/
def proveIsBigOReal (source : Q(Filter ℝ)) (f g : Q(ℝ → ℝ)) : TacticM Q($f =O[$source] $g) := do
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

/-- Proves that `f : α → ℝ` is big-o of `g : α → ℝ` at `source`. -/
partial def proveIsBigORealCodomain {α : Q(Type)} (source : Q(Filter $α)) (f g : Q($α → ℝ)) :
    TacticM Q($f =O[$source] $g) := do
  match α with
  | ~q(ℝ) => return (← proveIsBigOReal q($source) q($f) q($g))
  | _ =>
    let ⟨castf, source', h_source, f', _⟩ ← ConvertDomain.convertFunDomain q($f) q($source)
    let ⟨castg, _, _, g', _⟩ ← ConvertDomain.convertFunDomain q($g) q($source)
    haveI : $castf =Q $castg := ⟨⟩; do
    let pf ← proveIsBigOReal q($source') q($f') q($g')
    return q(ConvertDomain.IsBigO_cast_domain $f' $g' $source $source' $castf $pf $h_source)

/-- Proves that `f : α → β` is big-o of `g : α → γ` at `source`. -/
partial def proveIsBigO {α β γ : Q(Type)} (source : Q(Filter $α)) (f : Q($α → $β)) (g : Q($α → $γ))
    (β_norm : Q(NormedAddCommGroup $β)) (γ_norm : Q(NormedAddCommGroup $γ)) :
    TacticM Q($f =O[$source] $g) := do
  let ⟨castf, h_castf⟩ ← ConvertDomain.getLawfulCodomainCast β β_norm
  let ⟨castg, h_castg⟩ ← ConvertDomain.getLawfulCodomainCast γ γ_norm
  let f' : Q($α → ℝ) := q(fun x ↦ $castf ($f x))
  let g' : Q($α → ℝ) := q(fun x ↦ $castg ($g x))
  let h_goal ← mkFreshExprMVarQ q($f' =O[$source] $g')
  let [newGoal] ← evalTacticAt (← `(tactic| push_cast)) h_goal.mvarId!
    | panic! "proveIsBigO: Unexpected number of goals after push_cast"
  let t : Q(Prop) ← inferType (.mvar newGoal)
  let ~q(@IsBigO.{0, 0, 0} $α'' ℝ ℝ _ _ $source'' $f'' $g'') := t
    | panic! "proveIsBigO: Unexpected newGoal type"
  haveI : $α'' =Q $α := ⟨⟩; do
  newGoal.assign (← proveIsBigORealCodomain q($source) q($f'') q($g''))
  assumeInstancesCommute
  return q(ConvertDomain.IsBigO_cast_codomain $f $g $source $castf $castg
    $h_castf $h_castg $h_goal)

/-- Proves that `f` is equivalent to `g` at `source`. -/
def proveIsEquivalentReal (source : Q(Filter ℝ)) (f g : Q(ℝ → ℝ)) :
    TacticM Q($f ~[$source] $g) := do
  let pf ← proveTendsto q(fun x ↦ $f x / $g x) source q(𝓝 1)
  return q(isEquivalent_of_tendsto_one $pf)

/-- Proves that `f : α → ℝ` is equivalent to `g : α → ℝ` at `source`. -/
def proveIsEquivalentRealCodomain {α : Q(Type)} (source : Q(Filter $α)) (f g : Q($α → ℝ)) :
    TacticM Q($f ~[$source] $g) := do
  match α with
  | ~q(ℝ) => return (← proveIsEquivalentReal q($source) q($f) q($g))
  | _ =>
    let ⟨castf, source', h_source, f', _⟩ ← ConvertDomain.convertFunDomain q($f) q($source)
    let ⟨castg, _, _, g', _⟩ ← ConvertDomain.convertFunDomain q($g) q($source)
    haveI : $castf =Q $castg := ⟨⟩; do
    let pf ← proveIsEquivalentReal q($source') q($f') q($g')
    return q(ConvertDomain.IsEquivalent_cast_domain $f' $g' $source $source' $castf $pf $h_source)

/-- Proves that `f : α → β` is equivalent to `g : α → β` at `source`. -/
def proveIsEquivalent {α β : Q(Type)} (source : Q(Filter $α)) (f : Q($α → $β)) (g : Q($α → $β))
    (β_norm : Q(NormedAddCommGroup $β)) :
    TacticM Q($f ~[$source] $g) := do
  let ⟨cast, h_cast⟩ ← ConvertDomain.getLawfulCodomainCast β β_norm
  let f' : Q($α → ℝ) := q(fun x ↦ $cast ($f x))
  let g' : Q($α → ℝ) := q(fun x ↦ $cast ($g x))
  let h_goal ← mkFreshExprMVarQ q($f' ~[$source] $g')
  let [newGoal] ← evalTacticAt (← `(tactic| push_cast)) h_goal.mvarId!
    | panic! "proveIsEquivalent: Unexpected number of goals after push_cast"
  let t : Q(Prop) ← inferType (.mvar newGoal)
  let ~q(@IsEquivalent.{0, 0} $α'' ℝ _ $source'' $f'' $g'') := t
    | panic! "proveIsEquivalent: Unexpected newGoal type"
  haveI : $α'' =Q $α := ⟨⟩; do
  newGoal.assign (← proveIsEquivalentRealCodomain q($source) q($f'') q($g''))
  assumeInstancesCommute
  return q(ConvertDomain.IsEquivalent_cast_codomain $f $g $source $cast $h_cast $h_goal)

/-- Computes asymptotics of functions. Domain and codomain of the function must be `ℕ`, `ℤ`,
`ℚ` or `ℝ`. It is able to close goals of types `Tendsto`, `IsLittleO`, `IsBigO` and `IsEquivalent`.

It works on wide class of function, that is constructed by arithmetic operations, powers, `exp` and
`log` operations. -/
elab "compute_asymptotics" : tactic =>
  focus do
  withMainContext do
    let goal ← getMainGoal
    let t : Q(Prop) ← getMainTarget
    match t with
    | ~q(@Tendsto.{0, 0} $domain $codomain $f $source $target) =>
      goal.assign (← proveTendsto q($f) q($source) q($target))
    | ~q(@IsLittleO.{0, 0, 0} $α $β $γ $inst_β $inst_γ $source $f $g) =>
      let inst_β' ← synthInstanceQ q(NormedAddCommGroup $β)
      let inst_γ' ← synthInstanceQ q(NormedAddCommGroup $γ)
      goal.assign (← proveIsLittleO source f g inst_β' inst_γ')
    | ~q(@IsBigO.{0, 0, 0} $α $β $γ $inst_β $inst_γ $source $f $g) =>
      let inst_β' ← synthInstanceQ q(NormedAddCommGroup $β)
      let inst_γ' ← synthInstanceQ q(NormedAddCommGroup $γ)
      goal.assign (← proveIsBigO source f g inst_β' inst_γ')
    | ~q(@IsEquivalent.{0, 0} $α $β $inst_β $source $f $g) =>
      let inst_β' ← synthInstanceQ q(NormedAddCommGroup $β)
      goal.assign (← proveIsEquivalent source f g inst_β')
    | _ =>
      throwError "unsupported goal"

-- TODO: support other types
/-- `compute_limit f at source with h` computes the limit `limit` of `f : ℝ → ℝ` at `source`
and add the fact `h : Tendsto f source limit` to the context. -/
elab (name := computeLimit)
    "compute_limit " f:(term) " at " source:(term) " with " name:(ident) : tactic => do
  focus do
  withMainContext do
    let f : Q(ℝ → ℝ) ← Term.elabTermAndSynthesize f q(ℝ → ℝ)
    let source : Q(Filter ℝ) ← Term.elabTermAndSynthesize source q(Filter ℝ)
    let ⟨limit, h_tendsto⟩ ← computeTendsto f source
    let goalNew ← (← getMainGoal).assert name.getId q(Tendsto $f $source $limit) h_tendsto
    let (_, goalNew) ← goalNew.intro1P
    replaceMainGoal [goalNew]

end ComputeAsymptotics

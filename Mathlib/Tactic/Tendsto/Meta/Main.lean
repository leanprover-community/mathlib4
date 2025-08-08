/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries
import Mathlib.Tactic.Tendsto.Lemmas
import Mathlib.Tactic.Tendsto.Meta.Trimming
import Mathlib.Tactic.Tendsto.Meta.LeadingTerm

/-!
# TODO
-/

open Filter Topology Asymptotics TendstoTactic Stream'.Seq ElimDestruct

open Lean Elab Meta Tactic Qq

namespace TendstoTactic

theorem basis_wo : WellFormedBasis [fun (x : ℝ) ↦ x] := by
  simp [WellFormedBasis]
  exact fun _ a ↦ a

lemma proveLastExpZero_aux {x y : ℝ} {z : Option ℝ} (hx : z = .some x) (hy : z = .some y)
    (hy0 : y = 0) : x = 0 := by
  aesop

partial def proveLastExpZero (li : Q(List ℝ)) : TacticM <| Option <|
    Q(∀ a, List.getLast? $li = .some a → a = 0) := do
  let .some last ← getLast li | return .none
  let .zero h_zero := ← compareReal last | return .none
  let h_eq : Q(List.getLast? $li = .some $last) ← mkFreshExprMVar q(List.getLast? $li = .some $last)
  let res ← evalTacticAt (← `(tactic| rfl)) h_eq.mvarId!
  if !res.isEmpty then
    panic! "proveLastExpZero: unexpected result of rfl"
  return .some q(fun _ ha ↦ proveLastExpZero_aux ha $h_eq $h_zero)

partial def getBasisExtension (basis basis' : Q(Basis)) : MetaM (Q(BasisExtension $basis)) := do
  match basis, basis' with
  | ~q(List.nil), ~q(List.nil) => return q(BasisExtension.nil)
  | ~q(List.cons $basis_hd $basis_tl), ~q(List.nil) => panic! "getBasisExtension: short basis"
  | ~q(List.nil), ~q(List.cons $basis_hd' $basis_tl') =>
    let ex ← getBasisExtension q([]) basis_tl'
    return q(BasisExtension.insert $basis_hd' $ex)
  | ~q(List.cons $basis_hd $basis_tl), ~q(List.cons $basis_hd' $basis_tl') =>
    if basis_hd == basis_hd' then
      -- they must be just equal. Maybe need to use isDefEq with reducible transparency?
      let ex ← getBasisExtension basis_tl basis_tl'
      return q(BasisExtension.keep $basis_hd $ex)
    else
      let ex ← getBasisExtension basis basis_tl'
      return q(BasisExtension.insert $basis_hd' $ex)

structure BasisState where
  basis : Q(Basis)
  logBasis : Q(LogBasis $basis)
  h_basis : Q(WellFormedBasis $basis)
  n_id : Q(Fin (List.length $basis))

abbrev BasisM := StateT BasisState TacticM

example (n m : ℕ) (h : n < m) : n < m + 1 := by exact Nat.lt_add_right 1 h
#check Fin.prop

partial def createMSImp (body : Expr) : BasisM MS := do
  if body.isBVar then
    if body.bvarIdx! != 0 then
      throwError "Unexpected bvarIdx in createMS: expected 0"
    return MS.monomial (← get).basis (← get).logBasis (← get).n_id (← get).h_basis
  match body.getAppFnArgs with
  | (``Neg.neg, #[_, _, arg]) => return MS.neg (← createMSImp arg)
  | (``HAdd.hAdd, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ex ← getBasisExtension ms1.basis ms2.basis
      let ms1' ← ms1.updateBasis ex ms2.logBasis ms2.h_basis
      return MS.add ms1' ms2 ⟨⟩
    else
      return MS.add ms1 ms2 ⟨⟩
  | (``HSub.hSub, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ex ← getBasisExtension ms1.basis ms2.basis
      let ms1' ← ms1.updateBasis ex ms2.logBasis ms2.h_basis
      return MS.sub ms1' ms2 ⟨⟩
    else
      return MS.sub ms1 ms2 ⟨⟩
  | (``HMul.hMul, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ex ← getBasisExtension ms1.basis ms2.basis
      let ms1' ← ms1.updateBasis ex ms2.logBasis ms2.h_basis
      return MS.mul ms1' ms2 ⟨⟩
    else
      return MS.mul ms1 ms2 ⟨⟩
  | (``Inv.inv, #[_, _, arg]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
    return MS.inv ms h_trimmed
  | (``HDiv.hDiv, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ⟨ms2, h_trimmed⟩ ← trimMS (← createMSImp arg2)
    if ms1.basis != ms2.basis then
      let ex ← getBasisExtension ms1.basis ms2.basis
      let ms1' ← ms1.updateBasis ex ms2.logBasis ms2.h_basis
      return MS.div ms1' ms2 h_trimmed ⟨⟩
    else
      return MS.div ms1 ms2 h_trimmed ⟨⟩
  | (``HPow.hPow, #[_, t, _, _, arg, exp]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
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
  | (``Real.log, #[arg]) =>
    -- dbg_trace "log"
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
    let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms.val
    let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendsto"
    let .some h_pos ← getLeadingTermCoefPos ms.val
      | throwError f!"Cannot prove that argument of log is eventually positive: {← ppExpr arg}"
    match ← proveLastExpZero exps with
    | .some h_last => return MS.log ms h_trimmed h_pos h_last
    | .none =>
      let kek ← ms.insertLastLog
      -- dbg_trace (← ppExpr kek.basis)
      let ⟨ms, h_trimmed⟩ ← trimMS kek
      let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms.val
      let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendsto"
      -- TODO: prove h_pos' from h_pos
      let .some h_pos ← getLeadingTermCoefPos ms.val
        | panic! s!"Cannot prove that argument of log is eventually positive: {← ppExpr arg}"
      let .some h_last ← proveLastExpZero exps | panic! "Unexpected last exp in log"
      -- dbg_trace "basis after update {← ppExpr ms.basis}"
      -- dbg_trace "h_basis after update {← ppExpr (← inferType ms.h_basis)}"
      -- haveI : List.length $((← get).basis) =Q List.length $ms.basis := ⟨⟩
      let new_n_id ← mkAppM ``Fin.castSucc #[(← get).n_id]
      StateT.set {
        basis := ms.basis
        logBasis := ms.logBasis
        h_basis := ms.h_basis
        n_id := new_n_id
          --q(Fin.castSucc $((← get).n_id))
      }
      return MS.log ms h_trimmed h_pos h_last
  | _ =>
    if body.hasLooseBVars then
      throwError f!"Unsupported body in createMS: {body}"
    else
      return MS.const (← get).basis (← get).logBasis body (← get).h_basis

def createMS (body : Expr) : TacticM MS := do
  return (← (createMSImp body).run {
    basis := q([fun (x : ℝ) ↦ x])
    logBasis := q(LogBasis.single _)
    h_basis := q(basis_wo)
    n_id := q(⟨0, by simp⟩)
  }).fst

def computeTendsto (f : Q(ℝ → ℝ)) :
    TacticM ((limit : Q(Filter ℝ)) × Q(Tendsto $f atTop $limit)) := do
  match f with
  | .lam _ _ b _ =>
    let ms ← createMS b
    -- dbg_trace f!"ms created: {← ppExpr ms.val}"
    let ⟨ms_trimmed, h_trimmed⟩ ← trimPartialMS ms
    -- dbg_trace "trimmed"
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
            $h_trimmed.get! $ms_trimmed.h_basis $h_leading_eq $h_exps $h_coef) : Expr)
        | .pos h_coef =>
          pure (q(PreMS.tendsto_top_of_FirstIsPos $ms_trimmed.h_wo $ms_trimmed.h_approx
            $h_trimmed.get! $ms_trimmed.h_basis $h_leading_eq $h_exps $h_coef) : Expr)
        | .zero _ => panic! "Unexpected zero coef with FirstIsPos"
      | .neg h_exps =>
        pure (q(PreMS.tendsto_zero_of_FirstIsNeg $ms_trimmed.h_wo $ms_trimmed.h_approx
          $h_leading_eq $h_exps) : Expr)
      | .zero h_exps =>
        pure (q(PreMS.tendsto_const_of_AllZero $ms_trimmed.h_wo $ms_trimmed.h_approx
          $h_trimmed.get! $ms_trimmed.h_basis $h_leading_eq $h_exps) : Expr)
    | _ => panic! "Unexpected result of trimMS"

    let ⟨0, t, h_tendsto⟩ ← inferTypeQ h_tendsto
      | panic! "Unexpected h_tendsto's universe level"
    let ~q(@Tendsto ℝ ℝ $g atTop $limit) := t | panic! "Unexpected h_tendsto's type"
    haveI' : $g =Q $ms.f := ⟨⟩
    -- let res := h_tendsto -- also works, decide later
    let res := q(Eq.subst (motive := fun x ↦ Tendsto x atTop $limit) $hf_eq $h_tendsto)
    return ⟨limit, res⟩
  | _ => throwError "Function should be lambda"

def convertFilter (f : Q(ℝ → ℝ)) (limit : Q(Filter ℝ)) : MetaM (Option Name × List (Q(ℝ → ℝ))) := do
  match limit with
  | ~q(atTop) => return (.none, [f])
  | ~q(atBot) => return (.some ``tendsto_bot_of_tendsto_top, [q(fun x ↦ $f (-x))])
  | ~q(𝓝[>] $c) => return (.some ``tendsto_nhds_right_of_tendsto_top, [q(fun x ↦ $f ($c + x⁻¹))])
  | ~q(𝓝[<] $c) => return (.some ``tendsto_nhds_left_of_tendsto_top, [q(fun x ↦ $f ($c - x⁻¹))])
  | ~q(𝓝[≠] $c) => return (.some ``tendsto_nhds_punctured_of_tendsto_top,
    [q(fun x ↦ $f ($c - x⁻¹)), q(fun x ↦ $f ($c + x⁻¹))])
  | _ => throwError f!"Unexpected source filter: {← ppExpr limit}"

elab "compute_asymptotics" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let target : Q(Prop) ← getMainTarget
    let ~q(@Filter.Tendsto ℝ ℝ $f $filter $targetLimit) := target
      | throwError "The goal must me in the form Tendsto (fun x ↦ ...) ... ..."
    let (convertLemma?, convertedFs) ← convertFilter f filter
    let proofs : List (Expr) ← convertedFs.mapM fun f => do
      let ⟨1, fType, f⟩ ← inferTypeQ f
        | throwError "Unexpected universe level of function in compute_asymptotics"
      let ~q(ℝ → ℝ) := fType | throwError "Only real functions are supported"
      let ⟨limit, h_tendsto⟩ ← computeTendsto f
      if !(← isDefEq limit targetLimit) then
        match targetLimit, limit with
        | ~q(𝓝 $a), ~q(𝓝 $b) =>
          let h_eq : Q($b = $a) ← mkFreshExprMVarQ q($b = $a)
          let extraGoals ← evalTacticAt (← `(tactic| try norm_num)) h_eq.mvarId!
          appendGoals extraGoals
          pure q(Eq.subst
            (motive := fun x ↦ Filter.Tendsto $f atTop (𝓝 x)) $h_eq $h_tendsto)
        | _ =>
          throwError m!"The tactic proved that the function tends to {← ppExpr limit},
            not {← ppExpr targetLimit}."
      else
        pure h_tendsto
    let pf ← match convertLemma? with
    | .none => pure proofs[0]!
    | .some convertLemma => mkAppM convertLemma (f :: proofs).toArray

    (← getMainGoal).assign pf

end TendstoTactic

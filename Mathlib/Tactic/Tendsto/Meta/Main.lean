/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Lemmas
import Mathlib.Tactic.Tendsto.Meta.Trimming
import Mathlib.Tactic.Tendsto.Meta.CompareMS

/-!
# TODO
-/

set_option linter.style.longLine false

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

/-- Returns `BasisExtension` creating `basis'` from `basis`. -/
partial def getBasisExtension (basis basis' : Q(Basis)) : MetaM (Q(BasisExtension $basis)) := do
  match basis, basis' with
  | ~q(List.nil), ~q(List.nil) => return q(BasisExtension.nil)
  | ~q(List.cons $basis_hd $basis_tl), ~q(List.nil) => panic! "getBasisExtension: short basis'"
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
  h_logBasis : Q(LogBasis.WellFormed $logBasis)
  n_id : Q(Fin (List.length $basis))

abbrev BasisM := StateT BasisState TacticM

-- assumptions:
-- `ms` tends to infinity
-- `ms` is o-little of logs of `left`
-- `ms.basis = left ++ cur :: right`
partial def findPlaceAux (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val))
    (left : Q(Basis)) (cur : Q(ℝ → ℝ)) (right : Q(Basis))
    (logBasis : Q(LogBasis ($cur :: $right)))
    (h_logBasis : Q(LogBasis.WellFormed $logBasis)) :
    BasisM (Q(Basis) × Q(ℝ → ℝ) × Q(Basis)) := do
  match right with
  | ~q(List.nil) =>
    -- then `cur` is the last element of basis, so
    -- `ms` is not o-little of `log cur = log b_n` as `ms ~ b_1 ^ e_1 * ... * b_n ^ e_n -> inf`
    return (← reduceBasis left, cur, ← reduceBasis right)
  | ~q(List.cons $right_hd $right_tl) =>
    -- in this case `log cur` is approximated by `logBasis`
    let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis
      | panic! s!"findPlaceAux: unexpected logBasis: {← ppExpr logBasis}"
    let log_hd' : MS := {
      basis := _
      logBasis := _
      val := q($log_hd)
      f := q(Real.log ∘ $cur)
      h_approx := q(sorry) -- from h_logBasis
      h_wo := q(sorry) -- from h_logBasis
      h_basis := q(sorry) -- from h_basis
      h_logBasis := q(LogBasis.tail_WellFormed $h_logBasis)
    }
    match ← MS.compare ms log_hd' h_trimmed q(sorry) with
    | .gt h => -- `ms` grows faster than `log cur` => we stop here, `left` is maximal
      return (← reduceBasis left, cur, right)
    | .lt h => -- `log cur` grows faster than `ms` => we add `cur` to the `left`
      findPlaceAux ms h_trimmed q($left ++ [$cur]) right_hd right_tl q(LogBasis.tail $logBasis)
        q(LogBasis.tail_WellFormed $h_logBasis)
    | .eq c hc h =>
      throwError "Not implemented: eq in findPlace"
  | _ => panic! "findPlaceAux: unexpected right"

/-- Finds `left`, `right_hd`, `right_tl` such that `ms.basis = left ++ right_hd :: right_tl`,
`ms` is o-little of logs of `left`, and `left` is maximal. Assumes `ms` tendsto infinity. -/
partial def findPlace (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) :
    BasisM (Q(Basis) × Q(ℝ → ℝ) × Q(Basis)) := do
  let basis : Q(Basis) := (← get).basis
  let ~q(List.cons $basis_hd $basis_tl) := basis | panic! "Unexpected basis (nil) in findPlace"
  findPlaceAux ms h_trimmed q(List.nil) basis_hd basis_tl (← get).logBasis (← get).h_logBasis

-- TODO: move
lemma PreMS.Approximates_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis} {coef : PreMS basis_tl}
    {exp : ℝ} {tl : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_approx : PreMS.Approximates (PreMS.cons (exp, coef) tl) f) :
    PreMS.Approximates coef (PreMS.Approximates_cons h_approx).choose := by
  generalize_proofs h
  exact h.choose_spec.left

def extractDeepCoef (ms : MS) (depth : Nat) : MetaM MS := do
  match depth with
  | 0 => return ms
  | newDepth + 1 =>
    let ~q(List.cons $basis_hd $basis_tl) := ms.basis | panic! "Unexpected basis in extractDeepCoef"
    let ~q(PreMS.cons ($exp, $coef) $tl) := ms.val | panic! "Unexpected ms in extractDeepCoef"
    let newMS : MS := {
      basis := q($basis_tl)
      logBasis := q(LogBasis.tail $ms.logBasis)
      val := q($coef)
      f := _
      h_approx := q(PreMS.Approximates_coef $ms.h_approx)
      h_wo := q((PreMS.WellOrdered_cons $ms.h_wo).left)
      h_basis := q(WellFormedBasis.tail $ms.h_basis)
      h_logBasis := q(LogBasis.tail_WellFormed $ms.h_logBasis)
    }
    extractDeepCoef newMS newDepth

lemma PreMS.Approximates_log_exp {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_approx : ms.Approximates f) :
    ms.Approximates (Real.log ∘ (Real.exp ∘ f)) := by
  convert h_approx
  ext
  simp

def updateNId (left right : Q(Basis)) (newElem : Q(ℝ → ℝ))
    (n_id : Q(Fin (List.length ($left ++ $right)))) :
    MetaM (Q(Fin (List.length ($left ++ $newElem :: $right)))) := do
  let leftLength ← computeLength left
  let n := (← getNatValue? (← withTransparency .all <| reduce q(Fin.val $n_id))).get!
  if n < leftLength then
    return ← mkAppM ``Fin.castSucc #[n_id]
  else
    return ← mkAppM ``Fin.succ #[n_id]

@[reducible]
def getInsertedIndex (left right : Basis) (newElem : ℝ → ℝ) :
    Fin (List.length (left ++ newElem :: right)) :=
  ⟨left.length, by simp⟩

def updateBasis (ms : MS) : BasisM MS := do
  let ex ← getBasisExtension ms.basis (← get).basis
  let ms' ← ms.updateBasis ex (← get).logBasis (← get).h_basis (← get).h_logBasis
  return ms'

theorem PreMS.sub_exp_Approximates {basis : Basis} {G H : PreMS basis} {f g : ℝ → ℝ}
    (h_basis : WellFormedBasis basis)
    (hG_approx : G.Approximates (Real.exp ∘ g))
    (hH_approx : H.Approximates (Real.exp ∘ (f - g))) :
    (G.mul H).Approximates (Real.exp ∘ f) := by
  have : Real.exp ∘ f = (Real.exp ∘ g) * (Real.exp ∘ (f - g)) := by
    ext
    simp [← Real.exp_add]
  rw [this]
  apply PreMS.mul_Approximates h_basis hG_approx hH_approx

partial def createExpMS (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) : BasisM MS := do
  let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms.val
  let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in createExpMS"
  match ← getFirstIs exps with
  | .pos _ =>
    -- find place for a new basis element
    let (left, right_hd, right_tl) ← findPlace ms h_trimmed
    haveI : $ms.basis =Q $left ++ $right_hd :: $right_tl := ⟨⟩
    -- extract deep coef `G`
    let G : MS := ← extractDeepCoef ms (← computeLength left)
    haveI : $G.basis =Q $right_hd :: $right_tl := ⟨⟩
    haveI expG := q(Real.exp ∘ $G.f)
    haveI : $expG =Q Real.exp ∘ $G.f := ⟨⟩
    do
    -- insert `exp g` in basis
    let new_n_id ← updateNId left q($right_hd :: $right_tl) expG (← get).n_id
    let basis := ← reduceBasis q($left ++ $expG :: $right_hd :: $right_tl)
    haveI : $basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩
    haveI h_basis : Q(WellFormedBasis ($left ++ $expG :: $right_hd :: $right_tl)) :=
      q(WellFormedBasis.insert $ms.h_basis sorry sorry sorry)
    StateT.set {
      basis := basis
      h_basis := q($h_basis)
      logBasis := q(LogBasis.extendBasisMiddle $expG $ms.logBasis $G.val)
      h_logBasis := q(LogBasis.extendBasisMiddle_WellFormed $h_basis $ms.h_logBasis $G.h_wo
        (PreMS.Approximates_log_exp $G.h_approx))
      n_id := q($new_n_id)
    }
    -- create H = F - G
    let G_updated ← updateBasis G
    let ms_updated ← updateBasis ms
    let H := ms_updated.sub G_updated ⟨⟩
    let ⟨H, hH_trimmed⟩ ← trimMS H
    -- prove `¬ FirstIsPos` for `H`
    let ⟨H_leading, hH_leading_eq⟩ ← getLeadingTermWithProof H.val
    let ~q(⟨$H_coef, $H_exps⟩) := H_leading | panic! "Unexpected leading of H in createExpMS"
    let h_H_nonpos : Q(¬ Term.FirstIsPos $H_exps) := q(sorry)
    let H_exp := H.exp h_H_nonpos
    let new_idx := q(getInsertedIndex $left ($right_hd :: $right_tl) $expG)
    let G_exp := MS.monomial (← get).basis (← get).logBasis new_idx (← get).h_basis
      (← get).h_logBasis
    -- g ~ G
    -- f - g ~ H
    -- exp (f - g) ~ H_exp
    -- exp g ~ G_exp
    haveI : $G_exp.basis =Q $H_exp.basis := ⟨⟩
    let kek := ← mkAppOptM ``PreMS.sub_exp_Approximates #[none, G_exp.val, H_exp.val, ms.f, G.f,
      G_exp.h_basis, G_exp.h_approx, H_exp.h_approx]
    -- let kek := q(PreMS.sub_exp_Approximates (f := $ms.f) (g := $G.f) $G_exp.h_basis $G_exp.h_approx sorry)
    return {
      basis := G_exp.basis
      logBasis := G_exp.logBasis
      val := q(PreMS.mul $G_exp.val $H_exp.val)
      f := q(Real.exp ∘ $ms.f)
      h_wo := q(PreMS.mul_WellOrdered $G_exp.h_wo $H_exp.h_wo)
      h_approx := kek
      h_basis := G_exp.h_basis
      h_logBasis := G_exp.h_logBasis
    }
    -- throwError "exp of function with infinite leading term is not implemented"
  | .neg h_exps =>
    let h_nonpos : Q(¬ Term.FirstIsPos $exps) := q(Term.not_FirstIsPos_of_FirstIsNeg $h_exps)
    return ms.exp h_nonpos
  | .zero h_exps =>
    let h_nonpos : Q(¬ Term.FirstIsPos $exps) := q(Term.not_FirstIsPos_of_AllZero $h_exps)
    return ms.exp h_nonpos

partial def createMSImp (body : Expr) : BasisM MS := do
  if body.isBVar then
    if body.bvarIdx! != 0 then
      throwError "Unexpected bvarIdx in createMS: expected 0"
    return MS.monomial (← get).basis (← get).logBasis (← get).n_id (← get).h_basis (← get).h_logBasis
  match body.getAppFnArgs with
  | (``Neg.neg, #[_, _, arg]) => return MS.neg (← createMSImp arg)
  | (``HAdd.hAdd, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.add ms1' ms2 ⟨⟩
    else
      return MS.add ms1 ms2 ⟨⟩
  | (``HSub.hSub, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
      return MS.sub ms1' ms2 ⟨⟩
    else
      return MS.sub ms1 ms2 ⟨⟩
  | (``HMul.hMul, #[_, _, _, _, arg1, arg2]) =>
    let ms1 ← createMSImp arg1
    let ms2 ← createMSImp arg2
    if ms1.basis != ms2.basis then
      let ms1' ← updateBasis ms1
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
      let ms1' ← updateBasis ms1
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
        h_logBasis := ms.h_logBasis
        n_id := new_n_id
      }
      return MS.log ms h_trimmed h_pos h_last
  | (``Real.exp, #[arg]) =>
    let ⟨ms, h_trimmed⟩ ← trimMS (← createMSImp arg)
    return ← createExpMS ms h_trimmed
  | _ =>
    if body.hasLooseBVars then
      throwError f!"Unsupported body in createMS: {body}"
    else
      return MS.const (← get).basis (← get).logBasis body (← get).h_basis (← get).h_logBasis

def createMS (body : Expr) : TacticM MS := do
  return (← (createMSImp body).run {
    basis := q([fun (x : ℝ) ↦ x])
    logBasis := q(LogBasis.single _)
    h_basis := q(basis_wo)
    h_logBasis := q(LogBasis.single_WellFormed _)
    n_id := q(⟨0, by simp⟩)
  }).fst

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
      -- dbg_trace f!"before : {← ppExpr ms_trimmed.val}"
      let ⟨leading, h_leading_eq⟩ ← getLeadingTermWithProof ms_trimmed.val
      -- dbg_trace "after"
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

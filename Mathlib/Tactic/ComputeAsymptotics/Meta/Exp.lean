/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module
public import Mathlib.Tactic.ComputeAsymptotics.Meta.BasisM
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Trimming
public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareMS

/-!
# TODO
-/

set_option linter.style.longLine false
set_option linter.flexible false

public meta section

open Filter Topology Asymptotics Stream'.Seq

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

section BasisUpdate

-- TODO: `h_c_pos` and `h_eq` are not actually used. Do we need them?
/-- Type for the `h_right` field of the `FindPlaceResult`. -/
inductive FindPlaceResultRight (f right_hd : Q(ℝ → ℝ))
  | gt (h : Q((Real.log ∘ $right_hd) =o[atTop] $f))
  | eq (c : Q(ℝ)) (h_c_pos : Q($c ≠ 0)) (h_eq : Q($f ~[atTop] $c • Real.log ∘ $right_hd))
    (log_right_hd : MS) (h_fun : Q(($log_right_hd.val).toFun = Real.log ∘ $right_hd))
deriving Inhabited

/-- Result of the `findPlace` function. -/
structure FindPlaceResult (ms : MS) where
  /-- `ms` is o-little of logarithms of `left`. -/
  left : Q(Basis)
  /-- Head of the right part of the basis. -/
  right_hd : Q(ℝ → ℝ)
  /-- Tail of the right part of the basis. -/
  right_tl : Q(Basis)
  /-- `ms` is o-little of logarithms of `left`. -/
  h_left : Q(∀ g ∈ List.getLast? $left, $(ms.val).toFun =o[atTop] (Real.log ∘ g))
  /-- Either `right_hd` is o-little of `ms.f` or `ms.f` and `right_hd` are equivalent. -/
  h_right : FindPlaceResultRight q($(ms.val).toFun) right_hd
deriving Inhabited

/-- Given `ms : MS` with `ms.basis = left ++ cur :: right` return the place where `ms` can be
inserted into the log-basis. Assumes `ms` is o-little of logarithms of `left`. -/
partial def findPlaceAux (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val))
    (h_pos : Q(Term.FirstIsPos (PreMS.leadingTerm $ms.val).exps))
    (left : Q(Basis)) (cur : Q(ℝ → ℝ)) (right : Q(Basis))
    (logBasis : Q(LogBasis ($cur :: $right)))
    (h_logBasis : Q(LogBasis.WellFormed $logBasis))
    (h_left : Q(∀ g ∈ List.getLast? $left, $(ms.val).toFun =o[atTop] (Real.log ∘ g))) :
    BasisM (FindPlaceResult ms) := do
  match right with
  | ~q(List.nil) =>
    -- then `cur` is the last element of basis, so
    -- `ms` is not o-little of `log cur = log b_n` as `ms ~ b_1 ^ e_1 * ... * b_n ^ e_n -> inf`
    let left' := ← reduceBasis left
    have : $left' =Q $left := ⟨⟩
    have : $cur =Q List.getLast $ms.basis sorry := ⟨⟩
    let h_right : Q((Real.log ∘ $cur) =o[atTop] $(ms.val).toFun) :=
      q(PreMS.log_basis_getLast_IsLittleO $ms.h_basis $ms.h_wo $ms.h_approx $h_trimmed $h_pos)
      -- (q(PreMS.log_basis_getLast_IsLittleO $ms.h_basis $ms.h_wo $ms.h_approx
      --   $h_trimmed $h_pos) : Expr)
    return {
      left := left'
      right_hd := cur
      right_tl := q(List.nil)
      h_left := q($h_left)
      h_right := .gt q($h_right)
    }
  | ~q(List.cons $right_hd $right_tl) =>
    -- in this case `log cur` is approximated by `logBasis`
    let logBasis' ← reduceLogBasis logBasis
    haveI : $logBasis' =Q $logBasis := ⟨⟩
    do
    -- check logBasis
    let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis'
      | panic! s!"findPlaceAux: unexpected logBasis: {← ppExpr logBasis}"
    have : $ms.basis =Q $left ++ $cur :: $right_hd :: $right_tl := ⟨⟩
    let h_basis' : Q(WellFormedBasis ($right_hd :: $right_tl)) :=
      q(WellFormedBasis.tail (WellFormedBasis.of_append_right $ms.h_basis))
    let log_hd_ms : MS := {
      basis := q($right_hd :: $right_tl)
      logBasis := _
      val := q($log_hd)
      -- f := q(Real.log ∘ $cur)
      h_approx := q(LogBasis.WellFormed_cons_Approximates $h_logBasis)
      h_wo := q(LogBasis.WellFormed_cons_WellOrdered $h_logBasis)
      h_basis := q($h_basis')
      h_logBasis := q(LogBasis.tail_WellFormed $h_logBasis)
    }
    let ⟨log_hd', h_log_hd_fun, h_log_hd_trimmed⟩ ← trimMS log_hd_ms
    -- match ← MS.compare ms log_hd' h_trimmed q(LogBasis.WellFormed_cons_Trimmed $h_logBasis) with
    match ← MS.compare ms log_hd' h_trimmed h_log_hd_trimmed with
    | .gt h => -- `ms` grows faster than `log cur` => we stop here, `left` is maximal
      let h : Q((Real.log ∘ $cur) =o[atTop] $(ms.val).toFun) :=
        q(($h_log_hd_fun ▸ LogBasis.WellFormed_cons_toFun $h_logBasis) ▸ $h)
      let left' := ← reduceBasis left
      have : $left' =Q $left := ⟨⟩
      return {
        left := left'
        right_hd := cur
        right_tl := right
        h_left := q($h_left)
        h_right := .gt q($h)
      }
    | .lt h => -- `log cur` grows faster than `ms` => we add `cur` to the `left`
      -- have : ($log_hd'.val).toFun =Q (Real.log ∘ $cur) := ⟨⟩
      let h : Q($(ms.val).toFun =o[atTop] (Real.log ∘ $cur)) :=
        q(($h_log_hd_fun ▸ LogBasis.WellFormed_cons_toFun $h_logBasis) ▸ $h)
      let h_left' : Q(∀ g ∈ List.getLast? ($left ++ [$cur]), $(ms.val).toFun =o[atTop] (Real.log ∘ g)) :=
        q(log_left_concat $left $h)
      findPlaceAux ms h_trimmed h_pos q($left ++ [$cur]) right_hd right_tl
        q(LogBasis.tail $logBasis) q(LogBasis.tail_WellFormed $h_logBasis) q($h_left')
    | .eq c hc h =>
      let h : Q($(ms.val).toFun ~[atTop] $c • Real.log ∘ $cur) :=
        q(($h_log_hd_fun ▸ LogBasis.WellFormed_cons_toFun $h_logBasis) ▸ $h)
      let left' := ← reduceBasis left
      have : $left' =Q $left := ⟨⟩
      return {
        left := left'
        right_hd := cur
        right_tl := right
        h_left := q($h_left)
        h_right := .eq q($c) q($hc) q($h) log_hd'
          q($h_log_hd_fun ▸ LogBasis.WellFormed_cons_toFun $h_logBasis)
      }
  | _ => panic! "findPlaceAux: unexpected right"

/-- Finds `left`, `right_hd`, `right_tl` such that `ms.basis = left ++ right_hd :: right_tl`,
`ms` is o-little of logs of `left`, and `left` is maximal. Assumes `ms` tendsto infinity. -/
partial def findPlace (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val))
    (h_pos : Q(Term.FirstIsPos (PreMS.leadingTerm $ms.val).exps)) :
    BasisM (FindPlaceResult ms) := do
  let basis : Q(Basis) := (← get).basis
  let ~q(List.cons $basis_hd $basis_tl) := basis | panic! "Unexpected basis (nil) in findPlace"
  findPlaceAux ms h_trimmed h_pos q(List.nil) basis_hd basis_tl (← get).logBasis (← get).h_logBasis
    q(by simp)

-- TODO: move
-- lemma PreMS.Approximates_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis} {coef : PreMS basis_tl}
--     {exp : ℝ} {tl : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
--     (h_approx : PreMS.Approximates (PreMS.cons exp coef tl) f) :
--     PreMS.Approximates coef (PreMS.Approximates_cons h_approx).choose := by
--   generalize_proofs h
--   exact h.choose_spec.left

structure ExtractDeepCoefResult (ms : MS) (depth : Q(Nat)) where
  coef : MS
  trimmed : Q(($coef.val).Trimmed)
  h_exps : Q(List.replicate $depth 0 ++ (PreMS.leadingTerm $coef.val).exps =
    (PreMS.leadingTerm $ms.val).exps)
  h_coef : Q(($ms.val).leadingTerm.coef = ($coef.val).leadingTerm.coef)

lemma PreMS.leadingTerm_cons_exps {basis_hd : ℝ → ℝ} {basis_tl : Basis} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} {depth : ℕ}
    {basis : Basis} {deepCoef : PreMS basis}
    (h : List.replicate depth 0 ++ deepCoef.leadingTerm.exps = coef.leadingTerm.exps) :
    List.replicate (depth + 1) 0 ++ deepCoef.leadingTerm.exps = (PreMS.mk (.cons 0 coef tl) f).leadingTerm.exps := by
  simp [PreMS.leadingTerm, List.replicate_succ]
  simpa [PreMS.leadingTerm] using h

/-- Given trimmed `ms : MS` finds its coefficient on depth `depth`. -/
def extractDeepCoef (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) (depth : Nat) :
    MetaM <| ExtractDeepCoefResult ms q($depth) := do
  match depth with
  | 0 => return ⟨ms, q($h_trimmed), q(rfl), q(rfl)⟩
  | newDepth + 1 =>
    let ~q(List.cons $basis_hd $basis_tl) := ms.basis | panic! "Unexpected basis in extractDeepCoef"
    let ~q(PreMS.mk (.cons $exp $coef $tl) $f) := ms.val | panic! "Unexpected ms in extractDeepCoef"
    let newMS : MS := {
      basis := q($basis_tl)
      logBasis := q(LogBasis.tail $ms.logBasis)
      val := q($coef)
      h_approx := q((PreMS.Approximates_cons $ms.h_approx).left)
      h_wo := q((PreMS.WellOrdered_cons $ms.h_wo).left)
      h_basis := q(WellFormedBasis.tail $ms.h_basis)
      h_logBasis := q(LogBasis.tail_WellFormed $ms.h_logBasis)
    }
    let new_h_trimmed : Q(PreMS.Trimmed $coef) := q((PreMS.Trimmed_cons $h_trimmed).left)
    let ⟨deepCoef, h_coef_trimmed, h_exps, h_coef⟩ ← extractDeepCoef newMS new_h_trimmed newDepth
    have : $exp =Q 0 := ⟨⟩
    return ⟨deepCoef, q($h_coef_trimmed),
      q(@PreMS.leadingTerm_cons_exps _ _ $coef $tl $f $newDepth _ _ $h_exps),
      q((@PreMS.leadingTerm_cons_coef _ _ $exp $coef $tl $f).trans $h_coef)⟩


-- -- TODO: rename
theorem PreMS.inv_exp_neg_toFun {basis : Basis} {n : Fin basis.length}
    {f : ℝ → ℝ}
    (h : basis[n] = Real.exp ∘ (-f)) :
    (monomialRpow basis n (-1)).toFun =ᶠ[atTop] (Real.exp ∘ f) := by
  apply EventuallyEq.of_eq
  simp [h]
  ext t
  simp [Real.rpow_neg_one, Real.exp_neg]

theorem PreMS.neg_log_exp_toFun {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ} (h : ms.toFun = f) :
    ms.neg.toFun = (Real.log ∘ Real.exp ∘ (-f)) := by
  subst h
  ext t
  simp

lemma PreMS.log_exp_toFun {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ} (h : ms.toFun = f) :
    ms.toFun = Real.log ∘ (Real.exp ∘ f) := by
  subst h
  ext t
  simp

/-- Finds the new `n_id` after inserting `newElem` into `basis = left ++ right`. -/
def getNewNId (left right : Q(Basis)) (newElem : Q(ℝ → ℝ))
    (n_id : Q(Fin (List.length ($left ++ $right)))) :
    MetaM (Q(Fin (List.length ($left ++ $newElem :: $right)))) := do
  let leftLength ← computeLength left
  let n := (← getNatValue? (← withTransparency .all <| reduce q(Fin.val $n_id))).get!
  if n < leftLength then
    return ← mkAppM ``Fin.castSucc #[n_id]
  else
    return ← mkAppM ``Fin.succ #[n_id]

/-- Returns the index of the inserted element at `Fin (List.length (left ++ newElem :: right))`. -/
abbrev getInsertedIndex (left right : Basis) (newElem : ℝ → ℝ) :
    Fin (List.length (left ++ newElem :: right)) :=
  ⟨left.length, by simp⟩

/-- Takes `ms` and its place in current `basis`.
Finds a deep coef `G` of `ms` to insert.
Inserts `exp ±G.f` (with the right sign) in the basis between `left` and `right_hd :: right_tl`.
Returns `G` and the MS representing `exp G.f`. -/
def insertEquivalentToBasis (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) (left : Q(Basis))
    (right_hd : Q(ℝ → ℝ)) (right_tl : Q(Basis))
    (coef : Q(ℝ)) (exps : Q(List ℝ))
    (h_leading : Q((PreMS.leadingTerm $ms.val) = ⟨$coef, $exps⟩))
    (h_first_is_pos' : Q(Term.FirstIsPos $exps))
    (h_left : Q(∀ g ∈ List.getLast? $left, $(ms.val).toFun =o[atTop] (Real.log ∘ g)))
    (h_right : Q((Real.log ∘ $right_hd) =o[atTop] $(ms.val).toFun)) : BasisM (MS × MS) := do
  let h_first_is_pos : Q(Term.FirstIsPos (($ms.val).leadingTerm).exps) :=
    q($h_leading ▸ $h_first_is_pos')
  haveI : $ms.basis =Q $left ++ $right_hd :: $right_tl := ⟨⟩; do
  -- extract deep coef `G`
  let depth := ← computeLength left
  -- let depthQ : Q(ℕ) := q($depth)
  -- have : $depth =Q List.length $left := ⟨⟩
  let ⟨G, hG_trimmed, hG_exps, hG_coef⟩ := ← extractDeepCoef ms h_trimmed depth
  let ⟨Gf, hGf⟩ ← Normalization.getFun G.val
  haveI : $G.basis =Q $right_hd :: $right_tl := ⟨⟩
  let h_ms_equiv_G : Q($(ms.val).toFun ~[atTop] $Gf) :=
    -- let h_coef : Q((PreMS.leadingTerm $ms.val).coef = (PreMS.leadingTerm $G.val).coef) :=
    --   q(sorry)
    --   -- ← mkEqRefl q((PreMS.leadingTerm $ms.val).coef)
    -- let h_exps : Q(List.replicate (List.length $left) 0 ++ (PreMS.leadingTerm $G.val).exps =
    --     (PreMS.leadingTerm $ms.val).exps) :=
    --   q(sorry)
      -- ← mkEqRefl q(List.replicate (List.length $left) 0 ++ (PreMS.leadingTerm $G.val).exps)
    let hG_exps : Q(List.replicate (List.length $left) 0 ++ (PreMS.leadingTerm $G.val).exps =
        (PreMS.leadingTerm $ms.val).exps) := hG_exps
    q(PreMS.IsEquivalent_of_leadingTerm_zeros_append $ms.h_wo $G.h_wo $ms.h_approx $G.h_approx
      $h_trimmed $hG_trimmed $hGf $ms.h_basis $hG_coef $hG_exps)
  do
  -- insert `exp g` in basis
  match ← compareReal coef with
  | .pos h_pos' =>
    let h_pos : Q(0 < ($ms.val).leadingTerm.coef) := q($h_leading ▸ $h_pos')
    have expG := q(Real.exp ∘ $Gf)
    haveI : $expG =Q Real.exp ∘ $Gf := ⟨⟩
    let new_n_id := ← getNewNId left q($right_hd :: $right_tl) expG (← get).n_id
    let basis := ← reduceBasis q($left ++ $expG :: $right_hd :: $right_tl)
    haveI : $basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩
    do
    let h_basis : Q(WellFormedBasis ($left ++ $expG :: $right_hd :: $right_tl)) :=
      q(WellFormedBasis.insert_pos_exp $left $right_hd $right_tl $ms.h_wo $ms.h_approx $h_trimmed
        $h_first_is_pos $h_pos $ms.h_basis $h_ms_equiv_G $h_left $h_right)
    let logBasis : Q(LogBasis $basis) :=
      ← reduceLogBasis q(LogBasis.extendBasisMiddle $expG $ms.logBasis $G.val)
    haveI : $logBasis =Q LogBasis.extendBasisMiddle $expG $ms.logBasis $G.val := ⟨⟩
    StateT.set {
      basis := q($basis)
      h_basis := q($h_basis)
      logBasis := q($logBasis)
      h_logBasis :=
        q(LogBasis.extendBasisMiddle_WellFormed $h_basis $ms.h_logBasis $G.h_wo
        $G.h_approx (PreMS.log_exp_toFun $hGf) $hG_trimmed)
      n_id := q($new_n_id)
    }
    let new_idx := q(getInsertedIndex $left ($right_hd :: $right_tl) $expG)
    let G_exp ← BasisM.monomial new_idx
    return (← updateBasis G, G_exp)
  | .neg h_neg' =>
    let h_neg : Q(($ms.val).leadingTerm.coef < 0) := q($h_leading ▸ $h_neg')
    have expG := q(Real.exp ∘ (-$Gf))
    haveI : $expG =Q Real.exp ∘ (-$Gf) := ⟨⟩
    let new_n_id := ← getNewNId left q($right_hd :: $right_tl) expG (← get).n_id
    let basis := ← reduceBasis q($left ++ $expG :: $right_hd :: $right_tl)
    haveI : $basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩
    do
    let h_basis : Q(WellFormedBasis ($left ++ $expG :: $right_hd :: $right_tl)) :=
      q(WellFormedBasis.insert_neg_exp $left $right_hd $right_tl $ms.h_wo $ms.h_approx $h_trimmed
        $h_first_is_pos $h_neg $ms.h_basis $h_ms_equiv_G $h_left $h_right)
    haveI : $G.neg.basis =Q $right_hd :: $right_tl := ⟨⟩
    do
    let logBasis : Q(LogBasis $basis) := ← reduceLogBasis q(LogBasis.extendBasisMiddle $expG
      $ms.logBasis $G.neg.val)
    haveI : $logBasis =Q LogBasis.extendBasisMiddle $expG $ms.logBasis $G.neg.val := ⟨⟩; do
    haveI : ($G.neg.val) =Q ($G.val).neg := ⟨⟩; do
    StateT.set {
      basis := q($basis)
      h_basis := q($h_basis)
      logBasis := q($logBasis)
      h_logBasis := q(LogBasis.extendBasisMiddle_WellFormed $h_basis $ms.h_logBasis
        (PreMS.neg_WellOrdered $G.h_wo) (PreMS.neg_Approximates $G.h_approx)
        (PreMS.neg_log_exp_toFun $hGf) (PreMS.neg_Trimmed $hG_trimmed))
      n_id := q($new_n_id)
    }
    let new_idx := q(getInsertedIndex $left ($right_hd :: $right_tl) $expG)
    let G_exp ← BasisM.monomialRpow new_idx q(-1)
    -- let ⟨G_exp_f, h_G_exp_f⟩ ← Normalization.getFun q($G_exp.val)
    -- G_exp_f =Q expG ^ (-1)
    -- haveI : $G_exp.basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩; do
    let new_idx : Q(Fin (List.length $G_exp.basis)) := new_idx
    -- let h_eq : Q(List.get _ $new_idx = Real.exp ∘ (-$(G.val).toFun)) := ← mkEqRefl q(Real.exp ∘ (-$(G.val).toFun))
    let ~q($basis_hd :: $basis_tl) := G_exp.basis | panic! "Unexpected basis in insertEquivalentToBasis"
    let h : Q(($G_exp.val).toFun =ᶠ[atTop] Real.exp ∘ $Gf) := ← mkAppOptM
      ``PreMS.inv_exp_neg_toFun #[G_exp.basis, new_idx, Gf, ← mkEqRefl q(Real.exp ∘ (-$Gf))]
    let G_exp ← (G_exp.replaceFun q(Real.exp ∘ $Gf) q($h)) --q($hGf ▸ PreMS.inv_exp_neg_toFun rfl))
    return (← updateBasis G, G_exp)
  | .zero _ => panic! "Unexpected coef = zero in insertEquivalentToBasis"

end BasisUpdate

theorem PreMS.sub_exp_toFun {basis : Basis} {ms G G_exp H : PreMS basis} {f : ℝ → ℝ}
    {Gf : ℝ → ℝ}
    (hf : ms.toFun = f)
    (hGf : G.toFun = Gf)
    (hH : H.toFun = (ms.sub G).toFun)
    (h_G_exp : G_exp.toFun = Real.exp ∘ Gf) :
    (G_exp.mul H.exp).toFun =ᶠ[atTop] Real.exp ∘ f := by
  apply EventuallyEq.of_eq
  subst hGf hf
  simp [h_G_exp, hH]
  ext t
  simp [← Real.exp_add]

theorem PreMS.sub_log_exp_toFun {basis basis' : Basis} {ex : BasisExtension basis}
    {L : PreMS basis}
    {ms H : PreMS ex.getBasis}
    {B expH : PreMS basis'}
    {f : ℝ → ℝ} {c : ℝ}
    {i : Fin basis'.length}
    (h_basis : WellFormedBasis basis')
    (h_ms : ms.toFun = f)
    (hB : B.toFun = basis'[i] ^ c)
    (hL : L.toFun = Real.log ∘ basis'[i])
    (hH : H.toFun = (ms.sub ((L.updateBasis ex).mulConst c)).toFun)
    (h_expH : expH.toFun = Real.exp ∘ H.toFun) :
    (B.mul expH).toFun =ᶠ[atTop] (Real.exp ∘ f) := by
  simp [h_expH, hH]
  have : Real.exp ∘ f = (Real.exp ∘ (c • Real.log ∘ basis'[i])) *
      (Real.exp ∘ (f - c • Real.log ∘ basis'[i])) := by
    ext
    simp [← Real.exp_add]
  rw [this]
  apply (basis_eventually_pos h_basis).mono
  intro t h_pos
  simp [hB, hL, h_ms]
  rw [Real.rpow_def_of_pos, mul_comm]
  apply h_pos
  simp

def MS.replaceFun' (ms : MS) (f : Q(ℝ → ℝ)) (h : Q(($ms.val).toFun =ᶠ[Filter.atTop] $f)) :
    MetaM <| (res : MS) × Q(($res.val).toFun = $f) := do
  let ~q($basis_hd :: $basis_tl) := ms.basis | panic! "replaceFun: unexpected basis"
  let res ← ms.replaceFun q($f) q($h)
  have : $res.basis =Q $basis_hd :: $basis_tl := ⟨⟩
  have : $res.val =Q ($ms.val).replaceFun $f := ⟨⟩
  return ⟨res, q(PreMS.replaceFun_toFun _ _)⟩

set_option maxHeartbeats 0 in
/-- Given a partially trimmed `ms` returns the MS approximating `exp ∘ ms.f`. -/
partial def createExpMSImp (ms : MS) (h_trimmed? : Option Q(PreMS.Trimmed $ms.val)) :
    BasisM <| (res : MS) × Q(($res.val).toFun = Real.exp ∘ ($ms.val).toFun) := do
  let ⟨leading, h_leading⟩ ← getLeadingTermWithProof ms.val
  let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in createExpMS"
  match ← getFirstIsPos exps with
  | .wrong h_nonpos' =>
    let h_nonpos : Q(¬ Term.FirstIsPos ($ms.val).leadingTerm.exps) := q($h_leading ▸ $h_nonpos')
    let res := ms.exp q($h_nonpos)
    have : $res.basis =Q $ms.basis := ⟨⟩
    have : $res.val =Q PreMS.exp $ms.val := ⟨⟩
    return ⟨res, q(PreMS.exp_toFun)⟩
  | .right h_first_is_pos' =>
    let h_first_is_pos : Q(Term.FirstIsPos (($ms.val).leadingTerm).exps) :=
      q($h_leading ▸ $h_first_is_pos')
    let h_trimmed := h_trimmed?.get!
    -- find place for a new basis element
    let ⟨left, right_hd, right_tl, h_left, h_right⟩ ← findPlace ms q($h_trimmed) q($h_first_is_pos)
    match h_right with
    | .eq c _ _ log_right_hd h_log_right_hd_fun =>
      -- expand `log_right_hd` basis
      let ex ← getBasisExtension q($log_right_hd.basis) q($ms.basis)
      have : ($ex).getBasis =Q $ms.basis := ⟨⟩
      let log_right_hd' ← log_right_hd.updateBasis q($ex) q($ms.logBasis)
        q($ms.h_basis) q($ms.h_logBasis)
      let ⟨H, hH_fun, hH_trimmed?⟩ ← trimPartialMS (ms.sub (log_right_hd'.mulConst q($c)))
      let ⟨expH, h_expH⟩ := ← createExpMSImp H hH_trimmed? -- here basis may grow
      -- return b_i^c * exp (H)
      let n : Q(Fin (List.length $expH.basis)) := ← findIndex q($expH.basis) q($right_hd)
      let B := MS.monomialRpow q($expH.basis) q($expH.logBasis) n q($c) q($expH.h_basis) q($expH.h_logBasis)
      let hB : Q(($B.val).toFun = List.get _ $n ^ $c) :=
        ← mkAppOptM ``PreMS.monomialRpow_toFun #[expH.basis, n, c]
      -- B ~ b_i^c
      -- expH ~ exp (f - c * log b_i)
      let res := B.mul expH
      let ⟨ms_f, hms_f⟩ ← Normalization.getFun ms.val
      let h : Q(($res.val).toFun =ᶠ[atTop] (Real.exp ∘ $ms_f)) :=
        ← mkAppOptM ``PreMS.sub_log_exp_toFun #[log_right_hd.basis, expH.basis, ex, log_right_hd.val,
          ms.val, H.val, B.val, expH.val,
          ms_f, c, n, expH.h_basis, hms_f, hB, h_log_right_hd_fun, hH_fun, h_expH]
      return ← res.replaceFun' q(Real.exp ∘ $ms_f) q($h)
    | .gt h_right =>
      let (G, G_exp) ← insertEquivalentToBasis ms q($h_trimmed) q($left) q($right_hd) q($right_tl) q($coef) q($exps)
        q($h_leading) q($h_first_is_pos') q($h_left) q($h_right)
      let ⟨Gf, hGf⟩ ← Normalization.getFun q($G.val)
      let ⟨G_exp_f, h_G_exp_f⟩ ← Normalization.getFun q($G_exp.val)
      -- create H = F - G
      let ms ← updateBasis ms
      let ⟨H, hH_fun, hH_trimmed?⟩ ← trimPartialMS (ms.sub G)
      -- prove `¬ FirstIsPos` for `H`
      let ⟨H_leading, hH_leading⟩ ← getLeadingTermWithProof H.val
      let ~q(⟨$H_coef, $H_exps⟩) := H_leading | panic! "Unexpected leading of H in createExpMS"
      let .wrong h_H_nonpos' := (← getFirstIsPos H_exps) | panic! "Unexpected nonpos in createExpMS"
      let h_H_nonpos : Q(¬ Term.FirstIsPos ($H.val).leadingTerm.exps) := q($hH_leading ▸ $h_H_nonpos')
      let H_exp := H.exp q($h_H_nonpos)
      -- g ~ G
      -- f - g ~ H
      -- exp (f - g) ~ H_exp
      -- exp g ~ G_exp
      haveI : $G_exp.basis =Q $H_exp.basis := ⟨⟩; do
      let ~q($basis_hd :: $basis_tl) := G_exp.basis | panic! "unexpected G_exp basis in createExpMS"
      let ⟨ms_f, hms_f⟩ ← Normalization.getFun ms.val
      let h : Q((($G_exp.val).mul $H_exp.val).toFun =ᶠ[atTop] Real.exp ∘ $ms_f) :=
        ← mkAppOptM ``PreMS.sub_exp_toFun #[G_exp.basis, ms.val, G.val, G_exp.val, H.val, ms_f, Gf, hms_f, hGf, hH_fun, h_G_exp_f]
      return ← (G_exp.mul H_exp).replaceFun' q(Real.exp ∘ $ms_f) h

/-- Given a partially trimmed `ms` returns the MS approximating `exp ∘ ms.f`. -/
partial def createExpMS (ms : MS) (h_trimmed? : Option Q(PreMS.Trimmed $ms.val)) :
    BasisM MS := do
  return (← createExpMSImp ms h_trimmed?).fst

end ComputeAsymptotics

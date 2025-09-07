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

open Filter Topology Asymptotics TendstoTactic Stream'.Seq Normalization

open Lean Elab Meta Tactic Qq

namespace TendstoTactic

theorem init_basis_wo : WellFormedBasis [fun (x : ℝ) ↦ x] :=
  WellFormedBasis.single _ (fun _ a ↦ a)

lemma proveLastExpZero_aux {x y : ℝ} {z : Option ℝ} (hx : z = .some x) (hy : z = .some y)
    (hy0 : y = 0) : x = 0 := by
  aesop

/-- Proves that the last element of the list is zero. Return `none` otherwise. -/
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
  | _ => panic! "unexpected basis or basis' in getBasisExtension"

/-- State of the `BasisM` monad. -/
structure BasisState where
  /-- Current basis. -/
  basis : Q(Basis)
  /-- Log-basis. -/
  logBasis : Q(LogBasis $basis)
  /-- Proof of well-formedness of the basis. -/
  h_basis : Q(WellFormedBasis $basis)
  /-- Proof of well-formedness of the log-basis. -/
  h_logBasis : Q(LogBasis.WellFormed $logBasis)
  /-- Index of the `id` function in the basis. -/
  n_id : Q(Fin (List.length $basis))

/-- Monad currying the basis. -/
abbrev BasisM := StateT BasisState TacticM

-- TODO: `h_c_pos` and `h_eq` are not used. Do we need them?
/-- Type for the `h_right` field of the `FindPlaceResult`. -/
inductive FindPlaceResultRight (f right_hd : Q(ℝ → ℝ))
  | gt (h : Q((Real.log ∘ $right_hd) =o[atTop] $f))
  | eq (c : Q(ℝ)) (h_c_pos : Q($c ≠ 0)) (h_eq : Q($f ~[atTop] $c • Real.log ∘ $right_hd))
    (log_right_hd : MS)
deriving Inhabited

/-- Result of the `findPlace` function. -/
structure FindPlaceResult (ms : MS) where
  /-- `ms` is o-little of logarithms of `left`. -/
  left : Q(Basis)
  /-- The head of the right part of the basis. -/
  right_hd : Q(ℝ → ℝ)
  /-- The tail of the right part of the basis. -/
  right_tl : Q(Basis)
  /-- `ms` is o-little of logarithms of `left`. -/
  h_left : Q(∀ g ∈ List.getLast? $left, $ms.f =o[atTop] (Real.log ∘ g))
  /-- Either `right_hd` is o-little of `ms.f` or `ms.f` and `right_hd` are equivalent. -/
  h_right : FindPlaceResultRight ms.f right_hd
deriving Inhabited

/-- Given `ms : MS` with `ms.basis = left ++ cur :: right` return the place where `ms` can be
inserted into the log-basis. Assumes `ms` is o-little of logarithms of `left`. -/
partial def findPlaceAux (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val))
    (h_pos : Q(Term.FirstIsPos (PreMS.leadingTerm $ms.val).exps))
    (left : Q(Basis)) (cur : Q(ℝ → ℝ)) (right : Q(Basis))
    (logBasis : Q(LogBasis ($cur :: $right)))
    (h_logBasis : Q(LogBasis.WellFormed $logBasis))
    (h_left : Q(∀ g ∈ List.getLast? $left, $ms.f =o[atTop] (Real.log ∘ g))) :
    BasisM (FindPlaceResult ms) := do
  match right with
  | ~q(List.nil) =>
    -- then `cur` is the last element of basis, so
    -- `ms` is not o-little of `log cur = log b_n` as `ms ~ b_1 ^ e_1 * ... * b_n ^ e_n -> inf`
    let left' := ← reduceBasis left
    have : $left' =Q $left := ⟨⟩
    let h_right : Q((Real.log ∘ $cur) =o[atTop] $ms.f) :=
      (q(PreMS.log_basis_getLast_IsLittleO $ms.h_basis $ms.h_wo $ms.h_approx
        $h_trimmed $h_pos) : Expr)
    return {
      left := left'
      right_hd := cur
      right_tl := q(List.nil)
      h_left := q($h_left)
      h_right := .gt q($h_right)
    }
  | ~q(List.cons $right_hd $right_tl) =>
    -- in this case `log cur` is approximated by `logBasis`
    let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis
      | panic! s!"findPlaceAux: unexpected logBasis: {← ppExpr logBasis}"
    have : $ms.basis =Q $left ++ $cur :: $right_hd :: $right_tl := ⟨⟩
    let h_basis' : Q(WellFormedBasis ($right_hd :: $right_tl)) :=
      q(WellFormedBasis.tail (WellFormedBasis.of_append_right $ms.h_basis))
    let log_hd' : MS := {
      basis := q($right_hd :: $right_tl)
      logBasis := _
      val := q($log_hd)
      f := q(Real.log ∘ $cur)
      h_approx := q(LogBasis.WellFormed_cons_Approximates $h_logBasis)
      h_wo := q(LogBasis.WellFormed_cons_WellOrdered $h_logBasis)
      h_basis := q($h_basis')
      h_logBasis := q(LogBasis.tail_WellFormed $h_logBasis)
    }
    let ⟨log_hd', h_log_hd_trimmed⟩ ← trimMS log_hd'
    -- match ← MS.compare ms log_hd' h_trimmed q(LogBasis.WellFormed_cons_Trimmed $h_logBasis) with
    match ← MS.compare ms log_hd' h_trimmed h_log_hd_trimmed with
    | .gt h => -- `ms` grows faster than `log cur` => we stop here, `left` is maximal
      let left' := ← reduceBasis left
      have : $left' =Q $left := ⟨⟩
      return {
        left := left'
        right_hd := cur
        right_tl := right
        h_left := q($h_left)
        h_right := .gt h
      }
    | .lt h => -- `log cur` grows faster than `ms` => we add `cur` to the `left`
      have : $log_hd'.f =Q (Real.log ∘ $cur) := ⟨⟩
      let h_left' : Q(∀ g ∈ List.getLast? ($left ++ [$cur]), $ms.f =o[atTop] (Real.log ∘ g)) :=
        q(log_left_concat $left $h)
      findPlaceAux ms h_trimmed h_pos q($left ++ [$cur]) right_hd right_tl
        q(LogBasis.tail $logBasis) q(LogBasis.tail_WellFormed $h_logBasis) q($h_left')
    | .eq c hc h =>
      let left' := ← reduceBasis left
      have : $left' =Q $left := ⟨⟩
      return {
        left := left'
        right_hd := cur
        right_tl := right
        h_left := q($h_left)
        h_right := .eq q($c) q($hc) h log_hd'
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
lemma PreMS.Approximates_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis} {coef : PreMS basis_tl}
    {exp : ℝ} {tl : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_approx : PreMS.Approximates (PreMS.cons (exp, coef) tl) f) :
    PreMS.Approximates coef (PreMS.Approximates_cons h_approx).choose := by
  generalize_proofs h
  exact h.choose_spec.left

/-- Given trimmed `ms : MS` finds its coefficient on depth `depth`. -/
def extractDeepCoef (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) (depth : Nat) :
    MetaM <| (ms : MS) × Q(PreMS.Trimmed $ms.val) := do
  match depth with
  | 0 => return ⟨ms, h_trimmed⟩
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
    let new_h_trimmed : Q(PreMS.Trimmed $coef) := q((PreMS.Trimmed_cons $h_trimmed).left)
    extractDeepCoef newMS new_h_trimmed newDepth

lemma PreMS.Approximates_log_exp {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_approx : ms.Approximates f) :
    ms.Approximates (Real.log ∘ (Real.exp ∘ f)) := by
  convert h_approx
  ext
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
@[reducible]
def getInsertedIndex (left right : Basis) (newElem : ℝ → ℝ) :
    Fin (List.length (left ++ newElem :: right)) :=
  ⟨left.length, by simp⟩

/-- Given `ms` immerses it into the current basis. -/
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

theorem PreMS.sub_log_exp_Approximates {basis : Basis} {B expH : PreMS basis} {f : ℝ → ℝ} {c : ℝ}
    {i : Fin basis.length}
    (h_basis : WellFormedBasis basis)
    (hB_approx : B.Approximates (basis[i] ^ c))
    (hH_approx : expH.Approximates (Real.exp ∘ (f - c • Real.log ∘ basis[i]))) :
    (B.mul expH).Approximates (Real.exp ∘ f) := by
  have : Real.exp ∘ f = (Real.exp ∘ (c • Real.log ∘ basis[i])) *
      (Real.exp ∘ (f - c • Real.log ∘ basis[i])) := by
    ext
    simp [← Real.exp_add]
  rw [this]
  apply PreMS.mul_Approximates h_basis _ hH_approx
  apply PreMS.Approximates_of_EventuallyEq _ hB_approx
  have : ∀ᶠ t in atTop, 0 < basis[i] t := by
    apply (basis_eventually_pos h_basis).mono
    intro x h
    exact h _ (by simp)
  apply this.mono
  intro x h_pos
  simp at h_pos ⊢
  rw [Real.rpow_def_of_pos h_pos]
  congr 1
  rw [mul_comm]

-- TODO: rename
theorem PreMS.inv_exp_neg_Approximates {basis : Basis} {n : Fin basis.length}
    {f : ℝ → ℝ}
    (h_basis : WellFormedBasis basis)
    (h : basis.get n = Real.exp ∘ (-f)) :
    (monomial_rpow basis n (-1)).Approximates (Real.exp ∘ f) := by
  convert monomial_rpow_Approximates h_basis using 1
  ext
  simp at h
  simp [h, Real.rpow_def_of_pos (Real.exp_pos _)]

theorem PreMS.neg_log_exp_Approximates {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_approx : ms.Approximates f) :
    ms.neg.Approximates (Real.log ∘ Real.exp ∘ (-f)) := by
  convert PreMS.neg_Approximates h_approx using 1
  ext
  simp

set_option maxHeartbeats 0 in
/-- Takes `ms` and its place in current `basis`.
Finds a deep coef `G` of `ms` to insert.
Inserts `exp ±G.f` (with the right sign) in the basis between `left` and `right_hd :: right_tl`.
Returns `G` and the MS representing `exp G.f`. -/
def insertEquivalentToBasis (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) (left : Q(Basis))
    (right_hd : Q(ℝ → ℝ)) (right_tl : Q(Basis))
    (coef : Q(ℝ)) (exps : Q(List ℝ))
    (h_first_is_pos : Q(Term.FirstIsPos $exps))
    (h_left : Q(∀ g ∈ List.getLast? $left, $ms.f =o[atTop] (Real.log ∘ g)))
    (h_right : Q((Real.log ∘ $right_hd) =o[atTop] $ms.f)) : BasisM (MS × MS) := do
  haveI : $ms.basis =Q $left ++ $right_hd :: $right_tl := ⟨⟩; do
  haveI : (PreMS.leadingTerm $ms.val).coef =Q $coef := ⟨⟩; do
  haveI : (PreMS.leadingTerm $ms.val).exps =Q $exps := ⟨⟩; do
  -- extract deep coef `G`
  let ⟨G, hG_trimmed⟩ := ← extractDeepCoef ms h_trimmed (← computeLength left)
  haveI : $G.basis =Q $right_hd :: $right_tl := ⟨⟩
  let h_ms_equiv_G : Q($ms.f ~[atTop] $G.f) :=
    let h_coef : Q((PreMS.leadingTerm $ms.val).coef = (PreMS.leadingTerm $G.val).coef) :=
      ← mkEqRefl q((PreMS.leadingTerm $ms.val).coef)
    let h_exps : Q(List.replicate (List.length $left) 0 ++ (PreMS.leadingTerm $G.val).exps =
        (PreMS.leadingTerm $ms.val).exps) :=
      ← mkEqRefl q(List.replicate (List.length $left) 0 ++ (PreMS.leadingTerm $G.val).exps)
    q(PreMS.IsEquivalent_of_leadingTerm_zeros_append $ms.h_wo $G.h_wo $ms.h_approx $G.h_approx
      $h_trimmed $hG_trimmed $ms.h_basis $h_coef $h_exps)
  do
  -- insert `exp g` in basis
  match ← compareReal coef with
  | .pos h_pos =>
    have expG := q(Real.exp ∘ $G.f)
    haveI : $expG =Q Real.exp ∘ $G.f := ⟨⟩
    let new_n_id := ← getNewNId left q($right_hd :: $right_tl) expG (← get).n_id
    let basis := ← reduceBasis q($left ++ $expG :: $right_hd :: $right_tl)
    haveI : $basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩
    do
    let h_basis : Q(WellFormedBasis ($left ++ $expG :: $right_hd :: $right_tl)) :=
      q(WellFormedBasis.insert_pos_exp $left $right_hd $right_tl $ms.h_wo $ms.h_approx $h_trimmed
        $h_first_is_pos $h_pos $ms.h_basis $h_ms_equiv_G $h_left $h_right)
    let logBasis : Q(LogBasis $basis) :=
      ← reduceLogBasis q(LogBasis.extendBasisMiddle $expG $ms.logBasis $G.val)
    StateT.set {
      basis := basis
      h_basis := q($h_basis)
      logBasis := logBasis
      h_logBasis := (q(LogBasis.extendBasisMiddle_WellFormed $h_basis $ms.h_logBasis $G.h_wo
        (PreMS.Approximates_log_exp $G.h_approx) $hG_trimmed) : Expr)
      n_id := q($new_n_id)
    }
    let new_idx := q(getInsertedIndex $left ($right_hd :: $right_tl) $expG)
    let G_exp := MS.monomial (← get).basis (← get).logBasis new_idx (← get).h_basis
      (← get).h_logBasis
    return (← updateBasis G, G_exp)
  | .neg h_neg =>
    have expG := q(Real.exp ∘ (-$G.f))
    haveI : $expG =Q Real.exp ∘ (-$G.f) := ⟨⟩
    let new_n_id := ← getNewNId left q($right_hd :: $right_tl) expG (← get).n_id
    let basis := ← reduceBasis q($left ++ $expG :: $right_hd :: $right_tl)
    haveI : $basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩
    do
    let h_basis : Q(WellFormedBasis ($left ++ $expG :: $right_hd :: $right_tl)) :=
      q(WellFormedBasis.insert_neg_exp $left $right_hd $right_tl $ms.h_wo $ms.h_approx $h_trimmed
        $h_first_is_pos $h_neg $ms.h_basis $h_ms_equiv_G $h_left $h_right)
    let logBasis : Q(LogBasis $basis) := ← reduceLogBasis q(LogBasis.extendBasisMiddle $expG
      $ms.logBasis $G.neg.val)
    StateT.set {
      basis := basis
      h_basis := q($h_basis)
      logBasis := logBasis
      h_logBasis := (q(LogBasis.extendBasisMiddle_WellFormed $h_basis $ms.h_logBasis
        (PreMS.neg_WellOrdered $G.h_wo) (PreMS.neg_log_exp_Approximates $G.h_approx)
        (PreMS.neg_Trimmed $hG_trimmed)) : Expr)
      n_id := q($new_n_id)
    }
    let new_idx := q(getInsertedIndex $left ($right_hd :: $right_tl) $expG)
    let G_exp := MS.monomial_rpow (← get).basis (← get).logBasis new_idx q(-1) (← get).h_basis
      (← get).h_logBasis
    haveI : $G_exp.basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩; do
    let new_idx : Q(Fin (List.length $G_exp.basis)) := new_idx
    let h_eq : Q(List.get _ $new_idx = Real.exp ∘ (-$G.f)) := ← mkEqRefl q(Real.exp ∘ (-$G.f))
    let G_exp := {G_exp with
      f := q(Real.exp ∘ $G.f)
      h_approx := q(PreMS.inv_exp_neg_Approximates $G_exp.h_basis $h_eq)
    }
    return (← updateBasis G, G_exp)
  | .zero _ => panic! "Unexpected coef = zero in insertEquivalentToBasis"

/-- Given a partially trimmed `ms` returns the MS approximating `exp ∘ ms.f`. -/
partial def createExpMS (ms : MS) (h_trimmed? : Option Q(PreMS.Trimmed $ms.val)) : BasisM MS := do
  let leading ← getLeadingTerm ms.val
  let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in createExpMS"
  match ← getFirstIsPos exps with
  | .wrong h_nonpos => return ms.exp h_nonpos
  | .right h_first_is_pos =>
    -- let .some h_trimmed := h_trimmed? | panic! "createExpMS: FirstIsPos but ms is not trimmed"
    let h_trimmed := h_trimmed?.get!
    -- find place for a new basis element
    let ⟨left, right_hd, right_tl, h_left, h_right⟩ ← findPlace ms h_trimmed h_first_is_pos
    match h_right with
    | .eq c _ _ log_right_hd =>
      have : $log_right_hd.f =Q Real.log ∘ $right_hd := ⟨⟩
      -- expand `log_right_hd` basis
      let ex ← getBasisExtension log_right_hd.basis ms.basis
      let log_right_hd' ← log_right_hd.updateBasis ex ms.logBasis ms.h_basis ms.h_logBasis
      have : $log_right_hd'.f =Q Real.log ∘ $right_hd := ⟨⟩
      let G := log_right_hd'.mulConst q($c)
      let H := ms.sub G
      let ⟨H, hH_trimmed?⟩ ← trimPartialMS H
      let expH := ← createExpMS H hH_trimmed?
      -- return b_i^c * exp (H)
      let n := ← findIndex (← get).basis right_hd
      let B := MS.monomial_rpow (← get).basis (← get).logBasis n q($c) (← get).h_basis
        (← get).h_logBasis
      -- B ~ b_i^c
      -- expH ~ exp (f - c * log b_i)
      let res := B.mul expH
      return {res with
        f := q(Real.exp ∘ $ms.f)
        h_approx :=
          ← mkAppOptM ``PreMS.sub_log_exp_Approximates #[res.basis, B.val, expH.val, ms.f, c, n,
            ms.h_basis, B.h_approx, expH.h_approx]
      }
    | .gt h_right =>
      let (G, G_exp) ← insertEquivalentToBasis ms h_trimmed left right_hd right_tl coef exps
        h_first_is_pos h_left h_right
      -- create H = F - G
      let ms ← updateBasis ms
      let H := ms.sub G
      let ⟨H, _⟩ ← trimPartialMS H
      -- prove `¬ FirstIsPos` for `H`
      let H_leading ← getLeadingTerm H.val
      let ~q(⟨$H_coef, $H_exps⟩) := H_leading | panic! "Unexpected leading of H in createExpMS"
      let .wrong h_H_nonpos := (← getFirstIsPos H_exps) | panic! "Unexpected nonpos in createExpMS"
      let H_exp := H.exp h_H_nonpos
      -- g ~ G
      -- f - g ~ H
      -- exp (f - g) ~ H_exp
      -- exp g ~ G_exp
      haveI : $G_exp.basis =Q $H_exp.basis := ⟨⟩
      -- TODO
      -- let h_approx := q(PreMS.sub_exp_Approximates (f := $ms.f) (g := $G.f)
      --  $G_exp.h_basis $G_exp.h_approx sorry)
      let h_approx := ← mkAppOptM ``PreMS.sub_exp_Approximates
        #[G_exp.basis, G_exp.val, H_exp.val, ms.f, G.f, G_exp.h_basis, G_exp.h_approx,
          H_exp.h_approx]
      return {
        basis := G_exp.basis
        logBasis := G_exp.logBasis
        val := q(PreMS.mul $G_exp.val $H_exp.val)
        f := q(Real.exp ∘ $ms.f)
        h_wo := q(PreMS.mul_WellOrdered $G_exp.h_wo $H_exp.h_wo)
        h_approx := h_approx
        h_basis := G_exp.h_basis
        h_logBasis := G_exp.h_logBasis
      }

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
    return MS.monomial (← get).basis (← get).logBasis (← get).n_id (← get).h_basis
      (← get).h_logBasis
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
      let res := MS.monomial_rpow (← get).basis (← get).logBasis (← get).n_id q(-1) (← get).h_basis
        (← get).h_logBasis
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
    let leading ← getLeadingTerm ms.val
    let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendsto"
    let .some h_pos ← getLeadingTermCoefPos ms.val
      | throwError f!"Cannot prove that argument of log is eventually positive: {← ppExpr arg}"
    match ← proveLastExpZero exps with
    | .some h_last => return MS.log ms h_trimmed h_pos h_last
    | .none =>
      let ⟨ms, h_trimmed⟩ ← trimMS (← ms.insertLastLog)
      let leading ← getLeadingTerm ms.val
      let ~q(⟨$coef, $exps⟩) := leading | panic! "Unexpected leading in computeTendsto"
      -- TODO: prove h_pos' from h_pos
      let .some h_pos ← getLeadingTermCoefPos ms.val
        | panic! s!"Cannot prove that argument of log is eventually positive: {← ppExpr arg}"
      let .some h_last ← proveLastExpZero exps | panic! "Unexpected last exp in log"
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
      return MS.const (← get).basis (← get).logBasis body (← get).h_basis (← get).h_logBasis

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

end TendstoTactic

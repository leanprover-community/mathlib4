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
    (log_right_hd : MS)
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
    let logBasis' ← reduceLogBasis logBasis
    haveI : $logBasis' =Q $logBasis := ⟨⟩
    do
    -- check logBasis
    let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis'
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
    (h_approx : PreMS.Approximates (PreMS.cons exp coef tl) f) :
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
    let ~q(PreMS.cons $exp $coef $tl) := ms.val | panic! "Unexpected ms in extractDeepCoef"
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

-- TODO: rename
theorem PreMS.inv_exp_neg_Approximates {basis : Basis} {n : Fin basis.length}
    {f : ℝ → ℝ}
    (h_basis : WellFormedBasis basis)
    (h : basis.get n = Real.exp ∘ (-f)) :
    (monomialRpow basis n (-1)).Approximates (Real.exp ∘ f) := by
  convert monomialRpow_Approximates h_basis using 1
  ext
  simp at h
  simp [h, Real.rpow_def_of_pos (Real.exp_pos _)]

theorem PreMS.neg_log_exp_Approximates {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_approx : ms.Approximates f) :
    ms.neg.Approximates (Real.log ∘ Real.exp ∘ (-f)) := by
  convert PreMS.neg_Approximates h_approx using 1
  ext
  simp

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
    let G_exp ← BasisM.monomial new_idx
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
    haveI : $G.neg.basis =Q $right_hd :: $right_tl := ⟨⟩
    do
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
    let G_exp ← BasisM.monomialRpow new_idx q(-1)
    haveI : $G_exp.basis =Q $left ++ $expG :: $right_hd :: $right_tl := ⟨⟩; do
    let new_idx : Q(Fin (List.length $G_exp.basis)) := new_idx
    let h_eq : Q(List.get _ $new_idx = Real.exp ∘ (-$G.f)) := ← mkEqRefl q(Real.exp ∘ (-$G.f))
    let G_exp := {G_exp with
      f := q(Real.exp ∘ $G.f)
      h_approx := (q(PreMS.inv_exp_neg_Approximates $G_exp.h_basis $h_eq) : Expr)
    }
    return (← updateBasis G, G_exp)
  | .zero _ => panic! "Unexpected coef = zero in insertEquivalentToBasis"

end BasisUpdate

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
  simp only [Fin.getElem_fin, Pi.pow_apply, Function.comp_apply, Pi.smul_apply,
    smul_eq_mul] at h_pos ⊢
  rw [Real.rpow_def_of_pos h_pos]
  congr 1
  rw [mul_comm]

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
      let n ← findIndex (← get).basis right_hd
      let B ← BasisM.monomialRpow n q($c)
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

end ComputeAsymptotics

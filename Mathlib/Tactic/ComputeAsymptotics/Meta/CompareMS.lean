/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareReal
public import Mathlib.Tactic.ComputeAsymptotics.Meta.MS
public import Mathlib.Tactic.ComputeAsymptotics.Meta.LeadingTerm

/-!
# Comparing growth rates of multiseries

To compare the growth rate of two trimmed multiseries it's enough to compare their leading terms
as lists using lexigraphic order. In this file we implement this procedure.

## Main definitions

* `compareLists` is the function that compares two lists using lexigraphic order.
* `compare` is the function that compares two trimmed multiseries.

-/

set_option linter.docPrime false

public meta section

namespace ComputeAsymptotics

namespace MS

open Lean Meta Elab Tactic Qq

open Topology Filter Asymptotics

/-- Result of comparing two lists using lexigraphic order. -/
inductive CompareListsResult (x y : Q(List ℝ))
| lt (h : Q($x < $y))
| gt (h : Q($y < $x))
| eq (h : Q($x = $y))

lemma List.Lex.cons' {x y : ℝ} {x_tl y_tl : List ℝ} (h : x = y) (h_tl : x_tl < y_tl) :
    (x :: x_tl) < (y :: y_tl) := by
  subst h
  exact List.Lex.cons h_tl

lemma List.cons_eq' {x y : ℝ} {x_tl y_tl : List ℝ} (h : x = y) (h_tl : x_tl = y_tl) :
    (x :: x_tl) = (y :: y_tl) := by
  subst h h_tl
  rfl

/-- Compare two lists using lexigraphic order. -/
partial def compareLists (x y : Q(List ℝ)) : TacticM <| CompareListsResult x y := do
  match x, y with
  | ~q(List.nil), ~q(List.nil) =>
    return .eq q(rfl)
  | ~q(List.cons _ _), ~q(List.nil) =>
    panic! "compareLists: lists of different lengths"
  | ~q(List.nil), ~q(List.cons _ _) =>
    panic! "compareLists: lists of different lengths"
  | ~q(List.cons $x_hd $x_tl), ~q(List.cons $y_hd $y_tl) =>
    match ← compareReal q($x_hd - $y_hd) with
    | .pos h => return .gt q(List.Lex.rel (lt_add_neg_iff_lt.mp $h))
    | .neg h => return .lt q(List.Lex.rel (sub_neg.mp $h))
    | .zero h_zero =>
      match ← compareLists x_tl y_tl with
      | .lt h => return .lt q(List.Lex.cons' (eq_of_sub_eq_zero $h_zero) $h)
      | .gt h => return .gt q(List.Lex.cons' (eq_of_sub_eq_zero $h_zero).symm $h)
      | .eq h => return .eq q(List.cons_eq' (eq_of_sub_eq_zero $h_zero) $h)
  | _ => panic! s!"compareLists: unexpected x or y:\n{← ppExpr x}\n{← ppExpr y}"

/-- Result of comparing two trimmed multiseries. -/
inductive CompareResult (f g : Q(ℝ → ℝ))
| lt (h : Q($f =o[atTop] $g))
| gt (h : Q($g =o[atTop] $f))
| eq (c : Q(ℝ)) (hc : Q($c ≠ 0)) (h : Q($f ~[atTop] $c • $g))

/-- Prove that a trimmed multiseries is not zero. -/
def proveNeZero (ms : MS) : MetaM Q(¬ PreMS.IsZero $ms.val) := do
  let ~q($basis_hd :: $basis_tl) := ms.basis | panic! "proveNeZero: unexpected basis"
  let ~q(PreMS.mk (.cons $exp $coef $tl) $f) := ms.val | panic! "proveNeZero: unexpected val"
  return q(PreMS.cons_not_IsZero)

/-- Compare two trimmed multiseries. It assumes that `x.basis = ... ++ y.basis` and that `x` and
`y` both are not `nil`s. -/
def compare (x y : MS)
    (hx_trimmed : Q(PreMS.Trimmed $x.val))
    (hy_trimmed : Q(PreMS.Trimmed $y.val)) :
    TacticM <| CompareResult q(($x.val).toFun) q(($y.val).toFun) := do
  let left ← expressAsAppend x.basis y.basis
  haveI : $x.basis =Q $left ++ $y.basis := ⟨⟩; do
  let tx ← getLeadingTerm x.val
  let ty ← getLeadingTerm y.val
  let ~q(⟨$x_coef, $x_exps⟩) := tx | panic! "Unexpected x in compareLeadingTerms"
  let ~q(⟨$y_coef, $y_exps⟩) := ty | panic! "Unexpected y in compareLeadingTerms"
  let n : Nat := (← computeLength x.basis) - (← computeLength y.basis)
  let zeros ← replicate n q(0 : ℝ)
  let y_exps' : Q(List ℝ) := ← reduceAppend (α := q(ℝ)) q($zeros) q($y_exps)
  haveI : $x_exps =Q (PreMS.leadingTerm $x.val).exps := ⟨⟩; do
  haveI : $y_exps' =Q List.replicate (List.length $left) 0 ++ (PreMS.leadingTerm $y.val).exps := ⟨⟩
  do
  let res ← compareLists q($x_exps) q($y_exps')
  match res with
  | .lt h =>
    let h_ne_zero : Q(¬ PreMS.IsZero $y.val) ← proveNeZero y
    return .lt q(PreMS.IsLittleO_of_lt_leadingTerm_left $x.h_wo $y.h_wo $x.h_approx $y.h_approx
      $hx_trimmed $hy_trimmed $x.h_basis $h_ne_zero $h)
  | .gt h =>
    let h_ne_zero : Q(¬ PreMS.IsZero $x.val) ← proveNeZero x
    return .gt q(PreMS.IsLittleO_of_lt_leadingTerm_right $x.h_wo $y.h_wo $x.h_approx $y.h_approx
      $hx_trimmed $hy_trimmed $x.h_basis $h_ne_zero $h)
  | .eq h =>
    let c : Q(ℝ) := q($x_coef / $y_coef)
    let hc := ← CompareReal.proveNeZero c
    haveI : $x_coef =Q (PreMS.leadingTerm $x.val).coef := ⟨⟩
    haveI : $y_coef =Q (PreMS.leadingTerm $y.val).coef := ⟨⟩
    return .eq c hc q(PreMS.IsEquivalent_of_leadingTerm_zeros_append_mul_coef $x.h_wo $y.h_wo
      $x.h_approx $y.h_approx $hx_trimmed $hy_trimmed $x.h_basis $hc ($h).symm)

end MS

open Filter Topology Asymptotics

-- TODO: refactor below

lemma log_congr_IsEquivalent_left (left : Basis) {f f' : ℝ → ℝ} (h_equiv : f ~[atTop] f')
    (h : ∀ g ∈ left.getLast?, f =o[atTop] (Real.log ∘ g)) :
    ∀ (g : ℝ → ℝ), left.getLast? = some g → (Real.log ∘ Real.exp ∘ f') =o[atTop]
      (Real.log ∘ g) := by
  peel h with _ _ h
  apply Asymptotics.IsEquivalent.trans_isLittleO _ h
  convert h_equiv.symm
  ext
  simp

lemma log_congr_IsEquivalent_right (right : Basis) (f f' : ℝ → ℝ)
    (h_equiv : f ~[atTop] f')
    (h : ∀ g ∈ right.head?, (Real.log ∘ g) =o[atTop] f) :
    ∀ (g : ℝ → ℝ), right.head? = some g → (Real.log ∘ g) =o[atTop] f' := by
  peel h with _ _ h
  exact Asymptotics.IsLittleO.trans_isEquivalent h h_equiv

lemma log_congr_IsEquivalent_right' (right_hd : ℝ → ℝ) (right_tl : Basis) {f f' : ℝ → ℝ}
    (h_equiv : f ~[atTop] f')
    (h : (Real.log ∘ right_hd) =o[atTop] f) :
    ∀ g ∈ (right_hd :: right_tl).head?, (Real.log ∘ g) =o[atTop] (Real.log ∘ Real.exp ∘ f') := by
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
  apply Asymptotics.IsLittleO.trans_isEquivalent h
  convert h_equiv
  ext
  simp

lemma log_left_concat (left : Basis) {f last : ℝ → ℝ} (h : f =o[atTop] (Real.log ∘ last)) :
    ∀ g ∈ List.getLast? (left ++ [last]), f =o[atTop] (Real.log ∘ g) := by
  simpa

open PreMS

lemma WellFormedBasis.insert_pos_exp (left : Basis) (right_hd : ℝ → ℝ) (right_tl : Basis)
    {f' : ℝ → ℝ}
    {ms : PreMS (left ++ right_hd :: right_tl)}
    (h_wo : ms.WellOrdered) (h_approx : ms.Approximates)
    (h_trimmed : PreMS.Trimmed ms)
    (h_exps : Term.FirstIsPos (ms.leadingTerm).exps)
    (h_coef : 0 < (ms.leadingTerm).coef)
    (h_basis : WellFormedBasis (left ++ right_hd :: right_tl))
    (h_equiv : ms.toFun ~[atTop] f')
    (h_left : ∀ g ∈ left.getLast?, ms.toFun =o[atTop] (Real.log ∘ g))
    (h_right : (Real.log ∘ right_hd) =o[atTop] ms.toFun) :
    WellFormedBasis (left ++ (Real.exp ∘ f') :: right_hd :: right_tl) := by
  apply WellFormedBasis.insert h_basis
  · apply Tendsto.comp Real.tendsto_exp_atTop
    apply h_equiv.tendsto_atTop
    exact PreMS.tendsto_top_of_FirstIsPos h_wo h_approx h_trimmed h_basis rfl h_exps h_coef rfl
  · exact log_congr_IsEquivalent_left left h_equiv h_left
  · exact log_congr_IsEquivalent_right' right_hd right_tl h_equiv h_right

lemma WellFormedBasis.insert_neg_exp (left : Basis) (right_hd : ℝ → ℝ) (right_tl : Basis)
    {f' : ℝ → ℝ}
    {ms : PreMS (left ++ right_hd :: right_tl)}
    (h_wo : ms.WellOrdered) (h_approx : ms.Approximates)
    (h_trimmed : PreMS.Trimmed ms)
    (h_exps : Term.FirstIsPos (ms.leadingTerm).exps)
    (h_coef : (ms.leadingTerm).coef < 0)
    (h_basis : WellFormedBasis (left ++ right_hd :: right_tl))
    (h_equiv : ms.toFun ~[atTop] f')
    (h_left : ∀ g ∈ left.getLast?, ms.toFun =o[atTop] (Real.log ∘ g))
    (h_right : (Real.log ∘ right_hd) =o[atTop] ms.toFun) :
    WellFormedBasis (left ++ (Real.exp ∘ (-f')) :: right_hd :: right_tl) := by
  apply WellFormedBasis.insert_pos_exp _ _ _ (ms := ms.neg)
    (neg_WellOrdered h_wo) (neg_Approximates h_approx) (neg_Trimmed h_trimmed)
  · simpa [neg_leadingTerm]
  · simpa [neg_leadingTerm]
  · exact h_basis
  · convert h_equiv.neg using 1
    ext t
    simp
  · peel h_left
    convert this.neg_left using 1
    ext t
    simp
  · convert h_right.neg_right using 1
    ext t
    simp

end ComputeAsymptotics

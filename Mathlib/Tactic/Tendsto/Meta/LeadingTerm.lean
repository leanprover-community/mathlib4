/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries
import Mathlib.Tactic.Tendsto.Meta.MS
import Mathlib.Tactic.Tendsto.Meta.ElimDestruct
import Mathlib.Tactic.Tendsto.Meta.CompareReal

/-!
# TODO
-/

open Lean Meta Elab Tactic Qq

namespace TendstoTactic

/-- Given `ms`, computes its leading term. -/
partial def getLeadingTerm {basis : Q(Basis)} (ms : Q(PreMS $basis)) : MetaM Q(Term) := do
  match basis with
  | ~q(List.nil) =>
    return q(⟨$ms, List.nil⟩)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.nil) =>
      throwError "Unexpected ms = nil in getLeadingTerm"
    | ~q(PreMS.cons ($exp, $coef) $tl) =>
      match ← getLeadingTerm coef with
      | ~q(⟨$coef_coef, $coef_exps⟩) =>
        return q(⟨$coef_coef, $exp :: $coef_exps⟩)
      | _ =>
        dbg_trace "Unexpected pre in getLeadingTerm"
        return q(⟨Term.coef (PreMS.leadingTerm $coef), $exp :: Term.exps (PreMS.leadingTerm $coef)⟩)
    | _ => throwError "Unexpected ms in getLeadingTerm"
  | _ => throwError "Unexpected basis in getLeadingTerm"

def getLeadingTermWithProof {basis : Q(Basis)} (ms : Q(PreMS $basis)) :
    MetaM ((t : Q(Term)) × Q(PreMS.leadingTerm $ms = $t)) := do
  let rhs ← getLeadingTerm ms
  let e ← mkFreshExprMVar q(PreMS.leadingTerm $ms = $rhs)
  e.mvarId!.applyRfl
  return ⟨rhs, e⟩

def getLeadingTermCoefPos {basis : Q(Basis)} (ms : Q(PreMS $basis)) :
    TacticM (Option Q(0 < (PreMS.leadingTerm $ms).coef)) := do
  match basis with
  | ~q(List.nil) =>
    let .pos pf ← compareReal ms | return .none
    return .some pf
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.nil) => return .none
    | _ =>
      let ⟨rhs, h_eq⟩ ← getLeadingTermWithProof ms
      let ~q(⟨$coef, $exps⟩) := rhs | return .none
      let .pos pf ← compareReal coef | return .none
      return .some q(Eq.subst (motive := fun (x : Term) ↦ 0 < x.coef) (Eq.symm $h_eq) $pf)

inductive FirstIsResult (x : Q(List ℝ))
| zero (pf : Q(Term.AllZero $x))
| pos (pf : Q(Term.FirstIsPos $x))
| neg (pf : Q(Term.FirstIsNeg $x))

partial def getFirstIs (x : Q(List ℝ)) : TacticM (FirstIsResult x) := do
  match x with
  | ~q(List.nil) => return .zero q(Term.AllZero_of_nil)
  | ~q(List.cons $hd $tl) =>
    match ← compareReal hd with
    | .pos h_hd => return .pos q(Term.FirstIsPos_of_head $tl $h_hd)
    | .neg h_hd => return .neg q(Term.FirstIsNeg_of_head $tl $h_hd)
    | .zero h_hd =>
      match ← getFirstIs tl with
      | .zero h_tl => return .zero q(Term.AllZero_of_tail $h_hd $h_tl)
      | .pos h_tl => return .pos q(Term.FirstIsPos_of_tail $h_hd $h_tl)
      | .neg h_tl => return .neg q(Term.FirstIsNeg_of_tail $h_hd $h_tl)

end TendstoTactic

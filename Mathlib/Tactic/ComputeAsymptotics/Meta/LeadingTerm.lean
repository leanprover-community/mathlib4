/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries
public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareReal

/-!
# Computing the leading term of a trimmed multiseries
-/

public meta section

open Lean Meta Elab Tactic Qq

namespace ComputeAsymptotics

/-- Given a trimmed multiseries `ms`, computes its leading term. -/
partial def getLeadingTerm {basis : Q(Basis)} (ms : Q(PreMS $basis)) : MetaM Q(Term) := do
  match basis with
  | ~q(List.nil) =>
    return q(⟨$ms, List.nil⟩)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.mk .nil $f) =>
      return q(⟨0, List.replicate (List.length ($basis_hd :: $basis_tl)) 0⟩)
    | ~q(PreMS.mk (.cons $exp $coef $tl) $f) =>
      match ← getLeadingTerm coef with
      | ~q(⟨$coef_coef, $coef_exps⟩) =>
        return q(⟨$coef_coef, $exp :: $coef_exps⟩)
      | _ =>
        return q(⟨Term.coef (PreMS.leadingTerm $coef), $exp :: Term.exps (PreMS.leadingTerm $coef)⟩)
    | _ =>
      return q(PreMS.leadingTerm $ms)
  | _ => panic! "Unexpected basis in getLeadingTerm"

/-- Given a trimmed multiseries `ms`, computes its leading term with a proof. -/
partial def getLeadingTermWithProof {basis : Q(Basis)} (ms : Q(PreMS $basis)) :
    MetaM ((t : Q(Term)) × Q(PreMS.leadingTerm $ms = $t)) := do
  match basis with
  | ~q(List.nil) =>
    return ⟨q(⟨($ms).toReal, List.nil⟩), q(PreMS.const_leadingTerm)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.mk .nil $f) =>
      return ⟨q(⟨0, List.replicate (List.length ($basis_hd :: $basis_tl)) 0⟩), q(PreMS.nil_leadingTerm)⟩
    | ~q(PreMS.mk (.cons $exp $coef $tl) $f) =>
      let ⟨coef_t, coef_h_eq⟩ ← getLeadingTermWithProof coef
      match coef_t with
      | ~q(⟨$coef_coef, $coef_exps⟩) =>
        return ⟨q(⟨$coef_coef, $exp :: $coef_exps⟩), q(PreMS.cons_leadingTerm' $coef_h_eq)⟩
      | _ =>
        return ⟨q(⟨Term.coef (PreMS.leadingTerm $coef), $exp :: Term.exps (PreMS.leadingTerm $coef)⟩), q(PreMS.cons_leadingTerm)⟩
    | _ =>
      return ⟨q(PreMS.leadingTerm $ms), q(rfl)⟩
  | _ => panic! "Unexpected basis in getLeadingTerm"

/-- Proves that the coefficient of the leading term of a trimmed multiseries is positive.
Return `none` if cannot prove it. -/
def getLeadingTermCoefPos {basis : Q(Basis)} (ms : Q(PreMS $basis)) :
    TacticM (Option Q(0 < (PreMS.leadingTerm $ms).coef)) := do
  match basis with
  | ~q(List.nil) =>
    let .pos pf ← compareReal ms | return .none
    return .some pf
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.mk .nil $f) => return .none
    | _ =>
      let ⟨rhs, h_eq⟩ ← getLeadingTermWithProof ms
      let ~q(⟨$coef, $exps⟩) := rhs | return .none
      let .pos pf ← compareReal coef | return .none
      return .some q(Eq.subst (motive := fun (x : Term) ↦ 0 < x.coef) (Eq.symm $h_eq) $pf)
  | _ => panic! "Unexpected basis in getLeadingTermCoefPos"

/-- Result of checking for a `x : List ℝ` if `x.FirstIsPos` or `x.FirstIsNeg` or `x.AllZero`. -/
inductive FirstIsResult (x : Q(List ℝ))
| zero (pf : Q(Term.AllZero $x))
| pos (pf : Q(Term.FirstIsPos $x))
| neg (pf : Q(Term.FirstIsNeg $x))

/-- Given a list `x`, checks if `x.FirstIsPos` or `x.FirstIsNeg` or `x.AllZero`. -/
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
  | ~q(List.replicate $n 0) => return .zero q(Term.AllZero_of_replicate)
  | _ => panic! "Unexpected list in getFirstIs"

/-- Result of checking for a `x : List ℝ` if `x.FirstIsPos`. -/
inductive FirstIsPosResult (x : Q(List ℝ))
| right (pf : Q(Term.FirstIsPos $x))
| wrong (pf : Q(¬ Term.FirstIsPos $x))

/-- Given a list `x`, checks if `x.FirstIsPos`. -/
def getFirstIsPos (x : Q(List ℝ)) : TacticM (FirstIsPosResult x) := do
  match ← getFirstIs x with
  | .pos pf => return .right pf
  | .neg pf => return .wrong q(Term.not_FirstIsPos_of_FirstIsNeg $pf)
  | .zero pf => return .wrong q(Term.not_FirstIsPos_of_AllZero $pf)

end ComputeAsymptotics

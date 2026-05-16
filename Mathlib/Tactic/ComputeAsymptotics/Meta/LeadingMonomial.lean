/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries
public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareReal

/-!
# Computing the leading monomial of a trimmed multiseries
-/

public meta section

open Lean Meta Elab Tactic Qq

namespace Tactic.ComputeAsymptotics

/-- Given a trimmed multiseries `ms`, computes its leading monomial. -/
partial def getLeadingMonomial {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis)) :
    MetaM Q(Monomial) := do
  match basis with
  | ~q(List.nil) =>
    return q(⟨$ms, List.nil⟩)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(MultiseriesExpansion.mk .nil $f) =>
      return q(⟨0, List.replicate (List.length ($basis_hd :: $basis_tl)) 0⟩)
    | ~q(MultiseriesExpansion.mk (.cons $exp $coef $tl) $f) =>
      match ← getLeadingMonomial coef with
      | ~q(⟨$coef_coef, $coef_exps⟩) =>
        return q(⟨$coef_coef, $exp :: $coef_exps⟩)
      | _ =>
        return q(⟨Monomial.coef (MultiseriesExpansion.leadingMonomial $coef),
          $exp :: Monomial.unit (MultiseriesExpansion.leadingMonomial $coef)⟩)
    | _ =>
      return q(MultiseriesExpansion.leadingMonomial $ms)
  | _ => panic! "Unexpected basis in getLeadingMonomial"

/-- Given a trimmed multiseries `ms`, computes its leading monomial with a proof. -/
partial def getLeadingMonomialWithProof {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis)) :
    TacticM ((t : Q(Monomial)) × Q(MultiseriesExpansion.leadingMonomial $ms = $t)) := do
  match basis with
  | ~q(List.nil) =>
    let coef_t := q(($ms).toReal)
    let ⟨coef_t', h_coef_t_eq⟩ ← normalizeReal q($coef_t)
    return ⟨q(⟨$coef_t', List.nil⟩), q($h_coef_t_eq ▸ MultiseriesExpansion.const_leadingMonomial)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(MultiseriesExpansion.mk .nil $f) =>
      return ⟨q(⟨0, List.replicate (List.length ($basis_hd :: $basis_tl)) 0⟩),
        q(MultiseriesExpansion.nil_leadingMonomial)⟩
    | ~q(MultiseriesExpansion.mk (.cons $exp $coef $tl) $f) =>
      let ⟨coef_t, coef_h_eq⟩ ← getLeadingMonomialWithProof coef
      match coef_t with
      | ~q(⟨$coef_coef, $coef_exps⟩) =>
        return ⟨q(⟨$coef_coef, $exp :: $coef_exps⟩),
          q(MultiseriesExpansion.cons_leadingMonomial' $coef_h_eq)⟩
      | _ =>
        return ⟨q(⟨Monomial.coef (MultiseriesExpansion.leadingMonomial $coef),
          $exp :: Monomial.unit (MultiseriesExpansion.leadingMonomial $coef)⟩),
          q(MultiseriesExpansion.cons_leadingMonomial)⟩
    | _ =>
      return ⟨q(MultiseriesExpansion.leadingMonomial $ms), q(rfl)⟩
  | _ => panic! "Unexpected basis in getLeadingMonomial"

/-- Proves that the coefficient of the leading monomial of a trimmed multiseries is positive.
Return `none` if cannot prove it. -/
def getLeadingMonomialCoefPos {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis)) :
    TacticM (Option Q(0 < (MultiseriesExpansion.leadingMonomial $ms).coef)) := do
  match basis with
  | ~q(List.nil) =>
    let .pos pf ← compareReal q(($ms).toReal) | return .none
    return .some pf
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(MultiseriesExpansion.mk .nil $f) => return .none
    | _ =>
      let ⟨rhs, h_eq⟩ ← getLeadingMonomialWithProof ms
      let ~q(⟨$coef, $exps⟩) := rhs | return .none
      let .pos pf ← compareReal coef | return .none
      return .some q(Eq.subst (motive := fun (x : Monomial) ↦ 0 < x.coef) (Eq.symm $h_eq) $pf)
  | _ => panic! "Unexpected basis in getLeadingMonomialCoefPos"

/-- Result of checking for a `x : UnitMonomial` if `x.FirstNonzeroIsPos` or `x.FirstNonzeroIsNeg`
or `x.AllZero`. -/
inductive FirstIsResult (x : Q(UnitMonomial))
| zero (pf : Q(($x).AllZero))
| pos (pf : Q(($x).FirstNonzeroIsPos))
| neg (pf : Q(($x).FirstNonzeroIsNeg))

open UnitMonomial

/-- Given a list `x`, checks if `x.FirstNonzeroIsPos` or `x.FirstNonzeroIsNeg` or `x.AllZero`. -/
partial def getFirstIs (x : Q(UnitMonomial)) : TacticM (FirstIsResult x) := do
  match x with
  | ~q(List.nil) => return .zero q(AllZero.nil)
  | ~q(List.cons $hd $tl) =>
    match ← compareReal q($hd) with
    | .pos h_hd => return .pos q(FirstNonzeroIsPos.of_head $tl $h_hd)
    | .neg h_hd => return .neg q(FirstNonzeroIsNeg.of_head $tl $h_hd)
    | .zero h_hd =>
      match ← getFirstIs q($tl) with
      | .zero h_tl => return .zero q(AllZero.of_tail $h_hd $h_tl)
      | .pos h_tl => return .pos q(FirstNonzeroIsPos.of_tail $h_hd $h_tl)
      | .neg h_tl => return .neg q(FirstNonzeroIsNeg.of_tail $h_hd $h_tl)
  | ~q(List.replicate $n 0) => return .zero q(AllZero.replicate)
  | _ => panic! "Unexpected list in getFirstIs"

/-- Result of checking for a `x : UnitMonomial` if `x.FirstNonzeroIsPos`. -/
inductive FirstNonzeroIsPosResult (x : Q(UnitMonomial))
| right (pf : Q(FirstNonzeroIsPos $x))
| wrong (pf : Q(¬ FirstNonzeroIsPos $x))

/-- Given a list `x`, checks if `x.FirstNonzeroIsPos`. -/
def getFirstNonzeroIsPos (x : Q(UnitMonomial)) : TacticM (FirstNonzeroIsPosResult x) := do
  match ← getFirstIs x with
  | .pos pf => return .right pf
  | .neg pf => return .wrong q(($pf).not_FirstNonzeroIsPos)
  | .zero pf => return .wrong q(($pf).not_FirstNonzeroIsPos)

end Tactic.ComputeAsymptotics

import Mathlib.Tactic.Tendsto.Multiseries.Main
import Mathlib.Tactic.Tendsto.Meta.MS
import Mathlib.Tactic.Tendsto.Meta.ElimDestruct
import Mathlib.Tactic.Tendsto.Meta.CompareReal

open Lean Meta Elab Tactic Qq

namespace TendstoTactic

/-- Given `ms`, computes its leading term `t`. -/
partial def getLeadingTerm {basis : Q(Basis)} (ms : Q(PreMS $basis)) : MetaM Q(MS.Term) := do
  match basis with
  | ~q(List.nil) =>
    return q(⟨$ms, List.nil⟩)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.nil) =>
      throwError "Unexpected ms = nil in getLeadingTerm"
    | ~q(PreMS.cons $hd $tl) =>
      match hd with
      | ~q(($exp, $coef)) =>
        match ← getLeadingTerm coef with
        | ~q(⟨$coef_coef, $coef_exps⟩) =>
          return q(⟨$coef_coef, $exp :: $coef_exps⟩)
        | _ => throwError "Unexpected pre in getLeadingTerm"
      | _ => throwError "Unexpected head in getLeadingTerm"
    | _ => throwError "Unexpected ms in getLeadingTerm"

def getLeadingTermWithProof {basis : Q(Basis)} (ms : Q(PreMS $basis)) :
    MetaM ((t : Q(MS.Term)) × Q(PreMS.leadingTerm $ms = $t)) := do
  let rhs ← getLeadingTerm ms
  let e ← mkFreshExprMVar q(PreMS.leadingTerm $ms = $rhs)
  e.mvarId!.applyRfl
  return ⟨rhs, e⟩

inductive FirstIsResult (x : Q(List ℝ))
| zero (pf : Q(MS.Term.AllZero $x))
| pos (pf : Q(MS.Term.FirstIsPos $x))
| neg (pf : Q(MS.Term.FirstIsNeg $x))

partial def getFirstIs (x : Q(List ℝ)) : TacticM (FirstIsResult x) := do
  match x with
  | ~q(List.nil) => return .zero q(MS.Term.AllZero_of_nil)
  | ~q(List.cons $hd $tl) =>
    match ← compareReal hd with
    | .pos h_hd => return .pos q(MS.Term.FirstIsPos_of_head $tl $h_hd)
    | .neg h_hd => return .neg q(MS.Term.FirstIsNeg_of_head $tl $h_hd)
    | .zero h_hd =>
      return match ← getFirstIs tl with
      | .zero h_tl => .zero q(MS.Term.AllZero_of_tail $h_hd $h_tl)
      | .pos h_tl => .pos q(MS.Term.FirstIsPos_of_tail $h_hd $h_tl)
      | .neg h_tl => .neg q(MS.Term.FirstIsNeg_of_tail $h_hd $h_tl)

end TendstoTactic

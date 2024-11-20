import Mathlib.Tactic.Tendsto.Multiseries.Main
import Mathlib.Tactic.Tendsto.Meta.MS
import Mathlib.Tactic.Tendsto.Meta.ElimDestruct
import Mathlib.Tactic.Tendsto.Meta.CompareReal

open Lean Meta Elab Tactic Qq

namespace TendstoTactic

/-- Given `ms`, computes its leading term `t`. -/
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
      return match ← getFirstIs tl with
      | .zero h_tl => .zero q(Term.AllZero_of_tail $h_hd $h_tl)
      | .pos h_tl => .pos q(Term.FirstIsPos_of_tail $h_hd $h_tl)
      | .neg h_tl => .neg q(Term.FirstIsNeg_of_tail $h_hd $h_tl)

end TendstoTactic

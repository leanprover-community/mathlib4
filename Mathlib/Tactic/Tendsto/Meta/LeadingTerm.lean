import Mathlib.Tactic.Tendsto.Multiseries.Main
import Mathlib.Tactic.Tendsto.Meta.MS
import Mathlib.Tactic.Tendsto.Meta.ElimDestruct
import Mathlib.Tactic.Tendsto.Meta.CompareReal

open Lean Qq Meta Elab  Tactic TendstoTactic

/-- Given `ms`, computes its leading term `t`. -/
partial def getLeadingTerm {basis : Q(Basis)} (ms : Q(PreMS $basis)) : MetaM Q(MS.Term) := do
  match basis with
  | ~q(List.nil) =>
    return q(⟨$ms, List.nil⟩)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.nil) =>
      throwError "ms = nil"
      -- let exps : List Q(ℝ) := List.range basis.length |>.map fun _ => q(0)
    | ~q(PreMS.cons $hd $tl) =>
      match hd with
      | ~q( ($exp, $coef) ) =>
        let pre ← getLeadingTerm coef
        match pre with
        | ~q(MS.Term.mk $pre_coef $pre_exps) =>
          return q(⟨$pre_coef, $exp :: $pre_exps⟩)
        | _ => throwError "strange pre"
      | _ => throwError "strange head"
    | _ => throwError "strange PreMS"

def getLeadingTermWithProof {basis : Q(Basis)} (ms : Q(PreMS $basis)) : MetaM (Q(MS.Term) × Expr) := do
  let rhs ← getLeadingTerm ms
  let target : Q(Prop) := q(PreMS.leadingTerm $ms = $rhs)
  let e ← mkFreshExprMVar target
  e.mvarId!.applyRfl
  return (rhs, e)

inductive FirstIsResult (x : Q(List ℝ))
| zero (pf : Q(MS.Term.AllZero $x))
| pos (pf : Q(MS.Term.FirstIsPos $x))
| neg (pf : Q(MS.Term.FirstIsNeg $x))

partial def getFirstIs (x : Q(List ℝ)) : TacticM (FirstIsResult x) := do
  match x with
  | ~q(List.nil) =>
    return .zero q(MS.Term.AllZero_of_nil)
  | ~q(List.cons $hd $tl) =>
    let comp_res ← compareReal hd
    match comp_res with
    | .pos h_hd =>
      return .pos q(MS.Term.FirstIsPos_of_head $tl $h_hd)
    | .neg h_hd =>
      return .neg q(MS.Term.FirstIsNeg_of_head $tl $h_hd)
    | .zero h_hd =>
      let rl_res ← getFirstIs tl
      match rl_res with
      | .zero h_tl =>
        return .zero q(MS.Term.AllZero_of_tail $h_hd $h_tl)
      | .pos h_tl =>
        return .pos q(MS.Term.FirstIsPos_of_tail $h_hd $h_tl)
      | .neg h_tl =>
        return .neg q(MS.Term.FirstIsNeg_of_tail $h_hd $h_tl)

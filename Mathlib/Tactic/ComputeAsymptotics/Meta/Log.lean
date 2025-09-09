/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ComputeAsymptotics.Lemmas
import Mathlib.Tactic.ComputeAsymptotics.Meta.BasisM
import Mathlib.Tactic.ComputeAsymptotics.Meta.Trimming
import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareMS

/-!
# TODO
-/

open Filter Topology Asymptotics Stream'.Seq

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

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

def createLogMS (arg : Q(ℝ)) (ms : MS) (h_trimmed : Q(PreMS.Trimmed $ms.val)) : BasisM MS := do
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
    let .some h_pos' ← getLeadingTermCoefPos ms.val
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
    return MS.log ms h_trimmed h_pos' h_last

end ComputeAsymptotics

/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Meta.Trimming

/-!
# TODO
-/

namespace TendstoTactic

namespace MS

open Lean Meta Elab Tactic

open Topology Filter Asymptotics
open Qq

inductive CompareListsResult (x y : Q(List ℝ))
| lt (h : Q($x < $y))
| gt (h : Q($y < $x))
| eq (h : Q($x = $y))

-- #eval [1, 2] < []

partial def compareLists (x y : Q(List ℝ)) : TacticM <| CompareListsResult x y := do
  match x, y with
  | ~q(List.nil), ~q(List.nil) =>
    return .eq q(sorry)
  | ~q(List.cons _ _), ~q(List.nil) =>
    panic! "compareLists: lists of different lengths"
  | ~q(List.nil), ~q(List.cons _ _) =>
    panic! "compareLists: lists of different lengths"
  | ~q(List.cons $x_hd $x_tl), ~q(List.cons $y_hd $y_tl) =>
    match ← compareReal q($x_hd - $y_hd) with
    | .pos h => return .gt q(sorry)
    | .neg h => return .lt q(sorry)
    | .zero h =>
      match ← compareLists x_tl y_tl with
      | .lt h => return .lt q(sorry)
      | .gt h => return .gt q(sorry)
      | .eq h => return .eq q(sorry)

inductive CompareResult (f g : Q(ℝ → ℝ))
| lt (h : Q($f =o[atTop] $g))
| gt (h : Q($g =o[atTop] $f))
| eq (c : Q(ℝ)) (hc : Q($c ≠ 0)) (h : Q($f ~[atTop] $c • $g))

-- assume that `x.basis = ... ++ y.basis`
def compare (x y : MS)
    (hx_trimmed : Q(PreMS.Trimmed $x.val))
    (hy_trimmed : Q(PreMS.Trimmed $y.val)) :
    TacticM <| CompareResult x.f y.f := do
  let ⟨tx, _⟩ ← getLeadingTermWithProof x.val
  let ⟨ty, _⟩ ← getLeadingTermWithProof y.val
  let ~q(⟨$x_coef, $x_exps⟩) := tx | panic! "Unexpected x in compareLeadingTerms"
  let ~q(⟨$y_coef, $y_exps⟩) := ty | panic! "Unexpected y in compareLeadingTerms"
  let n : Nat := (← computeLength x.basis) - (← computeLength y.basis)
  let zeros ← replicate n q(0 : ℝ)
  let y_exps' := ← reduceAppend (α := q(ℝ)) q($zeros) q($y_exps)
  let res ← compareLists q($x_exps) q($y_exps')
  match res with
  | .lt h =>
    return .lt q(sorry)
  | .gt h =>
    return .gt q(sorry)
  | .eq h =>
    let c : Q(ℝ) := q($x_coef / $y_coef)
    let hc ← CompareReal.proveNeZero c
    return .eq c hc q(sorry)

end MS

end TendstoTactic

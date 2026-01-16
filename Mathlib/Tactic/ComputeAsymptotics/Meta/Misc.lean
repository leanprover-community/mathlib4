/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.LogBasis
public import Qq

/-!
# Auxiliary meta-functions for `Basis` and `LogBasis`
-/

public meta section

namespace ComputeAsymptotics

open Lean Elab Meta Qq

/-- Computes the length of a `Basis`. -/
partial def computeLength (b : Q(Basis)) : MetaM Nat := do
  match b with
  | ~q(List.nil) => return 0
  | ~q(List.cons $basis_hd $basis_tl) => return 1 + (← computeLength basis_tl)
  | _ => panic! s!"computeLength: unexpected basis: {← ppExpr b}"

partial def getNth {α : Q(Type)} (li : Q(List $α)) (n : Nat) :
    MetaM <| Q($α) := do
  match n, li with
  | 0, ~q(List.cons $hd $tl) => return hd
  | n + 1, ~q(List.cons $hd $tl) => return ← getNth tl n
  | _, _ => panic! s!"getNth: unexpected list: {← ppExpr li}"

/-- Returns the last element of a list. -/
partial def getLast {α : Q(Type)} (li : Q(List $α)) : MetaM <| Option <| Q($α) := do
  match li with
  | ~q(List.nil) => return .none
  | ~q(List.cons $hd $tl) =>
    match tl with
    | ~q(List.cons $tl_hd $tl_tl) => return ← getLast tl
    | ~q(List.nil) => return .some hd
  | _ => panic! s!"getLast: unexpected list: {← ppExpr li}"

def mkFin (n m : Q(ℕ)) : MetaM Q(Fin $m) := do
  let hn : Q($n < $m) := ← mkDecideProof q($n < $m)
  return q(Fin.mk $n $hn)

/-- Returns the index (as a `Nat`) of the first element equal to `val` in a list. -/
partial def findIndexAux {α : Q(Type)} (li : Q(List $α)) (val : Q($α)) :
    MetaM Nat := do
  match li with
  | ~q(List.nil) => panic! "findIndexAux: not found"
  | ~q(List.cons $hd $tl) =>
    if hd == val then
      return 0
    else
      return 1 + (← findIndexAux tl val)
  | _ => panic! s!"findIndexAux: unexpected list: {← ppExpr li}"

/-- Returns the index (as a `Fin (List.length li)` of the first element equal to `val` in a list. -/
partial def findIndex {α : Q(Type)} (li : Q(List $α)) (val : Q($α)) :
    MetaM Q(Fin (List.length $li)) := do
  haveI n : Q(Nat) := mkNatLit (← findIndexAux li val)
  return ← mkFin q($n) q(List.length $li)

/-- Assuming `basis = left ++ right`, returns `left`. -/
def expressAsAppend (basis right : Q(Basis)) : MetaM Q(Basis) := do
  let leftLength := (← computeLength basis) - (← computeLength right)
  go basis leftLength
where
  /-- Helper function for `expressAsAppend`. -/
  go (li : Q(Basis)) (depth : Nat) : MetaM Q(Basis) := do
  match depth with
  | 0 => return q(List.nil)
  | d + 1 =>
    let ~q(List.cons $hd $tl) := li | panic! s!"expressAsAppend: unexpected basis: {← ppExpr li}"
    let tl' ← go tl d
    return q(List.cons $hd $tl')

/-- Replicates an element `x` `n` times in a list. -/
def replicate {α : Q(Type)} (n : Nat) (x : Q($α)) : MetaM Q(List $α) := do
  match n with
  | 0 => return q(List.nil)
  | n + 1 =>
    let tl ← replicate n x
    return q(List.cons $x $tl)

/-- Given `left : List α` and `right : List α`, returns `left ++ right` without
using `List.append`. -/
partial def reduceAppend {α : Q(Type)} (left right : Q(List $α)) : MetaM Q(List $α) := do
  match left with
  | ~q(List.nil), _ => return right
  | ~q(List.cons $left_hd $left_tl) =>
    let tl ← reduceAppend left_tl right
    return q(List.cons $left_hd $tl)
  | _ => panic! s!"Unexpected left in reduceAppend: {← ppExpr left}"

mutual

  /-- Reduces a `BasisExtension` to a normal form. -/
  partial def reduceBasisExtension {basis : Q(Basis)} (ex : Q(BasisExtension $basis)) :
      MetaM Q(Basis) := do
    match basis, ex with
    | ~q(List.nil), ~q(BasisExtension.nil) => return q(List.nil)
    | ~q(List.cons $basis_hd $basis_tl), ~q(BasisExtension.keep _ $ex_tl) =>
      let tl ← reduceBasisExtension ex_tl
      return q(List.cons $basis_hd $tl)
    | _, ~q(BasisExtension.insert $f $ex_tl) =>
      let tl ← reduceBasisExtension ex_tl
      return q(List.cons $f $tl)
    | _ => panic! s!"Unexpected ex in reduceBasisExtension: {← ppExpr ex}"

  /-- Reduces a `Basis` to a normal form. -/
  partial def reduceBasis (basis : Q(Basis)) : MetaM Q(Basis) := do
    match basis with
    | ~q(List.nil) => return q(List.nil)
    | ~q(List.cons $hd $tl) =>
      let tl' ← reduceBasis tl
      return q(List.cons $hd $tl')
    | ~q(BasisExtension.getBasis ($ex : BasisExtension $basis')) =>
      let basis'' ← reduceBasis basis'
      haveI : $basis =Q $basis' := ⟨⟩
      return ← @reduceBasisExtension basis'' ex
    | ~q($left ++ $right) =>
      let left' ← reduceBasis left
      let right' ← reduceBasis right
      return ← reduceAppend (α := q(ℝ → ℝ)) left' right'
    | _ =>
      panic! s!"Unexpected basis in reduceBasis: {← ppExpr basis}"

end

set_option linter.unusedVariables false in
/-- Reduces a `LogBasis` to a normal form. -/
partial def reduceLogBasis {basis : Q(Basis)} (logBasis : Q(LogBasis $basis)) :
    MetaM Q(LogBasis $basis) := do
  match logBasis.getAppFnArgs with
  | (``LogBasis.nil, _) => return logBasis
  | (``LogBasis.single, _) => return logBasis
  | (``LogBasis.cons, #[(basis_hd : Q(ℝ → ℝ)), (basis_tl_hd : Q(ℝ → ℝ)), (basis_tl_tl : Q(Basis)),
      (logBasis_tl : Q(LogBasis ($basis_tl_hd :: $basis_tl_tl))),
      (ms : Q(PreMS ($basis_tl_hd :: $basis_tl_tl)))]) =>
    have : $basis =Q $basis_hd :: $basis_tl_hd :: $basis_tl_tl := ⟨⟩
    let basis_tl_tl' ← reduceBasis basis_tl_tl
    let logBasis_tl' ← reduceLogBasis logBasis_tl
    have : $basis_tl_tl =Q $basis_tl_tl' := ⟨⟩
    return q(LogBasis.cons $basis_hd $basis_tl_hd $basis_tl_tl' $logBasis_tl' $ms)
  | (``LogBasis.tail, #[(basis_hd : Q(ℝ → ℝ)), (basis_tl : Q(Basis)),
      (logBasis_arg : Q(LogBasis ($basis_hd :: $basis_tl)))]) =>
    have : $basis =Q $basis_tl := ⟨⟩
    let logBasis_arg' ← reduceLogBasis logBasis_arg
    match basis_tl, logBasis_arg' with
    | ~q(List.nil), ~q(LogBasis.single _) => return q(LogBasis.nil)
    | ~q(List.cons $basis_tl_hd $basis_tl_tl), ~q(LogBasis.cons _ _ _ $logBasis_tl _) =>
      return q($logBasis_tl)
    | _ => panic! "Unexpected basis_tl or logBasis_arg' in reduceLogBasis"
  | (``LogBasis.extendBasisMiddle, #[(right_hd : Q(ℝ → ℝ)), (left : Q(Basis)),
      (right_tl : Q(Basis)), (f : Q(ℝ → ℝ)),
      (logBasis_arg : Q(LogBasis ($left ++ $right_hd :: $right_tl))),
      (ms : Q(PreMS ($right_hd :: $right_tl)))]) =>
    have : $basis =Q $left ++ $f :: $right_hd :: $right_tl := ⟨⟩
    let logBasis_arg' ← reduceLogBasis logBasis_arg
    have : $logBasis_arg' =Q $logBasis_arg := ⟨⟩
    match left with
    | ~q(List.nil) => return q(LogBasis.cons _ _ _ $logBasis_arg' $ms)
    | ~q(List.cons $left_hd $left_tl) =>
      match left_tl with
      | ~q(List.nil) =>
        match logBasis_arg' with
        | ~q(LogBasis.cons _ _ _ $logBasis_tl $ms') =>
          return q(LogBasis.cons _ _ _
            (LogBasis.extendBasisMiddle (left := []) $f $logBasis_tl $ms)
            (PreMS.extendBasisMiddle (left := []) $f $ms'))
        | _ => unreachable!
      | ~q(List.cons $left_tl_hd $left_tl_tl) =>
        match logBasis_arg' with
        | ~q(LogBasis.cons _ _ _ $logBasis_tl $ms') =>
          return q(LogBasis.cons $left_hd $left_tl_hd ($left_tl_tl ++ $f :: $right_hd :: $right_tl)
            (LogBasis.extendBasisMiddle (left := $left_tl_hd :: $left_tl_tl) $f $logBasis_tl $ms)
            (PreMS.extendBasisMiddle (left := $left_tl_hd :: $left_tl_tl) $f $ms'))
        | _ => unreachable!
      | _ => panic! "Unexpected left_tl in reduceLogBasis"
    | _ => panic! "Unexpected left in reduceLogBasis"
  | (``LogBasis.extendBasisEnd, #[(basis_hd : Q(ℝ → ℝ)), (basis_tl : Q(Basis)), (f : Q(ℝ → ℝ)),
      (logBasis_arg : Q(LogBasis ($basis_hd :: $basis_tl))),
      (ms : Q(PreMS ([$f])))]) =>
    have : $basis =Q $basis_hd :: $basis_tl ++ [$f] := ⟨⟩
    let logBasis_arg' ← reduceLogBasis logBasis_arg
    have : $logBasis_arg' =Q $logBasis_arg := ⟨⟩
    match basis_tl, logBasis_arg' with
    | ~q(List.nil), ~q(LogBasis.single _) => return q(LogBasis.cons _ _ _ (.single _) $ms)
    | ~q(List.cons $basis_tl_hd $basis_tl_tl), ~q(LogBasis.cons _ _ _ $logBasis_tl $ms') =>
      return q(LogBasis.cons $basis_hd $basis_tl_hd ($basis_tl_tl ++ [$f])
        (LogBasis.extendBasisEnd $f $logBasis_tl $ms) (PreMS.extendBasisEnd _ $ms'))
    | _ => panic! "Unexpected basis_tl or logBasis_arg' in reduceLogBasis"
  | (``LogBasis.insertLastLog, #[(basis_hd : Q(ℝ → ℝ)), (basis_tl : Q(Basis)),
      (logBasis_arg : Q(LogBasis ($basis_hd :: $basis_tl)))]) =>
    let .some lastElem ← getLast (α := q(ℝ → ℝ)) q($basis_hd :: $basis_tl) | unreachable!
    have : $basis =Q $basis_hd :: $basis_tl ++ [Real.log ∘ $lastElem] := ⟨⟩
    let logBasis' : Q(LogBasis $basis) := q(LogBasis.extendBasisEnd (Real.log ∘ $lastElem)
      $logBasis_arg (PreMS.monomial [Real.log ∘ $lastElem] 0))
    reduceLogBasis logBasis'
  | _ => panic! "Unexpected logBasis in reduceLogBasis"

end ComputeAsymptotics

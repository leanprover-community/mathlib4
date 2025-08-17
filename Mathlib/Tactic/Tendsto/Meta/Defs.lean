/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries
import Qq

/-!
# TODO
-/

namespace TendstoTactic.PreMS

open scoped Topology

-- I don't want to define them earlier because I was enjoying Stream'.Seq API available for `nil`
-- and `cons` when proving thing in `Multiseries` folder. On the meta level I need them to work only
-- with multiseries without heavy parsing.

def nil {basis_hd} {basis_tl} : PreMS (basis_hd :: basis_tl) := .nil

def cons {basis_hd} {basis_tl} (hd : (ℝ × PreMS basis_tl)) (tl : PreMS (basis_hd :: basis_tl)) :
    PreMS (basis_hd :: basis_tl) := .cons hd tl

open Stream'.Seq

theorem nil_of_destruct {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h_destruct : destruct ms = .none) :
    ms = PreMS.nil :=
  Stream'.Seq.destruct_eq_none h_destruct

theorem cons_of_destruct {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {hd : ℝ × PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_destruct : destruct ms = .some (hd, tl)) :
    ms = PreMS.cons hd tl :=
  Stream'.Seq.destruct_eq_cons h_destruct

open Filter in
lemma nil_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    (h : PreMS.Approximates (@PreMS.nil basis_hd basis_tl) f) : Tendsto f atTop (𝓝 0) := by
  apply PreMS.Approximates_nil at h
  exact h.tendsto

end PreMS

open Lean Elab Meta Qq

partial def computeLength (b : Q(Basis)) : MetaM Nat := do
  match b with
  | ~q(List.nil) => return 0
  | ~q(List.cons $basis_hd $basis_tl) => return 1 + (← computeLength basis_tl)
  | _ => panic! s!"computeLength: unexpected basis: {← ppExpr b}"

def replicate {α : Q(Type)} (n : Nat) (x : Q($α)) : MetaM Q(List $α) := do
  match n with
  | 0 => return q(List.nil)
  | n + 1 =>
    let tl ← replicate n x
    return q(List.cons $x $tl)

partial def reduceAppend {α : Q(Type)} (left right : Q(List $α)) : MetaM Q(List $α) := do
  match left with
  | ~q(List.nil), _ => return right
  | ~q(List.cons $left_hd $left_tl) =>
    let tl ← reduceAppend left_tl right
    return q(List.cons $left_hd $tl)
  | _ => panic! s!"Unexpected left in reduceAppend: {← ppExpr left}"

mutual

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

  partial def reduceBasis (basis : Q(Basis)) : MetaM Q(Basis) := do
    match basis with
    | ~q(List.nil) => return q(List.nil)
    | ~q(List.cons $hd $tl) =>
      let tl' ← reduceBasis tl
      return q(List.cons $hd $tl')
    | ~q(@BasisExtension.getBasis $basis' $ex) =>
      let basis'' ← reduceBasis basis'
      haveI : $basis =Q $basis' := ⟨⟩
      return ← @reduceBasisExtension basis'' ex
    | ~q($left ++ $right) =>
      let left' ← reduceBasis left
      let right' ← reduceBasis right
      return ← reduceAppend (α := q(ℝ → ℝ)) left' right'

end

-- partial def reduceLogBasis {basis : Q(Basis)} (logBasis : Q(LogBasis $basis)) :
--     MetaM Q(LogBasis $basis) := do
--   let ~q(List.cons $basis_hd $basis_tl) := basis | return logBasis
--   match logBasis with

end TendstoTactic

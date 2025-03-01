/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries

/-!
# TODO
-/

namespace TendstoTactic.PreMS

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
    (h : PreMS.Approximates (@PreMS.nil basis_hd basis_tl) f) : Tendsto f atTop (nhds 0) := by
  apply PreMS.Approximates_nil at h
  exact h.tendsto


end TendstoTactic.PreMS

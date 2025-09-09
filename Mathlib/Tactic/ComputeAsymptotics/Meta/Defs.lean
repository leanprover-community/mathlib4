/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs

/-!
# TODO
-/

namespace ComputeAsymptotics.PreMS

open scoped Topology

-- I don't want to define them earlier because I was enjoying Stream'.Seq API available for `nil`
-- and `cons` when proving thing in `Multiseries` folder. On the meta level I need them to work only
-- with multiseries without heavy parsing.

/-- Multiseries representing the empty multiseries. -/
def nil {basis_hd} {basis_tl} : PreMS (basis_hd :: basis_tl) := .nil

/-- Multiseries representing the multiseries with a head and a tail. -/
def cons {basis_hd} {basis_tl} (hd : (ℝ × PreMS basis_tl)) (tl : PreMS (basis_hd :: basis_tl)) :
    PreMS (basis_hd :: basis_tl) := .cons hd tl

open Filter in
lemma nil_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    (h : PreMS.Approximates (@PreMS.nil basis_hd basis_tl) f) : Tendsto f atTop (𝓝 0) := by
  apply PreMS.Approximates_nil at h
  exact h.tendsto

end PreMS

end ComputeAsymptotics

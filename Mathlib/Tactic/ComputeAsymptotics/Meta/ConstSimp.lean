/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Meta.ConstSimpAttribute
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations

/-!
# TODO
-/

@[expose] public section

open Filter Asymptotics Stream' Seq

namespace Tactic.ComputeAsymptotics.MultiseriesExpansion

section Const

-- @[MultiseriesExpansion_const low]
-- theorem real_toReal (c : ℝ) : MultiseriesExpansion.toReal c = c := by
--   rfl

@[MultiseriesExpansion_const]
theorem const_const (c : ℝ) : (MultiseriesExpansion.const [] c).toReal = c := by
  simp [MultiseriesExpansion.const, ofReal, toReal]

@[MultiseriesExpansion_const]
theorem one_const : (@MultiseriesExpansion.one []).toReal = 1 := by simp [one, const_const]

@[MultiseriesExpansion_const]
theorem neg_const (x : MultiseriesExpansion []) : (x.neg).toReal = -x.toReal := by
  simp [neg, mulConst, toReal, ofReal]

@[MultiseriesExpansion_const]
theorem add_const (x y : MultiseriesExpansion []) :
    (MultiseriesExpansion.add x y).toReal = x.toReal + y.toReal := by
  simp [add, ofReal, toReal]

@[MultiseriesExpansion_const]
theorem mul_const (x y : MultiseriesExpansion []) :
    (MultiseriesExpansion.mul x y).toReal = x.toReal * y.toReal := by
  simp [mul, toReal, ofReal]

@[MultiseriesExpansion_const]
theorem mulConst_const (x : MultiseriesExpansion []) (c : ℝ) :
    (MultiseriesExpansion.mulConst c x).toReal = c * x.toReal := by
  simp [mulConst, toReal, ofReal]

@[MultiseriesExpansion_const]
theorem inv_const (x : MultiseriesExpansion []) :
    (MultiseriesExpansion.inv x).toReal = (x.toReal)⁻¹ := by
  simp [inv, toReal, ofReal]

@[MultiseriesExpansion_const]
theorem pow_const (x : MultiseriesExpansion []) (a : ℝ) :
    (MultiseriesExpansion.pow x a).toReal = (x.toReal) ^ a := by
  simp [pow, toReal, ofReal]

@[MultiseriesExpansion_const]
theorem extendBasisEnd_const (f : ℝ → ℝ) (x : MultiseriesExpansion []) :
    (MultiseriesExpansion.extendBasisEnd f x) =
    MultiseriesExpansion.mk (.cons 0 x .nil) (fun _ ↦ x.toReal) := by
  simp [MultiseriesExpansion.extendBasisEnd, MultiseriesExpansion.const, Multiseries.const,
    toReal, ofReal]

@[MultiseriesExpansion_const]
theorem updateBasis_const (ms : MultiseriesExpansion []) (ex : BasisExtension []) :
    (MultiseriesExpansion.updateBasis ex ms) = MultiseriesExpansion.const _ ms.toReal := by
  cases ex with
  | nil =>
    simp [MultiseriesExpansion.updateBasis, BasisExtension.getBasis, MultiseriesExpansion.const,
      toReal, ofReal]
  | insert f ex_tl =>
    simp only [BasisExtension.getBasis, updateBasis, const_toFun, mk_eq_mk_iff_iff, const_seq,
      Multiseries.const, Multiseries.cons_eq_cons, and_true, true_and, const_toFun']
    rw [updateBasis_const]


-- @[MultiseriesExpansion_const]
-- theorem updateBasis_const_real (ms : ℝ) (ex : BasisExtension []) :
--     (MultiseriesExpansion.updateBasis ex ms) = MultiseriesExpansion.const _ ms := by
--   cases ex with
--   | nil =>
--     simp [MultiseriesExpansion.updateBasis, BasisExtension.getBasis,
--       MultiseriesExpansion.const, ofReal]
--   | insert f ex_tl =>
--     simp only [BasisExtension.getBasis, updateBasis, const_toFun, toReal, const,
--       Multiseries.const, ms_eq_mk_iff, mk_seq, Multiseries.cons_eq_cons, and_true, true_and,
--       mk_toFun]
--     rw [updateBasis_const]

@[MultiseriesExpansion_const]
theorem BasisExtension.nil_getBasis : BasisExtension.nil.getBasis = [] := rfl

@[MultiseriesExpansion_const]
theorem log_const (x : MultiseriesExpansion []) (logBasis : LogBasis []) :
    (MultiseriesExpansion.log logBasis x).toReal =
    Real.log x.toReal := by
  simp [MultiseriesExpansion.log, toReal]

@[MultiseriesExpansion_const]
theorem exp_const (x : MultiseriesExpansion []) :
    (MultiseriesExpansion.exp x).toReal = Real.exp x.toReal := by
  simp [exp, toReal, ofReal]

end Const

end Tactic.ComputeAsymptotics.MultiseriesExpansion

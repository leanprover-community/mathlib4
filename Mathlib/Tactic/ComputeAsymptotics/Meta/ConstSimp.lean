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

open Filter Asymptotics ComputeAsymptotics Stream' Seq

namespace ComputeAsymptotics.PreMS

section Const

@[PreMS_const]
theorem const_const (c : ℝ) : (PreMS.const [] c).toReal = c := by
  simp [PreMS.const, ofReal, toReal]

@[PreMS_const]
theorem one_const : (@PreMS.one []).toReal = 1 := by simp [one, const_const]

@[PreMS_const]
theorem neg_const (x : PreMS []) : (x.neg).toReal = -x.toReal := by
  simp [neg, mulConst, toReal, ofReal]

@[PreMS_const]
theorem add_const (x y : PreMS []) : (PreMS.add x y).toReal = x.toReal + y.toReal := by
  simp [add, ofReal, toReal]

@[PreMS_const]
theorem mul_const (x y : PreMS []) : (PreMS.mul x y).toReal = x.toReal * y.toReal := by
  simp [mul, toReal, ofReal]

@[PreMS_const]
theorem mulConst_const (x : PreMS []) (c : ℝ) : (PreMS.mulConst c x).toReal = c * x.toReal := by
  simp [mulConst, toReal, ofReal]

@[PreMS_const]
theorem inv_const (x : PreMS []) : (PreMS.inv x).toReal = (x.toReal)⁻¹ := by
  simp [inv, toReal]

@[PreMS_const]
theorem pow_const (x : PreMS []) (a : ℝ) :
    (PreMS.pow x a).toReal = (x.toReal) ^ a := by
  simp [pow, toReal]

@[PreMS_const]
theorem extendBasisEnd_const (f : ℝ → ℝ) (x : PreMS []) : (PreMS.extendBasisEnd f x) =
    PreMS.const [f] x := rfl

@[PreMS_const]
theorem updateBasis_const (ms : PreMS []) (ex : BasisExtension []) :
    (PreMS.updateBasis ex ms) = PreMS.const _ ms := by
  cases ex with
  | nil =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const, ofReal]
  | insert f ex_tl =>
    simp only [BasisExtension.getBasis, updateBasis, const_toFun, toReal, const, SeqMS.const,
      ms_eq_mk_iff, mk_seq, SeqMS.cons_eq_cons, and_true, true_and, mk_toFun]
    rw [updateBasis_const]

@[PreMS_const]
theorem updateBasis_const_real (ms : ℝ) (ex : BasisExtension []) :
    (PreMS.updateBasis ex ms) = PreMS.const _ ms := by
  cases ex with
  | nil =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const, ofReal]
  | insert f ex_tl =>
    simp only [BasisExtension.getBasis, updateBasis, const_toFun, toReal, const, SeqMS.const,
      ms_eq_mk_iff, mk_seq, SeqMS.cons_eq_cons, and_true, true_and, mk_toFun]
    rw [updateBasis_const]


@[PreMS_const]
theorem BasisExtension.nil_getBasis : BasisExtension.nil.getBasis = [] := rfl

@[PreMS_const]
theorem log_const (x : PreMS []) (logBasis : LogBasis []) : (PreMS.log logBasis x).toReal =
    Real.log x.toReal := by
  simp [PreMS.log, toReal]

@[PreMS_const]
theorem exp_const (x : PreMS []) : (PreMS.exp x).toReal = Real.exp x.toReal := by
  simp [exp, toReal]

end Const

end ComputeAsymptotics.PreMS

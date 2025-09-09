/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ComputeAsymptotics.Meta.ConstSimpAttribute
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations

/-!
# TODO
-/

open Filter Asymptotics ComputeAsymptotics Stream' Seq

namespace ComputeAsymptotics.PreMS

section Const

@[PreMS_const]
theorem const_const (c : ℝ) : PreMS.const [] c = c := rfl

@[PreMS_const]
theorem one_const : PreMS.one [] = 1 := rfl

@[PreMS_const]
theorem neg_const (x : PreMS []) : (x.neg) = -x := by simp [PreMS.neg, PreMS.mulConst]

@[PreMS_const]
theorem add_const (x y : PreMS []) : (PreMS.add x y) = x + y := rfl

@[PreMS_const]
theorem mul_const (x y : PreMS []) : (PreMS.mul x y) = x * y := by simp [PreMS.mul]

@[PreMS_const]
theorem mulConst_const (x : PreMS []) (c : ℝ) : (PreMS.mulConst x c) = x * c := rfl

@[PreMS_const]
theorem inv_const (x : PreMS []) : (PreMS.inv x) = x⁻¹ := rfl

@[PreMS_const]
theorem pow_const (x : PreMS []) (a : ℝ) : (PreMS.pow x a) = x^a := rfl

@[PreMS_const]
theorem extendBasisEnd_const (f : ℝ → ℝ) (x : PreMS []) : (PreMS.extendBasisEnd f x) =
    PreMS.const [f] x := rfl

@[PreMS_const]
theorem updateBasis_const (ms : PreMS []) (ex : BasisExtension []) :
    (PreMS.updateBasis ex ms) = PreMS.const _ ms := by
  cases ex with
  | nil =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
  | insert f ex_tl =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
    rw [updateBasis_const]

@[PreMS_const]
theorem updateBasis_const_real (ms : ℝ) (ex : BasisExtension []) :
    (PreMS.updateBasis ex ms) = PreMS.const _ ms := by
  cases ex with
  | nil =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
  | insert f ex_tl =>
    simp [PreMS.updateBasis, BasisExtension.getBasis, PreMS.const]
    rw [updateBasis_const]

@[PreMS_const]
theorem BasisExtension.nil_getBasis : BasisExtension.nil.getBasis = [] := rfl

@[PreMS_const]
theorem log_const (x : PreMS []) (logBasis : LogBasis []) : (PreMS.log logBasis x) =
    Real.log x := by
  simp [PreMS.log]

@[PreMS_const]
theorem exp_const (x : PreMS []) : (PreMS.exp x) = Real.exp x := rfl

end Const

end ComputeAsymptotics.PreMS

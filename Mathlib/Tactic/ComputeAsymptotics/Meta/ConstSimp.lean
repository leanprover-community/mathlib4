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
theorem const_const (c : ℝ) : (PreMS.const [] c).toReal = c := rfl

@[PreMS_const]
theorem one_const : (PreMS.one []).toReal = 1 := rfl

@[PreMS_const]
theorem neg_const (x : PreMS []) : (x.neg).toReal = Neg.neg (α := ℝ) x.toReal := by
  simp [neg, mulConst, toReal]

@[PreMS_const]
theorem add_const (x y : PreMS []) : (PreMS.add x y).toReal = x.toReal + y.toReal := rfl

@[PreMS_const]
theorem mul_const (x y : PreMS []) : (PreMS.mul x y).toReal = x.toReal * y.toReal := by
  simp [mul, toReal]

@[PreMS_const]
theorem mulConst_const (x : PreMS []) (c : ℝ) : (PreMS.mulConst x c).toReal = c * x.toReal := rfl

@[PreMS_const]
theorem inv_const (x : PreMS []) : (PreMS.inv x).toReal = Inv.inv (α := ℝ) x.toReal := rfl

@[PreMS_const]
theorem pow_const (x : PreMS []) (a : ℝ) :
    (PreMS.pow x a).toReal = HPow.hPow (α := ℝ) (β := ℝ) x.toReal a := rfl

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

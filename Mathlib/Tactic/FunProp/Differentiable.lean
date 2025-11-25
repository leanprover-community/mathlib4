/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Analysis.Calculus.FDeriv.Basic
public meta import Mathlib.Analysis.Calculus.FDeriv.Comp
public meta import Mathlib.Analysis.Calculus.FDeriv.Prod
public meta import Mathlib.Analysis.Calculus.FDeriv.Pi
public meta import Mathlib.Analysis.Calculus.FDeriv.Add
public meta import Mathlib.Analysis.Calculus.FDeriv.Mul
public meta import Mathlib.Analysis.Calculus.Deriv.Inv
public meta import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public meta import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public meta import Mathlib.Tactic.FunProp

deprecated_module
  "fun_prop knows about Differentiable(At/On) directly; no need to import this file any more"
  (since := "2025-06-25")

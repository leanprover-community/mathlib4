/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import Mathlib.SetTheory.ZFC.Constructible.FiniteStageInternalOrder
public import Mathlib.SetTheory.ZFC.Constructible.FormulaDefinedSet
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryGraphSystem

/-!
# The constructible universe

This directory defines the constructible hierarchy as internally represented `ZFSet`s, proves
that its stages agree with first-order definability, and constructs coherent internal well-orders
of all stages. The membership structure on the constructible universe is consequently a model of
the canonical first-order theory ZFC.

Each stage `LStageZF α` is an actual `ZFSet`; only the union `L` of all ordinal-indexed stages is
represented externally as a `Set ZFSet`. Successor stages use the internally constructed operation
`DefZF`, while limit stages use Replacement followed by internal union.

The proof proceeds through the following interfaces:

* an intrinsically scoped formula syntax and its equivalence with Mathlib's first-order formulas;
* Gödel operations and rudimentary relation graphs realizing `DefZF` internally;
* reflection and bounding arguments giving the Separation and Replacement schemes in `L`;
* internally represented, coherent well-orders of all stages, yielding Choice in `L`.

## Main declarations

- `Constructible.LStageZF`: the internally represented constructible hierarchy.
- `Constructible.L`: the class of constructible sets.
- `Constructible.Model.LCarrier`: the membership structure carried by `L`.
- `Constructible.Model.lCarrier_models_ZF`: `L` is a model of ZF.
- `Constructible.Model.lCarrier_models_ZFC`: `L` is a model of ZFC.
-/

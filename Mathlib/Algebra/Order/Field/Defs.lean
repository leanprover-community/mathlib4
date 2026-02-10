/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module -- shake: keep-all

public import Mathlib.Tactic.Linter.DeprecatedModule
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Util.CompileInductive

deprecated_module
"for `[LinearOrderedSemifield]`, use `[Semifield K] [LinearOrder K] [IsStrictOrderedRing K]` \
instead.
for `[LinearOrderedField]`, use `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` instead."
(since := "2025-10-30")

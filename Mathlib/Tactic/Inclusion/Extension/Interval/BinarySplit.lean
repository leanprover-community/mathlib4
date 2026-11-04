/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Binary splitting of intervals

This file defines the shared binary splitting parameter and builder.
-/

public section

open Lean Qq

namespace Inclusion.Interval

/-- The maximum depth of binary splitting of bounded intervals. -/
@[inclusion_param]
meta def binarySplitParam : InclusionParamDecl where
  name := `binSplit
  type := q(ℕ)

/-- Construct the binary-splitting cover. -/
@[inline]
meta def mkBinarySplitCover {u v : Level} {Iα : Q(Type u)} {α : Q(Type v)}
    {inst : Q(ToSet $Iα $α)} (cover : Q(ℕ → @Cover.{0} $Iα $α $inst)) :
    InclusionM (Option Expr) := do
  return (← InclusionM.getParam? `binSplit).map (mkApp cover)

end Inclusion.Interval

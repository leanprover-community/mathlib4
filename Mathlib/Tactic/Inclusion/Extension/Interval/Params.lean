/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Parameters for interval inclusion families

This file defines parameters shared by the interval based inclusion families.
-/

public meta section

open Lean Qq

namespace Inclusion.Interval

/-- The maximum depth of binary splitting of bounded intervals. -/
@[inclusion_param]
def binarySplitParam : InclusionParamDecl where
  name := `binSplit
  type := q(ℕ)

/-- Construct the binary-splitting cover. -/
def mkBinarySplitCover (cover : Expr) : InclusionM (Option Expr) := do
  return (← InclusionM.getParam? `binSplit).map (mkApp cover)

end Inclusion.Interval

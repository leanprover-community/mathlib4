/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# The category of types satisfies Grothendieck's AB5 axiom

This is of course just the well-known fact that filtered colimits commute with finite limits in
the category of types.
-/

universe v

namespace CategoryTheory.Limits

instance : AB5 (Type v) where
  ofShape _ _ _ := ⟨inferInstance⟩

end CategoryTheory.Limits

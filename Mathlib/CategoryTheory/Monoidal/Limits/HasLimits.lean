/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.CategoryTheory.SpecializeMap

/-!
# Compatibility lemmas for limits and colimits in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

-/

public section

open CategoryTheory Limits MonoidalCategory

attribute [specialize_map tensorLeft (suffix := "_tensorLeft")]
  HasColimit.isoOfNatIso_ι_hom
  colimit.ι_desc

attribute [specialize_map tensorRight (suffix := "_tensorRight")]
  HasColimit.isoOfNatIso_ι_hom
  colimit.ι_desc

attribute [reassoc (attr := simp)]
  HasColimit.isoOfNatIso_ι_hom_tensorLeft
  colimit.ι_desc_tensorLeft
  HasColimit.isoOfNatIso_ι_hom_tensorRight
  colimit.ι_desc_tensorRight

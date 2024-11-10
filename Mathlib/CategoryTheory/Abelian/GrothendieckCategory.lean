/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
import Mathlib.CategoryTheory.Limits.Filtered

/-!

# Grothendieck categories

This file defines Grothendieck categories and proves basic facts about them.

## Definitions

A `GrothendieckCategory` is an abelian category provided that it has `AB5` and a separator.

## Theorems

Relevant implications of `GrothendieckCategory` are established in
`GrothendieckCategory.wellPowered`, `GrothendieckCategory.hasLimits` and
`GrothendieckCategory.hasColimits`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits

universe u v
variable (C : Type u) [Category.{v} C]

/--
An abelian category `C` is called a Grothendieck category provided that it has `AB5` and a
separator (see `HasSeparator`).
-/
class GrothendieckCategory [Abelian C] [HasFilteredColimits C] [AB5 C] [HasSeparator C] : Prop where

section Instances

variable [HasFilteredColimits C] [AB5 C] [Abelian C] [HasSeparator C] [GrothendieckCategory C]

instance GrothendieckCategory.wellPowered : WellPowered C := HasSeparator.wellPowered
instance GrothendieckCategory.hasColimits : HasColimits C := has_colimits_of_finite_and_filtered
instance GrothendieckCategory.hasLimits : HasLimits C := hasLimits_of_hasColimits_of_hasSeparator

end Instances

end CategoryTheory

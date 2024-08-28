/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isaac Hernando, Coleton Kotch, Adam Topaz
-/

import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!

# Grothendieck Axioms

This file defines some of the Grothendieck Axioms for abelian categories, and proves
basic facts about them.

## Definitions

1. `AB4` -- an abelian category satisfies `AB4` provided that coproducts are exact.
2. `AB5` -- an abelian category satisfies `AB5` provided that filtered colimits are exact.

## Results

- `AB5` implies `AB4`

## Implementation Details

For `AB4` and `AB5`, we only assume left exactness as right exactness is automatic.

## Projects

- Add additional axioms.

-/

namespace CategoryTheory

open Limits Classical

universe v v' u u'

variable (C : Type u) [Category.{v} C]

/--
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
class AB4 [HasCoproducts C] where
  /-- Exactness of coproducts stated as `colim : (Discrete α ⥤ C) ⥤ C` preserving limits. -/
  preservesFiniteLimits (α : Type v) :
    PreservesFiniteLimits (colim (J := Discrete α) (C := C))

instance [HasCoproducts C] [AB4 C] (α : Type v) :
    PreservesFiniteLimits (colim (J := Discrete α) (C := C)) :=
  AB4.preservesFiniteLimits _

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
class AB5 [HasFilteredColimits C] where
  /-- Exactness of filtered colimits stated as `colim : (J ⥤ C) ⥤ C` on filtered `J`
  preserving limits. -/
  preservesFiniteLimits (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim (J := J) (C := C))

instance [HasFilteredColimits C] [AB5 C] (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim (J := J) (C := C)) :=
  AB5.preservesFiniteLimits _

end CategoryTheory

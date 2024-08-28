/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isaac Hernando, Coleton Kotch, Adam Topaz
-/

import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Finite

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

/-- A Category `C` which has products is said to have `CoAB4` (in literature `AB4*`)
provided that products are exact. -/
class CoAB4 [HasProducts C] where
  /-- Exactness of products stated as `lim : (Discrete α ⥤ C) ⥤ C` preserving colimits. -/
  preservesFiniteColimits (α : Type v) :
    PreservesFiniteColimits (lim (J := Discrete α) (C := C))

instance [HasProducts C] [CoAB4 C] (α : Type v) :
    PreservesFiniteColimits (lim (J := Discrete α) (C := C)) :=
  CoAB4.preservesFiniteColimits _

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

/--
A category `C` which has cofiltered limits is said to have `CoAB5` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
class CoAB5 [HasCofilteredLimits C] where
  /-- Exactness of cofiltered limits stated as `lim : (J ⥤ C) ⥤ C` on cofiltered `J`
  preserving colimits. -/
  preservesFiniteColimits (J : Type v) [SmallCategory J] [IsCofiltered J] :
    PreservesFiniteColimits (lim (J := J) (C := C))

instance [HasCofilteredLimits C] [CoAB5 C] (J : Type v) [SmallCategory J] [IsCofiltered J] :
    PreservesFiniteColimits (lim (J := J) (C := C)) :=
  CoAB5.preservesFiniteColimits _


end CategoryTheory

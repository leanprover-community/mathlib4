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

- `AB4` -- an abelian category satisfies `AB4` provided that coproducts are exact.
- `AB5` -- an abelian category satisfies `AB5` provided that filtered colimits are exact.
- The duals of the above definitions, called `AB4Star` and `AB5Star`.

## Remarks

For `AB4` and `AB5`, we only require left exactness as right exactness is automatic.
A comparison with Grothendieck's original formulation of the properties can be found in the
comments of the linked Stacks page.
Exactness as the preservation of short exact sequences is introduced in
`CategoryTheory.Abelian.Exact`.

## Projects

- Add additional axioms, especially define Grothendieck categories.
- Prove that `AB5` implies `AB4`.

## References
* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits

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

attribute [instance] AB4.preservesFiniteLimits

/-- A category `C` which has products is said to have `AB4Star` (in literature `AB4*`)
provided that products are exact. -/
class AB4Star [HasProducts C] where
  /-- Exactness of products stated as `lim : (Discrete α ⥤ C) ⥤ C` preserving colimits. -/
  preservesFiniteColimits (α : Type v) :
    PreservesFiniteColimits (lim (J := Discrete α) (C := C))

attribute [instance] AB4Star.preservesFiniteColimits

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
class AB5 [HasFilteredColimits C] where
  /-- Exactness of filtered colimits stated as `colim : (J ⥤ C) ⥤ C` on filtered `J`
  preserving limits. -/
  preservesFiniteLimits (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim (J := J) (C := C))

attribute [instance] AB5.preservesFiniteLimits

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
class AB5Star [HasCofilteredLimits C] where
  /-- Exactness of cofiltered limits stated as `lim : (J ⥤ C) ⥤ C` on cofiltered `J`
  preserving colimits. -/
  preservesFiniteColimits (J : Type v) [SmallCategory J] [IsCofiltered J] :
    PreservesFiniteColimits (lim (J := J) (C := C))

attribute [instance] AB5Star.preservesFiniteColimits

end CategoryTheory

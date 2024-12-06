/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isaac Hernando, Coleton Kotch, Adam Topaz
-/

import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!

# Grothendieck Axioms

This file defines some of the Grothendieck Axioms for abelian categories, and proves
basic facts about them.

## Definitions

- `AB4` -- a category satisfies `AB4` provided that coproducts are exact.
- `AB5` -- a category satisfies `AB5` provided that filtered colimits are exact.
- The duals of the above definitions, called `AB4Star` and `AB5Star`.

## Theorems

- The implication from `AB5` to `AB4` is established in `AB4.ofAB5`.

## Remarks

For `AB4` and `AB5`, we only require left exactness as right exactness is automatic.
A comparison with Grothendieck's original formulation of the properties can be found in the
comments of the linked Stacks page.
Exactness as the preservation of short exact sequences is introduced in
`CategoryTheory.Abelian.Exact`.

We do not require `Abelian` in the definition of `AB4` and `AB5` because these classes represent
individual axioms. An `AB4` category is an _abelian_ category satisfying `AB4`, and similarly for
`AB5`.

## Projects

- Add additional axioms, especially define Grothendieck categories.

## References
* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits

universe v v' u u' w

variable (C : Type u) [Category.{v} C]

attribute [local instance] hasCoproducts_of_finite_and_filtered

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

noncomputable section

open CoproductsFromFiniteFiltered

variable {α : Type w}
variable [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]

instance preservesFiniteLimits_liftToFinset : PreservesFiniteLimits (liftToFinset C α) :=
  preservesFiniteLimits_of_evaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) :=
      ⟨fun J _ _ => whiskeringLeft_preservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso  I).symm

/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
lemma AB4.of_AB5 [HasFilteredColimits C] [AB5 C] : AB4 C where
  preservesFiniteLimits J :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

end

end CategoryTheory

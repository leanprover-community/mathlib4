/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isaac Hernando, Coleton Kotch, Adam Topaz
-/

import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

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

universe v v' u u' w

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

noncomputable section

open CoproductsFromFiniteFiltered

variable {α : Type w}

/-- `liftToFinset`, when composed with the evaluation functor, results in the whiskering composed
with `colim`. -/
def liftToFinsetEvaluationIso [HasFiniteCoproducts C] (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj I ≅
    (whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ colim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    (fun _ => by dsimp; ext; simp)

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

instance : PreservesFiniteLimits (liftToFinset C α) :=
  preservesFiniteLimitsOfEvaluation _ fun I =>
    let colimIso : colim (J := Discrete I) (C := C) ≅ lim := sorry
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimitsOfNatIso colimIso.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete { x // x ∈ I }) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) := by
      sorry
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      compPreservesFiniteLimits _ _
    preservesFiniteLimitsOfNatIso (liftToFinsetEvaluationIso C I).symm

def AB4.ofAB5 [HasFilteredColimits C] [HasCoproducts C] [AB5 C] : AB4 C where
  preservesFiniteLimits J :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      compPreservesFiniteLimits _ _
    preservesFiniteLimitsOfNatIso (liftToFinsetColimIso)

end

end CategoryTheory

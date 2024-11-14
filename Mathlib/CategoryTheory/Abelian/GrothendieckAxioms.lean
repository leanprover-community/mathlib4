/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isaac Hernando, Coleton Kotch, Adam Topaz
-/
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Logic.Equiv.List
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
A category `C` which has colimits of shape `J` is said to have `AB` of shape `J` provided that
colimits of shape `J` are exact.
-/
class ABOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasColimitsOfShape J C]  where
  /-- Exactness of `J`-shaped colimits stated as `colim : (J ⥤ C) ⥤ C` preserving finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (colim (J := J) (C := C))

attribute [instance] ABOfShape.preservesFiniteLimits

/--
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
abbrev AB4 [HasCoproducts C] := ∀ (α : Type v), ABOfShape (Discrete α) C

/--
A category `C` which has countable coproducts is said to have countable `AB4` provided that
countable coproducts are exact.
-/
abbrev CountableAB4 [HasCountableCoproducts C] :=
  ∀ (α : Type) [Countable α], ABOfShape (Discrete α) C

instance [HasCoproducts C] [AB4 C] (J : Type v) : ABOfShape (Discrete J) C := inferInstance

/--
A category `C` which has limits of shape `J` is said to have `ABStar` of shape `J` provided that
limits of shape `J` are exact.
-/
class ABStarOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasLimitsOfShape J C] where
  /-- Exactness of `J`-shaped limits stated as `lim : (J ⥤ C) ⥤ C` preserving finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (lim (J := J) (C := C))

attribute [instance] ABStarOfShape.preservesFiniteColimits

/-- A category `C` which has products is said to have `AB4Star` (in literature `AB4*`)
provided that products are exact. -/
abbrev AB4Star [HasProducts C] := ∀ (α : Type v), ABStarOfShape (Discrete α) C

/--
A category `C` which has countable coproducts is said to have countable `AB4Star` provided that
countable products are exact.
-/
abbrev CountableAB4Star [HasCountableProducts C] :=
  ∀ (α : Type) [Countable α], ABStarOfShape (Discrete α) C

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
abbrev AB5 [HasFilteredColimits C] := ∀ (J : Type v) [SmallCategory J] [IsFiltered J], ABOfShape J C

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
abbrev AB5Star [HasCofilteredLimits C] :=
  ∀ (J : Type v) [SmallCategory J] [IsCofiltered J], ABStarOfShape J C

noncomputable section


variable {α : Type w}
variable [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]
section

open CoproductsFromFiniteFiltered

instance preservesFiniteLimitsLiftToFinset : PreservesFiniteLimits (liftToFinset C α) :=
  preservesFiniteLimitsOfEvaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimitsOfNatIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) :=
      ⟨fun J _ _ => whiskeringLeftPreservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      compPreservesFiniteLimits _ _
    preservesFiniteLimitsOfNatIso (liftToFinsetEvaluationIso  I).symm

variable (J : Type*)


def ABOfShapeDiscreteOfABOfShapeFinsetDiscrete [HasColimitsOfShape (Discrete J) C]
    [HasColimitsOfShape (Finset (Discrete J)) C] [ABOfShape (Finset (Discrete J)) C] :
    ABOfShape (Discrete J) C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      compPreservesFiniteLimits _ _
    preservesFiniteLimitsOfNatIso (liftToFinsetColimIso)

section

variable {J} {J' : Type*} [Category J] [Category J'] (F : J ⥤ J') [F.Final]

def ABOfShapeOfInitial [HasColimitsOfShape J' C] [HasColimitsOfShape J C] [ABOfShape J C] :
    ABOfShape J' C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := compPreservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimitsOfNatIso (Functor.Final.colimIso F)

end

/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
def AB4.ofAB5 [HasFiniteCoproducts C] [HasFilteredColimits C] [AB5 C] : AB4 C := fun _ ↦
  ABOfShapeDiscreteOfABOfShapeFinsetDiscrete _ _

/--
A category with finite biproducts and finite limits has countable AB4 if sequential colimits are
exact.
-/
def CountableAB4.ofCountableAB5 [HasColimitsOfShape ℕ C] [ABOfShape ℕ C]
    [HasCountableCoproducts C] : CountableAB4 C := fun J _ ↦
  have : HasColimitsOfShape (Finset (Discrete J)) C :=
    Functor.Final.hasColimitsOfShape_of_final
      (IsFiltered.sequentialFunctor (Finset (Discrete J)))
  have := ABOfShapeOfInitial C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
  ABOfShapeDiscreteOfABOfShapeFinsetDiscrete _ _

end

variable [HasFiniteColimits C]

section

open ProductsFromFiniteCofiltered

instance preservesFiniteColimitsLiftToFinset : PreservesFiniteColimits (liftToFinset C α) :=
  preservesFiniteColimitsOfEvaluation _ fun ⟨I⟩ =>
    letI : PreservesFiniteColimits (lim (J := Discrete I) (C := C)) :=
      preservesFiniteColimitsOfNatIso HasBiproductsOfShape.colimIsoLim
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) := ⟨fun _ _ _ => inferInstance⟩
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ lim) :=
      compPreservesFiniteColimits _ _
    preservesFiniteColimitsOfNatIso (liftToFinsetEvaluationIso _ _ I).symm

variable (J : Type*)

def ABStarOfShapeDiscreteOfABStarOfShapeFinsetDiscreteOp [HasLimitsOfShape (Discrete J) C]
    [HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C] [ABStarOfShape (Finset (Discrete J))ᵒᵖ C] :
    ABStarOfShape (Discrete J) C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      compPreservesFiniteColimits _ _
    preservesFiniteColimitsOfNatIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

section

variable {J} {J' : Type*} [Category J] [Category J'] (F : J ⥤ J') [F.Initial]


def ABStarOfShapeOfFinal [HasLimitsOfShape J' C] [HasLimitsOfShape J C] [ABStarOfShape J C] :
    ABStarOfShape J' C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := compPreservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimitsOfNatIso (Functor.Initial.limIso F)

end

/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
def AB4Star.ofAB5Star [HasProducts C] [HasCofilteredLimits C] [AB5Star C] : AB4Star C :=
  fun _ ↦ ABStarOfShapeDiscreteOfABStarOfShapeFinsetDiscreteOp _ _

/--
A category with finite biproducts and finite limits has countable AB4* if sequential limits are
exact.
-/
def CountableAB4Star.ofCountableAB5Star [HasLimitsOfShape ℕᵒᵖ C] [ABStarOfShape ℕᵒᵖ C]
    [HasCountableProducts C] : CountableAB4Star C := fun J _ ↦
  have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
    Functor.Initial.hasLimitsOfShape_of_initial
      (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
  have := ABStarOfShapeOfFinal C (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
  ABStarOfShapeDiscreteOfABStarOfShapeFinsetDiscreteOp _ _

end

end

section EpiMono

open Functor

variable [Abelian C] -- Could be weakened

variable (J : Type u') [Category.{v'} J]

noncomputable def ABOfShapeOfPreservesMono [HasColimitsOfShape J C]
    [PreservesMonomorphisms (colim (J := J) (C := C))] : ABOfShape J C where
  preservesFiniteLimits := by
    apply (config := { allowSynthFailures := true }) preservesFiniteLimitsOfPreservesHomology
    · exact preservesHomologyOfPreservesMonosAndCokernels _
    · letI : PreservesZeroMorphisms (colim (J := J) (C := C)) := inferInstance
      letI : PreservesBinaryBiproducts (colim (J := J) (C := C)) :=
        preservesBinaryBiproductsOfPreservesBinaryCoproducts _
      exact additive_of_preservesBinaryBiproducts _

noncomputable def ABStarOfShapeOfPreservesEpi [HasLimitsOfShape J C]
    [PreservesEpimorphisms (lim (J := J) (C := C))] : ABStarOfShape J C where
  preservesFiniteColimits := by
    apply (config := { allowSynthFailures := true }) preservesFiniteColimitsOfPreservesHomology
    · exact preservesHomologyOfPreservesEpisAndKernels _
    · letI : PreservesZeroMorphisms (lim (J := J) (C := C)) := inferInstance
      letI : PreservesBinaryBiproducts (lim (J := J) (C := C)) :=
        preservesBinaryBiproductsOfPreservesBinaryProducts _
      exact additive_of_preservesBinaryBiproducts _

end EpiMono

end CategoryTheory

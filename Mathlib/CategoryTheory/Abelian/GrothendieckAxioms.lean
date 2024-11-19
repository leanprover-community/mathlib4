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

- `ABOfShape J` -- colimits of shape `J` are exact.
- The dual of the above definitions, called `ABStarOfShape`.
- `AB4` -- coproducts are exact (this is formulated in terms of `ABOfShape`).
- `AB5` -- filtered colimits are exact (this is formulated in terms of `ABOfShape`).

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
class AB4 [HasCoproducts C] where
  ofShape (α : Type v) : ABOfShape (Discrete α) C

attribute [instance] AB4.ofShape

/--
A category `C` which has countable coproducts is said to have countable `AB4` provided that
countable coproducts are exact.
-/
class CountableAB4 [HasCountableCoproducts C] where
  ofShape (α : Type) [Countable α] : ABOfShape (Discrete α) C

attribute [instance] CountableAB4.ofShape

-- instance [HasCoproducts C] [AB4 C] (J : Type v) : ABOfShape (Discrete J) C := inferInstance

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
class AB4Star [HasProducts C] where
  ofShape (α : Type v) : ABStarOfShape (Discrete α) C

attribute [instance] AB4Star.ofShape

/--
A category `C` which has countable coproducts is said to have countable `AB4Star` provided that
countable products are exact.
-/
class CountableAB4Star [HasCountableProducts C] where
  ofShape (α : Type) [Countable α] : ABStarOfShape (Discrete α) C

attribute [instance] CountableAB4Star.ofShape

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
class AB5 [HasFilteredColimits C] where
  ofShape (J : Type v) [SmallCategory J] [IsFiltered J] : ABOfShape J C

attribute [instance] AB5.ofShape

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
class AB5Star [HasCofilteredLimits C] where
  ofShape (J : Type v) [SmallCategory J] [IsCofiltered J] : ABStarOfShape J C

attribute [instance] AB5Star.ofShape

noncomputable section

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]

section

open CoproductsFromFiniteFiltered

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
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso I).symm

variable (J : Type*)

/-- `ABOfShape (Finset (Discrete J)) C` implies `ABOfShape (Discrete J) C` -/
def ABOfShape_discrete_of_ABOfShape_finset_discrete [HasColimitsOfShape (Discrete J) C]
    [HasColimitsOfShape (Finset (Discrete J)) C] [ABOfShape (Finset (Discrete J)) C] :
    ABOfShape (Discrete J) C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

section

variable {J} {J' : Type*} [Category J] [Category J'] (F : J ⥤ J') [F.Final]

/-- `ABOfShape` can be "pushed forward" along final functors -/
def ABOfShape_of_final [HasColimitsOfShape J' C] [HasColimitsOfShape J C] [ABOfShape J C] :
    ABOfShape J' C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := comp_preservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimits_of_natIso (Functor.Final.colimIso F)

end

/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
def AB4.of_AB5 [HasFiniteCoproducts C] [HasFilteredColimits C] [AB5 C] : AB4 C where
  ofShape _ := ABOfShape_discrete_of_ABOfShape_finset_discrete _ _

/--
A category with finite biproducts and finite limits has countable AB4 if sequential colimits are
exact.
-/
def CountableAB4.of_countableAB5 [HasColimitsOfShape ℕ C] [ABOfShape ℕ C]
    [HasCountableCoproducts C] : CountableAB4 C where
  ofShape J :=
    have : HasColimitsOfShape (Finset (Discrete J)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    have := ABOfShape_of_final C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    ABOfShape_discrete_of_ABOfShape_finset_discrete _ _

end

variable [HasFiniteColimits C]

section

open ProductsFromFiniteCofiltered

instance preservesFiniteColimits_liftToFinset : PreservesFiniteColimits (liftToFinset C α) :=
  preservesFiniteColimits_of_evaluation _ fun ⟨I⟩ =>
    letI : PreservesFiniteColimits (lim (J := Discrete I) (C := C)) :=
      preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) := ⟨fun _ _ _ => inferInstance⟩
    letI : PreservesFiniteColimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (liftToFinsetEvaluationIso _ _ I).symm

variable (J : Type*)

/-- `ABStarOfShape (Finset (Discrete J))ᵒᵖ C` implies `ABStarOfShape (Discrete J) C` -/
def ABStarOfShape_discrete_ofABStarOfShape_finset_discrete_op [HasLimitsOfShape (Discrete J) C]
    [HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C] [ABStarOfShape (Finset (Discrete J))ᵒᵖ C] :
    ABStarOfShape (Discrete J) C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

section

variable {J} {J' : Type*} [Category J] [Category J'] (F : J ⥤ J') [F.Initial]

/-- `ABStarOfShape` can be "pushed forward" along initial functors -/
def ABStarOfShape_of_initial [HasLimitsOfShape J' C] [HasLimitsOfShape J C] [ABStarOfShape J C] :
    ABStarOfShape J' C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := comp_preservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimits_of_natIso (Functor.Initial.limIso F)

end

/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
def AB4Star.of_AB5Star [HasProducts C] [HasCofilteredLimits C] [AB5Star C] : AB4Star C where
  ofShape _ := ABStarOfShape_discrete_ofABStarOfShape_finset_discrete_op _ _

/--
A category with finite biproducts and finite limits has countable AB4* if sequential limits are
exact.
-/
def CountableAB4Star.of_countableAB5Star [HasLimitsOfShape ℕᵒᵖ C] [ABStarOfShape ℕᵒᵖ C]
    [HasCountableProducts C] : CountableAB4Star C where
  ofShape J :=
    have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    have := ABStarOfShape_of_initial C (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    ABStarOfShape_discrete_ofABStarOfShape_finset_discrete_op _ _

/--
Checking AB of shape `Discrete ℕ` and `Discrete J` for finite `J` is enough for countable AB.
-/
def CountableAB4.of_ABOfShape_nat_and_finite [HasCountableCoproducts C]
    [∀ (J : Type) [Finite J], ABOfShape (Discrete J) C] [ABOfShape (Discrete ℕ) C] :
    CountableAB4 C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact ABOfShape_of_final C (Discrete.equivalence (Denumerable.eqv J)).inverse

/--
Checking AB* of shape `Discrete ℕ` and `Discrete J` for finite `J` is enough for countable AB*.
-/
def CountableAB4Star.of_ABStarOfShape_nat_and_finite [HasCountableProducts C]
    [∀ (J : Type) [Finite J], ABStarOfShape (Discrete J) C] [ABStarOfShape (Discrete ℕ) C] :
    CountableAB4Star C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact ABStarOfShape_of_initial C (Discrete.equivalence (Denumerable.eqv J)).inverse

end

end

section EpiMono

open Functor

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

noncomputable instance ABOfShape_discrete_finite (J : Type*) [Finite J] :
    ABOfShape (Discrete J) C where
  preservesFiniteLimits := preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm

noncomputable instance ABStarOfShape_discrete_finite {J : Type*} [Finite J] :
    ABStarOfShape (Discrete J) C where
  preservesFiniteColimits := preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim

/--
Checking AB of shape `Discrete ℕ` is enough for countable AB, provided that the category has
finite biproducts and finite limits.
-/
noncomputable def CountableAB4.of_ABOfShape_nat [HasFiniteLimits C] [HasCountableCoproducts C]
    [ABOfShape (Discrete ℕ) C] : CountableAB4 C := by
  apply (config := { allowSynthFailures := true }) CountableAB4.of_ABOfShape_nat_and_finite
  exact fun _ ↦ inferInstance

/--
Checking AB* of shape `Discrete ℕ` is enough for countable AB*, provided that the category has
finite biproducts and finite colimits.
-/
noncomputable def CountableAB4Star.of_ABStarOfShape_nat [HasFiniteColimits C]
    [HasCountableProducts C] [ABStarOfShape (Discrete ℕ) C] : CountableAB4Star C := by
  apply (config := { allowSynthFailures := true }) CountableAB4Star.of_ABStarOfShape_nat_and_finite
  exact fun _ ↦ inferInstance

end

variable [Abelian C] (J : Type u') [Category.{v'} J]

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

/--
If `colim` of shape `J` into an abelian category `C` preserves monomorphisms, then `C` has AB of
shape `J`.
-/
noncomputable def ABOfShape_of_preservesMono [HasColimitsOfShape J C]
    [PreservesMonomorphisms (colim (J := J) (C := C))] : ABOfShape J C where
  preservesFiniteLimits := by
    apply (config := { allowSynthFailures := true }) preservesFiniteLimits_of_preservesHomology
    · exact preservesHomology_of_preservesMonos_and_cokernels _
    · exact additive_of_preservesBinaryBiproducts _

/--
If `lim` of shape `J` into an abelian category `C` preserves epimorphisms, then `C` has AB* of
shape `J`.
-/
noncomputable def ABStarOfShape_of_preservesEpi [HasLimitsOfShape J C]
    [PreservesEpimorphisms (lim (J := J) (C := C))] : ABStarOfShape J C where
  preservesFiniteColimits := by
    apply (config := { allowSynthFailures := true }) preservesFiniteColimits_of_preservesHomology
    · exact preservesHomology_of_preservesEpis_and_kernels _
    · exact additive_of_preservesBinaryBiproducts _

end EpiMono

end CategoryTheory

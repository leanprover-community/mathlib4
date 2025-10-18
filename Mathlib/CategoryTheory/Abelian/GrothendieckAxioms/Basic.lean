/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Isaac Hernando, Coleton Kotch, Adam Topaz
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

- `HasExactColimitsOfShape J C` -- colimits of shape `J` in `C` are exact.
- The dual of the above definitions, called `HasExactLimitsOfShape`.
- `AB4` -- coproducts are exact (this is formulated in terms of `HasExactColimitsOfShape`).
- `AB5` -- filtered colimits are exact (this is formulated in terms of `HasExactColimitsOfShape`).

## Theorems

- The implication from `AB5` to `AB4` is established in `AB4.ofAB5`.
- That `HasExactColimitsOfShape J C` is invariant under equivalences in both parameters is shown
in `HasExactColimitsOfShape.of_domain_equivalence` and
`HasExactColimitsOfShape.of_codomain_equivalence`.

## Remarks

For `AB4` and `AB5`, we only require left exactness as right exactness is automatic.
A comparison with Grothendieck's original formulation of the properties can be found in the
comments of the linked Stacks page.
Exactness as the preservation of short exact sequences is introduced in
`CategoryTheory.Abelian.Exact`.

We do not require `Abelian` in the definition of `AB4` and `AB5` because these classes represent
individual axioms. An `AB4` category is an _abelian_ category satisfying `AB4`, and similarly for
`AB5`.

## References
* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits Functor

attribute [instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w w' w₂ w₂' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C]

/--
A category `C` is said to have exact colimits of shape `J` provided that colimits of shape `J`
exist and are exact (in the sense that they preserve finite limits).
-/
class HasExactColimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasColimitsOfShape J C] where
  /-- Exactness of `J`-shaped colimits stated as `colim : (J ⥤ C) ⥤ C` preserving finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (colim (J := J) (C := C))

/--
A category `C` is said to have exact limits of shape `J` provided that limits of shape `J`
exist and are exact (in the sense that they preserve finite colimits).
-/
class HasExactLimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasLimitsOfShape J C] where
  /-- Exactness of `J`-shaped limits stated as `lim : (J ⥤ C) ⥤ C` preserving finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (lim (J := J) (C := C))

attribute [instance] HasExactColimitsOfShape.preservesFiniteLimits
  HasExactLimitsOfShape.preservesFiniteColimits

variable {C} in
/--
Pull back a `HasExactColimitsOfShape J` along a functor which preserves and reflects finite limits
and preserves colimits of shape `J`
-/
lemma HasExactColimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category J] [Category D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [ReflectsFiniteLimits F] [HasFiniteLimits C]
    [PreservesColimitsOfShape J F] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cones.ext ((preservesColimitNatIso F).symm.app _)
        fun i ↦ (preservesColimitNatIso F).inv.naturality _ } } }

variable {C} in
/--
Pull back a `HasExactLimitsOfShape J` along a functor which preserves and reflects finite colimits
and preserves limits of shape `J`
-/
lemma HasExactLimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category D] [Category J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] [HasExactLimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteColimits F] [ReflectsFiniteColimits F] [HasFiniteColimits C]
    [PreservesLimitsOfShape J F] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocones.ext ((preservesLimitNatIso F).symm.app _) fun i ↦ ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocones.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocones.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      exact (preservesLimitNatIso F).inv.naturality _ } } }

/--
Transport a `HasExactColimitsOfShape` along an equivalence of the shape.

Note: When `C` has finite limits, this lemma holds with the equivalence replaced by a final
functor, see `hasExactColimitsOfShape_of_final` below.
-/
lemma HasExactColimitsOfShape.of_domain_equivalence {J J' : Type*} [Category J] [Category J']
    (e : J ≌ J') [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
    HasExactColimitsOfShape J' C :=
  haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
  ⟨preservesFiniteLimits_of_natIso (Functor.Final.colimIso e.functor)⟩

variable {C} in
lemma HasExactColimitsOfShape.of_codomain_equivalence (J : Type*) [Category J] {D : Type*}
    [Category D] (e : C ≌ D) [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
    HasExactColimitsOfShape J D := by
  haveI : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesLimit_of_natIso K (?_ : e.congrRight.inverse ⋙ colim ⋙ e.functor ≅ colim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ colim) e.unitIso.symm ≪≫ (preservesColimitNatIso e.inverse).symm

/--
Transport a `HasExactLimitsOfShape` along an equivalence of the shape.

Note: When `C` has finite colimits, this lemma holds with the equivalence replaced by a initial
functor, see `hasExactLimitsOfShape_of_initial` below.
-/
lemma HasExactLimitsOfShape.of_domain_equivalence {J J' : Type*} [Category J] [Category J']
    (e : J ≌ J') [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
    HasExactLimitsOfShape J' C :=
  haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
  ⟨preservesFiniteColimits_of_natIso (Functor.Initial.limIso e.functor)⟩

variable {C} in
lemma HasExactLimitsOfShape.of_codomain_equivalence (J : Type*) [Category J] {D : Type*}
    [Category D] (e : C ≌ D) [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
    HasExactLimitsOfShape J D := by
  haveI : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesColimit_of_natIso K (?_ : e.congrRight.inverse ⋙ lim ⋙ e.functor ≅ lim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ lim) e.unitIso.symm ≪≫ (preservesLimitNatIso e.inverse).symm

namespace Adjunction

variable {C} {D : Type u''} [Category.{v''} D] {F : C ⥤ D} {G : D ⥤ C}

/-- Let `adj : F ⊣ G` be an adjunction, with `G : D ⥤ C` reflective.
Assume that `D` has finite limits and `F` commutes to them.
If `C` has exact colimits of shape `J`, then `D` also has exact colimits of shape `J`. -/
lemma hasExactColimitsOfShape (adj : F ⊣ G) [G.Full] [G.Faithful]
    (J : Type u') [Category.{v'} J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [HasExactColimitsOfShape J C] [HasFiniteLimits D] [PreservesFiniteLimits F] :
    HasExactColimitsOfShape J D where
  preservesFiniteLimits := ⟨fun K _ _ ↦ ⟨fun {H} ↦ by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{v', u'} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J D C).obj G ⋙ colim ⋙ F ≅ colim :=
      isoWhiskerLeft _ (preservesColimitNatIso F) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso G F) _ ≪≫
        isoWhiskerRight ((whiskeringRight J D D).mapIso (asIso adj.counit)) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ colim.leftUnitor
    exact preservesLimit_of_natIso _ e⟩⟩

/-- Let `adj : F ⊣ G` be an adjunction, with `F : C ⥤ D` coreflective.
Assume that `C` has finite colimits and `G` commutes to them.
If `D` has exact limits of shape `J`, then `C` also has exact limits of shape `J`. -/
lemma hasExactLimitsOfShape (adj : F ⊣ G) [F.Full] [F.Faithful]
    (J : Type u') [Category.{v'} J] [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [HasExactLimitsOfShape J D] [HasFiniteColimits C] [PreservesFiniteColimits G] :
    HasExactLimitsOfShape J C where
  preservesFiniteColimits:= ⟨fun K _ _ ↦ ⟨fun {H} ↦ by
    have : PreservesLimitsOfSize.{v', u'} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J _ _).obj F ⋙ lim ⋙ G ≅ lim :=
      isoWhiskerLeft _ (preservesLimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso F G) _ ≪≫
        isoWhiskerRight ((whiskeringRight J C C).mapIso (asIso adj.unit).symm) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ lim.leftUnitor
    exact preservesColimit_of_natIso _ e⟩⟩

end Adjunction

/--
A category `C` which has coproducts is said to have `AB4` of size `w` provided that
coproducts of size `w` are exact.
-/
@[pp_with_univ]
class AB4OfSize [HasCoproducts.{w} C] where
  ofShape (α : Type w) : HasExactColimitsOfShape (Discrete α) C

attribute [instance] AB4OfSize.ofShape

/--
A category `C` which has coproducts is said to have `AB4` provided that
coproducts are exact.
-/
@[stacks 079B]
abbrev AB4 [HasCoproducts C] := AB4OfSize.{v} C

lemma AB4OfSize_shrink [HasCoproducts.{max w w'} C] [AB4OfSize.{max w w'} C] :
    haveI : HasCoproducts.{w} C := hasCoproducts_shrink.{w, w'}
    AB4OfSize.{w} C :=
  haveI := hasCoproducts_shrink.{w, w'} (C := C)
  ⟨fun J ↦ HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

instance (priority := 100) [HasCoproducts.{w} C] [AB4OfSize.{w} C] :
    haveI : HasCoproducts.{0} C := hasCoproducts_shrink
    AB4OfSize.{0} C := AB4OfSize_shrink C

/-- A category `C` which has products is said to have `AB4Star` (in literature `AB4*`)
provided that products are exact. -/
@[pp_with_univ, stacks 079B]
class AB4StarOfSize [HasProducts.{w} C] where
  ofShape (α : Type w) : HasExactLimitsOfShape (Discrete α) C

attribute [instance] AB4StarOfSize.ofShape

/-- A category `C` which has products is said to have `AB4Star` (in literature `AB4*`)
provided that products are exact. -/
abbrev AB4Star [HasProducts C] := AB4StarOfSize.{v} C

lemma AB4StarOfSize_shrink [HasProducts.{max w w'} C] [AB4StarOfSize.{max w w'} C] :
    haveI : HasProducts.{w} C := hasProducts_shrink.{w, w'}
    AB4StarOfSize.{w} C :=
  haveI := hasProducts_shrink.{w, w'} (C := C)
  ⟨fun J ↦ HasExactLimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)⟩

instance (priority := 100) [HasProducts.{w} C] [AB4StarOfSize.{w} C] :
    haveI : HasProducts.{0} C := hasProducts_shrink
    AB4StarOfSize.{0} C := AB4StarOfSize_shrink C

/--
A category `C` which has countable coproducts is said to have countable `AB4` provided that
countable coproducts are exact.
-/
class CountableAB4 [HasCountableCoproducts C] where
  ofShape (α : Type) [Countable α] : HasExactColimitsOfShape (Discrete α) C

instance (priority := 100) [HasCoproducts.{0} C] [AB4OfSize.{0} C] : CountableAB4 C :=
  ⟨inferInstance⟩

/--
A category `C` which has countable coproducts is said to have countable `AB4Star` provided that
countable products are exact.
-/
class CountableAB4Star [HasCountableProducts C] where
  ofShape (α : Type) [Countable α] : HasExactLimitsOfShape (Discrete α) C

instance (priority := 100) [HasProducts.{0} C] [AB4StarOfSize.{0} C] : CountableAB4Star C :=
  ⟨inferInstance⟩

attribute [instance] CountableAB4.ofShape CountableAB4Star.ofShape

/--
A category `C` which has filtered colimits of a given size is said to have `AB5` of that size
provided that these filtered colimits are exact.

`AB5OfSize.{w, w'} C` means that `C` has exact colimits of shape `J : Type w'` with
`Category.{w} J` such that `J` is filtered.
-/
@[pp_with_univ]
class AB5OfSize [HasFilteredColimitsOfSize.{w, w'} C] where
  ofShape (J : Type w') [Category.{w} J] [IsFiltered J] : HasExactColimitsOfShape J C

attribute [instance] AB5OfSize.ofShape

/--
A category `C` which has filtered colimits is said to have `AB5` provided that
filtered colimits are exact.
-/
@[stacks 079B]
abbrev AB5 [HasFilteredColimits C] := AB5OfSize.{v, v} C

lemma AB5OfSize_of_univLE [HasFilteredColimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
    [UnivLE.{w', w₂'}] [AB5OfSize.{w₂, w₂'} C] :
    haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
    AB5OfSize.{w, w'} C := by
  haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  haveI := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactColimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

lemma AB5OfSize_shrink [HasFilteredColimitsOfSize.{max w w₂, max w' w₂'} C]
    [AB5OfSize.{max w w₂, max w' w₂'} C] :
    haveI : HasFilteredColimitsOfSize.{w, w'} C := hasFilteredColimitsOfSize_shrink
    AB5OfSize.{w, w'} C :=
  AB5OfSize_of_univLE C

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
@[pp_with_univ, stacks 079B]
class AB5StarOfSize [HasCofilteredLimitsOfSize.{w, w'} C] where
  ofShape (J : Type w') [Category.{w} J] [IsCofiltered J] : HasExactLimitsOfShape J C

attribute [instance] AB5StarOfSize.ofShape

/--
A category `C` which has cofiltered limits is said to have `AB5Star` (in literature `AB5*`)
provided that cofiltered limits are exact.
-/
abbrev AB5Star [HasCofilteredLimits C] := AB5StarOfSize.{v, v} C

lemma AB5StarOfSize_of_univLE [HasCofilteredLimitsOfSize.{w₂, w₂'} C] [UnivLE.{w, w₂}]
    [UnivLE.{w', w₂'}] [AB5StarOfSize.{w₂, w₂'} C] :
    haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
    AB5StarOfSize.{w, w'} C := by
  haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_of_univLE.{w}
  constructor
  intro J _ _
  haveI := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J))
  exact HasExactLimitsOfShape.of_domain_equivalence _ ((ShrinkHoms.equivalence.{w₂} J).trans <|
    Shrink.equivalence.{w₂', w₂} (ShrinkHoms.{w'} J)).symm

lemma AB5StarOfSize_shrink [HasCofilteredLimitsOfSize.{max w w₂, max w' w₂'} C]
    [AB5StarOfSize.{max w w₂, max w' w₂'} C] :
    haveI : HasCofilteredLimitsOfSize.{w, w'} C := hasCofilteredLimitsOfSize_shrink
    AB5StarOfSize.{w, w'} C :=
  AB5StarOfSize_of_univLE C

/-- `HasExactColimitsOfShape` can be "pushed forward" along final functors -/
lemma hasExactColimitsOfShape_of_final [HasFiniteLimits C] {J J' : Type*} [Category J] [Category J']
    (F : J ⥤ J') [F.Final] [HasColimitsOfShape J' C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] : HasExactColimitsOfShape J' C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := comp_preservesFiniteLimits ((whiskeringLeft J J' C).obj F) colim
    preservesFiniteLimits_of_natIso (Functor.Final.colimIso F)

/-- `HasExactLimitsOfShape` can be "pushed forward" along initial functors -/
lemma hasExactLimitsOfShape_of_initial [HasFiniteColimits C] {J J' : Type*} [Category J]
    [Category J'] (F : J ⥤ J') [F.Initial] [HasLimitsOfShape J' C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] : HasExactLimitsOfShape J' C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits ((whiskeringLeft J J' C).obj F) := ⟨fun _ ↦ inferInstance⟩
    letI := comp_preservesFiniteColimits ((whiskeringLeft J J' C).obj F) lim
    preservesFiniteColimits_of_natIso (Functor.Initial.limIso F)

section AB4OfAB5

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]

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

/--
`HasExactColimitsOfShape (Finset (Discrete J)) C` implies `HasExactColimitsOfShape (Discrete J) C`
-/
lemma hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) C]
    [HasExactColimitsOfShape (Finset (Discrete J)) C] : HasExactColimitsOfShape (Discrete J) C where
  preservesFiniteLimits :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)

attribute [local instance] hasCoproducts_of_finite_and_filtered in
/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
lemma AB4.of_AB5 [HasFilteredColimitsOfSize.{w, w} C]
    [AB5OfSize.{w, w} C] : AB4OfSize.{w} C where
  ofShape _ := hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

/--
A category with finite biproducts and finite limits has countable AB4 if sequential colimits are
exact.
-/
lemma CountableAB4.of_countableAB5 [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [HasCountableCoproducts C] : CountableAB4 C where
  ofShape J :=
    have : HasColimitsOfShape (Finset (Discrete J)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    have := hasExactColimitsOfShape_of_final C (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _

end AB4OfAB5

section AB4StarOfAB5Star

variable {α : Type w} [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteColimits C]

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

/--
`HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C` implies  `HasExactLimitsOfShape (Discrete J) C`
-/
lemma hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
    [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C]
    [HasExactLimitsOfShape (Finset (Discrete J))ᵒᵖ C] :
    HasExactLimitsOfShape (Discrete J) C where
  preservesFiniteColimits :=
    letI : PreservesFiniteColimits (ProductsFromFiniteCofiltered.liftToFinset C J ⋙ lim) :=
      comp_preservesFiniteColimits _ _
    preservesFiniteColimits_of_natIso (ProductsFromFiniteCofiltered.liftToFinsetLimIso _ _)

attribute [local instance] hasProducts_of_finite_and_cofiltered in
/-- A category with finite biproducts and finite limits is AB4 if it is AB5. -/
lemma AB4Star.of_AB5Star [HasCofilteredLimitsOfSize.{w, w} C] [AB5StarOfSize.{w, w} C] :
    AB4StarOfSize.{w} C where
  ofShape _ := hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

/--
A category with finite biproducts and finite limits has countable AB4* if sequential limits are
exact.
-/
lemma CountableAB4Star.of_countableAB5Star [HasLimitsOfShape ℕᵒᵖ C] [HasExactLimitsOfShape ℕᵒᵖ C]
    [HasCountableProducts C] : CountableAB4Star C where
  ofShape J :=
    have : HasLimitsOfShape (Finset (Discrete J))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    have := hasExactLimitsOfShape_of_initial C
      (IsFiltered.sequentialFunctor (Finset (Discrete J))).op
    hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op _ _

end AB4StarOfAB5Star

/--
Checking exactness of colimits of shape `Discrete ℕ` and `Discrete J` for finite `J` is enough for
countable AB4.
-/
lemma CountableAB4.of_hasExactColimitsOfShape_nat_and_finite [HasCountableCoproducts C]
    [HasFiniteLimits C] [∀ (J : Type) [Finite J], HasExactColimitsOfShape (Discrete J) C]
    [HasExactColimitsOfShape (Discrete ℕ) C] :
    CountableAB4 C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactColimitsOfShape_of_final C (Discrete.equivalence (Denumerable.eqv J)).inverse

/--
Checking exactness of limits of shape `Discrete ℕ` and `Discrete J` for finite `J` is enough for
countable AB4*.
-/
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite [HasCountableProducts C]
    [HasFiniteColimits C] [∀ (J : Type) [Finite J], HasExactLimitsOfShape (Discrete J) C]
    [HasExactLimitsOfShape (Discrete ℕ) C] :
    CountableAB4Star C where
  ofShape J := by
    by_cases h : Finite J
    · infer_instance
    · have : Infinite J := ⟨h⟩
      let _ := Encodable.ofCountable J
      let _ := Denumerable.ofEncodableOfInfinite J
      exact hasExactLimitsOfShape_of_initial C (Discrete.equivalence (Denumerable.eqv J)).inverse

section EpiMono

open Functor

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

noncomputable instance hasExactColimitsOfShape_discrete_finite (J : Type*) [Finite J] :
    HasExactColimitsOfShape (Discrete J) C where
  preservesFiniteLimits := preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm

noncomputable instance hasExactLimitsOfShape_discrete_finite {J : Type*} [Finite J] :
    HasExactLimitsOfShape (Discrete J) C where
  preservesFiniteColimits := preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim

/--
Checking AB of shape `Discrete ℕ` is enough for countable AB4, provided that the category has
finite biproducts and finite limits.
-/
lemma CountableAB4.of_hasExactColimitsOfShape_nat [HasFiniteLimits C] [HasCountableCoproducts C]
    [HasExactColimitsOfShape (Discrete ℕ) C] : CountableAB4 C := by
  apply (config := { allowSynthFailures := true })
      CountableAB4.of_hasExactColimitsOfShape_nat_and_finite
  exact fun _ ↦ inferInstance

/--
Checking AB* of shape `Discrete ℕ` is enough for countable AB4*, provided that the category has
finite biproducts and finite colimits.
-/
lemma CountableAB4Star.of_hasExactLimitsOfShape_nat [HasFiniteColimits C]
    [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C] : CountableAB4Star C := by
  apply (config := { allowSynthFailures := true })
      CountableAB4Star.of_hasExactLimitsOfShape_nat_and_finite
  exact fun _ ↦ inferInstance

end

variable [Abelian C] (J : Type u') [Category.{v'} J]

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

/--
If `colim` of shape `J` into an abelian category `C` preserves monomorphisms, then `C` has AB of
shape `J`.
-/
lemma hasExactColimitsOfShape_of_preservesMono [HasColimitsOfShape J C]
    [PreservesMonomorphisms (colim (J := J) (C := C))] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := by
    apply (config := { allowSynthFailures := true }) preservesFiniteLimits_of_preservesHomology
    · exact preservesHomology_of_preservesMonos_and_cokernels _
    · exact additive_of_preservesBinaryBiproducts _

/--
If `lim` of shape `J` into an abelian category `C` preserves epimorphisms, then `C` has AB* of
shape `J`.
-/
lemma hasExactLimitsOfShape_of_preservesEpi [HasLimitsOfShape J C]
    [PreservesEpimorphisms (lim (J := J) (C := C))] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := by
    apply (config := { allowSynthFailures := true }) preservesFiniteColimits_of_preservesHomology
    · exact preservesHomology_of_preservesEpis_and_kernels _
    · exact additive_of_preservesBinaryBiproducts _

end EpiMono

end CategoryTheory

/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Finite-limit-preserving presheaves

In this file we prove that if `C` is a small finitely cocomplete category and `A : Cᵒᵖ ⥤ Type u`
is a presheaf such that `CostructuredArrow yoneda A` is filtered (equivalently, the category of
elements of `A` is cofiltered), then `A` preserves finite limits.

This is one of the keys steps of establishing the equivalence `Ind C ≌ (Cᵒᵖ ⥤ₗ Type u)` for a
*small* finitely cocomplete category `C`.

The converse is also true: if `A` preserves finite limits, then `CostructuredArrow yoneda A` is
filtered. In `Limits.Elements` we show that `A.Elements` has finite limits, hence is cofiltered,
from which we can deduce (TODO) that `CostructuredArrow yoneda A` is filtered.

## Implementation notes

The theorem is also true for large categories and the proof given here generalizes to this case on
paper. However, our infrastructure for commuting finite limits of shape `J` and filtered colimits
of shape `K` is fundamentally not equipped to deal with the case where not all limits of shape `K`
exist. In fact, not even the definition `colimitLimitToLimitColimit` can be written down if not
all limits of shape `K` exist. Refactoring this to the level of generality we need would be a major
undertaking. Since the application to the category of Ind-objects only require the case where `C`
is small, we leave this as a TODO.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.3.13
* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1], Proposition 6.1.2
-/

open CategoryTheory Limits

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteColimits C]

namespace CategoryTheory.Limits

variable (A : Cᵒᵖ ⥤ Type u)

namespace PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux

variable {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ Cᵒᵖ)

/-- (Implementation) This is the bifunctor we will apply "filtered colimits commute with finite
limits" to. -/
def functorToInterchange : J ⥤ CostructuredArrow yoneda A ⥤ Type u :=
  K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)

/-- (Implementation) The definition of `functorToInterchange`, up to functor associativity. -/
@[simps!]
def functorToInterchangeIso : functorToInterchange A K ≅
    K ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- (Implementation) One way to express the flipped version of our functor. -/
@[simps!]
def flip_functorToInterchange : (functorToInterchange A K).flip ≅
    ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft J Cᵒᵖ (Type u)).obj K) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- (Implementation) A natural isomorphism we will need to construct `iso`. -/
@[simps! (config := { fullyApplied := false }) hom_app]
noncomputable def isoAux :
  (CostructuredArrow.proj yoneda A ⋙ yoneda ⋙ (evaluation Cᵒᵖ (Type u)).obj (limit K)) ≅
    ((coyoneda ⋙ (whiskeringLeft (CostructuredArrow yoneda A) C (Type u)).obj
      (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- (Implementation) The isomorphism that proves that `A` preserves finite limits. -/
noncomputable def iso [IsFiltered (CostructuredArrow yoneda A)] :
    A.obj (limit K) ≅ limit (K ⋙ A) := calc
  A.obj (limit K) ≅ (colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)).obj (limit K) :=
      (IsColimit.coconePointUniqueUpToIso
        (Presheaf.isColimitTautologicalCocone A) (colimit.isColimit _)).app _
  _ ≅ colimit (((CostructuredArrow.proj yoneda A) ⋙ yoneda) ⋙ (evaluation _ _).obj (limit K)) :=
      (colimitObjIsoColimitCompEvaluation _ _)
  _ ≅ colimit ((CostructuredArrow.proj yoneda A) ⋙ yoneda ⋙ (evaluation _ _).obj (limit K)) :=
      HasColimit.isoOfNatIso (Functor.associator _ _ _)
  _ ≅ colimit
      ((coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
        HasColimit.isoOfNatIso (isoAux A K)
  _ ≅ colimit (limit (K ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)))) :=
        HasColimit.isoOfNatIso (preservesLimitIso _ _)
  _ ≅ colimit (limit (functorToInterchange A K)) :=
        HasColimit.isoOfNatIso (HasLimit.isoOfNatIso (functorToInterchangeIso A K).symm)
  _ ≅ limit (colimit (functorToInterchange A K).flip) := colimitLimitIso _
  _ ≅ limit (colimit
        ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft _ _ _).obj K)) :=
          HasLimit.isoOfNatIso (HasColimit.isoOfNatIso (flip_functorToInterchange A K))
  _ ≅ limit (K ⋙ colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)) :=
        HasLimit.isoOfNatIso
          (colimitCompWhiskeringLeftIsoCompColimit (CostructuredArrow.proj yoneda A ⋙ yoneda) K)
  _ ≅ limit (K ⋙ A) := HasLimit.isoOfNatIso (isoWhiskerLeft _
        (IsColimit.coconePointUniqueUpToIso
          (colimit.isColimit _) (Presheaf.isColimitTautologicalCocone A)))

theorem isIso_post [IsFiltered (CostructuredArrow yoneda A)] : IsIso (limit.post K A) := by
  suffices limit.post K A = (iso A K).hom from this ▸ inferInstance

  -- We will have to use `ι_colimitLimitIso_limit_π` eventually, so let's start by
  -- transforming the goal into something from a colimit to a limit so that we can apply
  -- `limit.hom_ext` and `colimit.hom_ext`.
  dsimp [iso, -Iso.app_hom]
  simp only [Category.assoc]
  rw [← Iso.inv_comp_eq, ← Iso.inv_comp_eq]
  refine limit.hom_ext (fun j => colimit.hom_ext (fun i => ?_))
  simp only [Category.assoc]

  -- `simp` is not too helpful here because we will need to apply `NatTrans.comp_app_assoc`
  -- backwards at certain points, so we rewrite the term manually.
  rw [HasLimit.isoOfNatIso_hom_π, HasLimit.isoOfNatIso_hom_π_assoc, limit.post_π,
    colimitObjIsoColimitCompEvaluation_ι_inv_assoc (CostructuredArrow.proj yoneda A ⋙ yoneda),
    Iso.app_inv, ← NatTrans.comp_app_assoc, colimit.comp_coconePointUniqueUpToIso_inv,
    Presheaf.tautologicalCocone_ι_app , HasColimit.isoOfNatIso_ι_hom_assoc,
    HasLimit.isoOfNatIso_hom_π_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    ι_colimitLimitIso_limit_π_assoc, isoAux_hom_app, ← NatTrans.comp_app_assoc,
    ← NatTrans.comp_app_assoc, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    preservesLimitsIso_hom_π_assoc, Iso.symm_hom,
    ← NatTrans.comp_app_assoc, HasColimit.isoOfNatIso_ι_hom,
    ← NatTrans.comp_app_assoc, Category.assoc,
    ι_colimitCompWhiskeringLeftIsoCompColimit_hom,
    NatTrans.comp_app, Category.assoc, isoWhiskerLeft_hom, NatTrans.comp_app, Category.assoc,
    ← NatTrans.comp_app, ← whiskerLeft_comp, colimit.comp_coconePointUniqueUpToIso_hom]

  have := i.hom.naturality (limit.π K j)
  dsimp only [yoneda_obj_obj, Functor.const_obj_obj] at this
  rw [← this]
  ext
  simp

end PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux

attribute [local instance] PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux.isIso_post

/-- If `C` is a small finitely cocomplete category and `A : Cᵒᵖ ⥤ Type u` is a presheaf such that
`CostructuredArrow yoneda A` is filtered, then `A` preserves finite limits.

One direction of Proposition 3.3.13 of [Kashiwara2006].
-/
noncomputable def preservesFiniteLimitsOfIsFilteredCostructuredArrowYoneda
    [IsFiltered (CostructuredArrow yoneda A)] : PreservesFiniteLimits A where
  preservesFiniteLimits _ _ _ := ⟨fun {_} => preservesLimitOfIsIsoPost _ _⟩

end CategoryTheory.Limits

/-
Copyright (c) 2023 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

open CategoryTheory Limits Functor

universe u

namespace CategoryTheory.Limits.FintypeCat

instance {J : Type} [SmallCategory J] (K : J ⥤ FintypeCat.{u}) (j : J) :
    Finite ((K ⋙ FintypeCat.incl.{u}).obj j) := by
  simp only [comp_obj, FintypeCat.incl_obj]
  infer_instance

/-- Any functor from a finite category to Types that only involves finite objects,
has a finite limit. -/
noncomputable instance finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (limit K) := by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

noncomputable instance inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J FintypeCat.incl.{u} where
  CreatesLimit {K} := createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/- Help typeclass inference to infer creation of finite limits for the forgtful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteLimits

instance {J : Type} [SmallCategory J] [FinCategory J] : HasLimitsOfShape J FintypeCat.{u} where
  has_limit F := hasLimit_of_created F FintypeCat.incl

instance hasFiniteLimits : HasFiniteLimits FintypeCat.{u} where
  out _ := inferInstance

noncomputable instance inclusion_preservesFiniteLimits :
    PreservesFiniteLimits FintypeCat.incl.{u} where
  preservesFiniteLimits _ :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape FintypeCat.incl

/- Help typeclass inference to infer preservation of finite limits for the forgtful functor. -/
noncomputable instance : PreservesFiniteLimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteLimits

/-- The categorical product of a finite family in `FintypeCat` is equivalent to the product
as types. -/
noncomputable def productEquiv {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u}) :
    (∏ᶜ X : FintypeCat) ≃ ∀ i, X i :=
  letI : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i ↦ X i) ≅ (∏ᶜ fun i ↦ X i : Type u) :=
    PreservesProduct.iso FintypeCat.incl (fun i ↦ X i)
  let is₂ : (∏ᶜ fun i ↦ X i : Type u) ≅ Shrink.{u} (∀ i, X i) :=
    Types.Small.productIso (fun i ↦ X i)
  let e : (∀ i, X i) ≃ Shrink.{u} (∀ i, X i) := equivShrink _
  (equivEquivIso.symm is₁).trans ((equivEquivIso.symm is₂).trans e.symm)

@[simp]
lemma productEquiv_apply {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    (x : (∏ᶜ X : FintypeCat)) (i : ι) : productEquiv X x i = Pi.π X i x := by
  simpa [productEquiv] using (elementwise_of% piComparison_comp_π FintypeCat.incl X i) x

@[simp]
lemma productEquiv_symm_comp_π_apply {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    (x : ∀ i, X i) (i : ι) : Pi.π X i ((productEquiv X).symm x) = x i := by
  rw [← productEquiv_apply, Equiv.apply_symm_apply]

instance nonempty_pi_of_nonempty {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    [∀ i, Nonempty (X i)] : Nonempty (∏ᶜ X : FintypeCat.{u}) :=
  (Equiv.nonempty_congr <| productEquiv X).mpr inferInstance

/-- Any functor from a finite category to Types that only involves finite objects,
has a finite colimit. -/
noncomputable instance finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (colimit K) := by
  have : Finite (Types.Quot K) := Quot.finite (Types.Quot.Rel K)
  have : Fintype (Types.Quot K) := Fintype.ofFinite (Types.Quot K)
  exact Fintype.ofEquiv (Types.Quot K) (Types.colimitEquivQuot K).symm

noncomputable instance inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J FintypeCat.incl.{u} where
  CreatesColimit {K} := createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/- Help typeclass inference to infer creation of finite colimits for the forgtful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteColimits

instance {J : Type} [SmallCategory J] [FinCategory J] : HasColimitsOfShape J FintypeCat.{u} where
  has_colimit F := hasColimit_of_created F FintypeCat.incl

instance hasFiniteColimits : HasFiniteColimits FintypeCat.{u} where
  out _ := inferInstance

noncomputable instance inclusion_preservesFiniteColimits :
    PreservesFiniteColimits FintypeCat.incl.{u} where
  preservesFiniteColimits _ :=
    preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape FintypeCat.incl

/- Help typeclass inference to infer preservation of finite colimits for the forgtful functor. -/
noncomputable instance : PreservesFiniteColimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteColimits

lemma jointly_surjective {J : Type*} [Category J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x :=
  let hs := isColimitOfPreserves FintypeCat.incl.{u} h
  Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

end CategoryTheory.Limits.FintypeCat

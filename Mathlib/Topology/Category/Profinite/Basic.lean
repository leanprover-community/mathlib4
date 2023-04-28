/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne

! This file was ported from Lean 3 source module topology.category.Profinite.basic
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.CompHaus.Basic
import Mathbin.Topology.Connected
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.LocallyConstant.Basic
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.CategoryTheory.Fintype

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. finite coproducts
2. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/


universe u

open CategoryTheory

open Topology

/-- The type of profinite topological spaces. -/
structure Profinite where
  toCompHaus : CompHaus
  [IsTotallyDisconnected : TotallyDisconnectedSpace to_CompHaus]
#align Profinite Profinite

namespace Profinite

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    Profinite :=
  ⟨⟨⟨X⟩⟩⟩
#align Profinite.of Profinite.of

instance : Inhabited Profinite :=
  ⟨Profinite.of PEmpty⟩

instance category : Category Profinite :=
  InducedCategory.category toCompHaus
#align Profinite.category Profinite.category

instance concreteCategory : ConcreteCategory Profinite :=
  InducedCategory.concreteCategory _
#align Profinite.concrete_category Profinite.concreteCategory

instance hasForget₂ : HasForget₂ Profinite TopCat :=
  InducedCategory.hasForget₂ _
#align Profinite.has_forget₂ Profinite.hasForget₂

instance : CoeSort Profinite (Type _) :=
  ⟨fun X => X.toCompHaus⟩

instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.IsTotallyDisconnected

-- We check that we automatically infer that Profinite sets are compact and Hausdorff.
example {X : Profinite} : CompactSpace X :=
  inferInstance

example {X : Profinite} : T2Space X :=
  inferInstance

@[simp]
theorem coe_toCompHaus {X : Profinite} : (X.toCompHaus : Type _) = X :=
  rfl
#align Profinite.coe_to_CompHaus Profinite.coe_toCompHaus

@[simp]
theorem coe_id (X : Profinite) : (𝟙 X : X → X) = id :=
  rfl
#align Profinite.coe_id Profinite.coe_id

@[simp]
theorem coe_comp {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl
#align Profinite.coe_comp Profinite.coe_comp

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps]
def profiniteToCompHaus : Profinite ⥤ CompHaus :=
  inducedFunctor _ deriving Full, Faithful
#align Profinite_to_CompHaus profiniteToCompHaus

/-- The fully faithful embedding of `Profinite` in `Top`. This is definitionally the same as the
obvious composite. -/
@[simps]
def Profinite.toTop : Profinite ⥤ TopCat :=
  forget₂ _ _ deriving Full, Faithful
#align Profinite.to_Top Profinite.toTop

@[simp]
theorem Profinite.to_compHausToTop : profiniteToCompHaus ⋙ compHausToTop = Profinite.toTop :=
  rfl
#align Profinite.to_CompHaus_to_Top Profinite.to_compHausToTop

section Profinite

-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u}
    where
  toCompHaus :=
    { toTop := TopCat.of (ConnectedComponents X)
      IsCompact := Quotient.compactSpace
      is_hausdorff := ConnectedComponents.t2 }
  IsTotallyDisconnected := ConnectedComponents.totallyDisconnectedSpace
#align CompHaus.to_Profinite_obj CompHaus.toProfiniteObj

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y)
    where
  toFun f := f.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩
  invFun g :=
    { toFun := Continuous.connectedComponentsLift g.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.2 }
  left_inv f := ContinuousMap.ext <| ConnectedComponents.surjective_coe.forall.2 fun a => rfl
  right_inv f := ContinuousMap.ext fun x => rfl
#align Profinite.to_CompHaus_equivalence Profinite.toCompHausEquivalence

/-- The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl
#align CompHaus.to_Profinite CompHaus.toProfinite

theorem CompHaus.toProfinite_obj' (X : CompHaus) :
    ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl
#align CompHaus.to_Profinite_obj' CompHaus.toProfinite_obj'

/-- Finite types are given the discrete topology. -/
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A :=
  ⊥
#align Fintype.bot_topology FintypeCat.botTopology

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

@[local instance]
theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩
#align Fintype.discrete_topology FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps]
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite
    where
  obj A := Profinite.of A
  map _ _ f := ⟨f⟩
#align Fintype.to_Profinite FintypeCat.toProfinite

end DiscreteTopology

end Profinite

namespace Profinite

-- TODO the following construction of limits could be generalised
-- to allow diagrams in lower universes.
/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`Top.limit_cone`. -/
def limitCone {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u}) : Limits.Cone F
    where
  pt :=
    { toCompHaus := (CompHaus.limitCone.{u, u} (F ⋙ profiniteToCompHaus)).pt
      IsTotallyDisconnected :=
        by
        change TotallyDisconnectedSpace ↥{ u : ∀ j : J, F.obj j | _ }
        exact Subtype.totallyDisconnectedSpace }
  π := { app := (CompHaus.limitCone.{u, u} (F ⋙ profiniteToCompHaus)).π.app }
#align Profinite.limit_cone Profinite.limitCone

/-- The limit cone `Profinite.limit_cone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u}) :
    Limits.IsLimit (limitCone F)
    where
  lift S :=
    (CompHaus.limitConeIsLimit.{u, u} (F ⋙ profiniteToCompHaus)).lift
      (profiniteToCompHaus.mapCone S)
  uniq S m h := (CompHaus.limitConeIsLimit.{u, u} _).uniq (profiniteToCompHaus.mapCone S) _ h
#align Profinite.limit_cone_is_limit Profinite.limitConeIsLimit

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _
#align Profinite.to_Profinite_adj_to_CompHaus Profinite.toProfiniteAdjToCompHaus

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance toCompHaus.reflective : Reflective profiniteToCompHaus
    where toIsRightAdjoint := ⟨CompHaus.toProfinite, Profinite.toProfiniteAdjToCompHaus⟩
#align Profinite.to_CompHaus.reflective Profinite.toCompHaus.reflective

noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _
#align Profinite.to_CompHaus.creates_limits Profinite.toCompHaus.createsLimits

noncomputable instance toTop.reflective : Reflective Profinite.toTop :=
  Reflective.comp profiniteToCompHaus compHausToTop
#align Profinite.to_Top.reflective Profinite.toTop.reflective

noncomputable instance toTop.createsLimits : CreatesLimits Profinite.toTop :=
  monadicCreatesLimits _
#align Profinite.to_Top.creates_limits Profinite.toTop.createsLimits

instance hasLimits : Limits.HasLimits Profinite :=
  has_limits_of_has_limits_creates_limits Profinite.toTop
#align Profinite.has_limits Profinite.hasLimits

instance hasColimits : Limits.HasColimits Profinite :=
  has_colimits_of_reflective profiniteToCompHaus
#align Profinite.has_colimits Profinite.hasColimits

noncomputable instance forgetPreservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply limits.comp_preserves_limits Profinite.toTop (forget TopCat)
#align Profinite.forget_preserves_limits Profinite.forgetPreservesLimits

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- Any morphism of profinite spaces is a closed map. -/
theorem isClosedMap : IsClosedMap f :=
  CompHaus.isClosedMap _
#align Profinite.is_closed_map Profinite.isClosedMap

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
theorem isIso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHaus.isIso_of_bijective (Profinite_to_CompHaus.map f) bij
  is_iso_of_fully_faithful profiniteToCompHaus _
#align Profinite.is_iso_of_bijective Profinite.isIso_of_bijective

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := Profinite.isIso_of_bijective f bij
  as_iso f
#align Profinite.iso_of_bijective Profinite.isoOfBijective

instance forget_reflectsIsomorphisms : ReflectsIsomorphisms (forget Profinite) :=
  ⟨by intro A B f hf <;> exact Profinite.isIso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩
#align Profinite.forget_reflects_isomorphisms Profinite.forget_reflectsIsomorphisms

/-- Construct an isomorphism from a homeomorphism. -/
@[simps Hom inv]
def isoOfHomeo (f : X ≃ₜ Y) : X ≅ Y
    where
  Hom := ⟨f, f.Continuous⟩
  inv := ⟨f.symm, f.symm.Continuous⟩
  hom_inv_id' := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id' := by
    ext x
    exact f.apply_symm_apply x
#align Profinite.iso_of_homeo Profinite.isoOfHomeo

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.Hom
  invFun := f.inv
  left_inv x := by
    change (f.hom ≫ f.inv) x = x
    rw [iso.hom_inv_id, coe_id, id.def]
  right_inv x := by
    change (f.inv ≫ f.hom) x = x
    rw [iso.inv_hom_id, coe_id, id.def]
  continuous_toFun := f.Hom.Continuous
  continuous_invFun := f.inv.Continuous
#align Profinite.homeo_of_iso Profinite.homeoOfIso

/-- The equivalence between isomorphisms in `Profinite` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo : (X ≅ Y) ≃ (X ≃ₜ Y)
    where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
#align Profinite.iso_equiv_homeo Profinite.isoEquivHomeo

theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  by
  constructor
  · contrapose!
    rintro ⟨y, hy⟩ hf
    skip
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).IsClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := is_topological_basis_clopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        dsimp [LocallyConstant.ofClopen]
        rw [if_neg]
        · rfl
        refine' mt (fun α => hVU α) _
        simp only [Set.mem_range_self, not_true, not_false_iff, Set.mem_compl_iff]
      apply_fun fun e => (e y).down  at H
      dsimp [LocallyConstant.ofClopen] at H
      rw [if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map
#align Profinite.epi_iff_surjective Profinite.epi_iff_surjective

theorem mono_iff_injective {X Y : Profinite.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  by
  constructor
  · intro h
    haveI : limits.preserves_limits profiniteToCompHaus := inferInstance
    haveI : mono (Profinite_to_CompHaus.map f) := inferInstance
    rwa [← CompHaus.mono_iff_injective]
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget Profinite).mono_of_mono_map
#align Profinite.mono_iff_injective Profinite.mono_iff_injective

end Profinite


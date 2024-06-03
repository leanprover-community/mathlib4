/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.CategoryTheory.FintypeCat

#align_import topology.category.Profinite.basic from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `TopCat`. The fully faithful functor
is called `Profinite.toTop`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

* Define procategories and prove that `Profinite` is equivalent to `Pro (FintypeCat)`.

## Tags

profinite

-/

-- This was a global instance prior to #13170. We may experiment with removing it.
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

set_option linter.uppercaseLean3 false

universe v u

open CategoryTheory

open Topology

/-- The type of profinite topological spaces. -/
structure Profinite where
  /-- The underlying compact Hausdorff space of a profinite space. -/
  toCompHaus : CompHaus
  /-- A profinite space is totally disconnected. -/
  [isTotallyDisconnected : TotallyDisconnectedSpace toCompHaus]
#align Profinite Profinite

namespace Profinite

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] : Profinite :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩
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

instance : CoeSort Profinite Type* :=
  ⟨fun X => X.toCompHaus⟩

-- Porting note (#10688): This lemma was not needed in mathlib3
@[simp]
lemma forget_ContinuousMap_mk {X Y : Profinite} (f : X → Y) (hf : Continuous f) :
    (forget Profinite).map (ContinuousMap.mk f hf) = f :=
  rfl

instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.isTotallyDisconnected

-- We check that we automatically infer that Profinite sets are compact and Hausdorff.
example {X : Profinite} : CompactSpace X :=
  inferInstance

example {X : Profinite} : T2Space X :=
  inferInstance

-- Porting note: the next four instances were not needed previously.
instance {X : Profinite} : TopologicalSpace ((forget Profinite).obj X) := by
  change TopologicalSpace X
  exact inferInstance

instance {X : Profinite} : TotallyDisconnectedSpace ((forget Profinite).obj X) := by
  change TotallyDisconnectedSpace X
  exact inferInstance

instance {X : Profinite} : CompactSpace ((forget Profinite).obj X) := by
  change CompactSpace X
  exact inferInstance

instance {X : Profinite} : T2Space ((forget Profinite).obj X) := by
  change T2Space X
  exact inferInstance

-- Porting note: removed, as it is a syntactic tautology.
-- @[simp]
-- theorem coe_toCompHaus {X : Profinite} : (X.toCompHaus : Type*) = (X : Type*) :=
--   rfl
-- #align Profinite.coe_to_CompHaus Profinite.coe_toCompHaus

-- Porting note: have changed statement as the original LHS simplified.
@[simp]
theorem coe_id (X : Profinite) : (𝟙 ((forget Profinite).obj X)) = id :=
  rfl
#align Profinite.coe_id Profinite.coe_id

-- Porting note: have changed statement as the original LHS simplified.
@[simp]
theorem coe_comp {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget Profinite).map f ≫ (forget Profinite).map g) = g ∘ f :=
  rfl
#align Profinite.coe_comp Profinite.coe_comp

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps!]
def profiniteToCompHaus : Profinite ⥤ CompHaus :=
  inducedFunctor _
-- Porting note: deriving fails, adding manually.
-- deriving Full, Faithful
#align Profinite_to_CompHaus profiniteToCompHaus

instance : profiniteToCompHaus.Full :=
  show (inducedFunctor _).Full from inferInstance

instance : profiniteToCompHaus.Faithful :=
  show (inducedFunctor _).Faithful from inferInstance

-- Porting note: added, as it is not found otherwise.
instance {X : Profinite} : TotallyDisconnectedSpace (profiniteToCompHaus.obj X) :=
  X.isTotallyDisconnected

/-- The fully faithful embedding of `Profinite` in `TopCat`.
This is definitionally the same as the obvious composite. -/
@[simps!]
def Profinite.toTopCat : Profinite ⥤ TopCat :=
  forget₂ _ _
-- Porting note: deriving fails, adding manually.
-- deriving Full, Faithful
#align Profinite.to_Top Profinite.toTopCat

instance : Profinite.toTopCat.Full :=
  show (inducedFunctor _).Full from inferInstance

instance : Profinite.toTopCat.Faithful :=
  show (inducedFunctor _).Faithful from inferInstance

@[simp]
theorem Profinite.to_compHausToTopCat :
    profiniteToCompHaus ⋙ compHausToTop = Profinite.toTopCat :=
  rfl
#align Profinite.to_CompHaus_to_Top Profinite.to_compHausToTopCat

section Profinite

-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toCompHaus :=
    { toTop := TopCat.of (ConnectedComponents X)
      is_compact := Quotient.compactSpace
      is_hausdorff := ConnectedComponents.t2 }
  isTotallyDisconnected := ConnectedComponents.totallyDisconnectedSpace
#align CompHaus.to_Profinite_obj CompHaus.toProfiniteObj

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := f.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩
  invFun g :=
    { toFun := Continuous.connectedComponentsLift g.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.2 }
  left_inv _ := ContinuousMap.ext <| ConnectedComponents.surjective_coe.forall.2 fun _ => rfl
  right_inv _ := ContinuousMap.ext fun _ => rfl
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
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A := ⊥
#align Fintype.bot_topology FintypeCat.botTopology

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩
#align Fintype.discrete_topology FintypeCat.discreteTopology

attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps!]
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite where
  obj A := Profinite.of A
  map f := ⟨f, by continuity⟩
#align Fintype.to_Profinite FintypeCat.toProfinite

instance : FintypeCat.toProfinite.Faithful where
  map_injective h := funext fun _ ↦ (DFunLike.ext_iff.mp h) _

instance : FintypeCat.toProfinite.Full where
  map_surjective f := ⟨fun x ↦ f x, rfl⟩

end DiscreteTopology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : Limits.Cone F where
  pt :=
    { toCompHaus := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt
      isTotallyDisconnected := by
        change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).π.app
    -- Porting note: was `by tidy`:
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }
#align Profinite.limit_cone Profinite.limitCone

/-- The limit cone `Profinite.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    (CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
      (profiniteToCompHaus.mapCone S)
  uniq S m h := (CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _ h
#align Profinite.limit_cone_is_limit Profinite.limitConeIsLimit

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _
#align Profinite.to_Profinite_adj_to_CompHaus Profinite.toProfiniteAdjToCompHaus

/-- The category of profinite sets is reflective in the category of compact Hausdorff spaces -/
instance toCompHaus.reflective : Reflective profiniteToCompHaus where
  adj := Profinite.toProfiniteAdjToCompHaus
#align Profinite.to_CompHaus.reflective Profinite.toCompHaus.reflective

noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _
#align Profinite.to_CompHaus.creates_limits Profinite.toCompHaus.createsLimits

noncomputable instance toTopCat.reflective : Reflective Profinite.toTopCat :=
  Reflective.comp profiniteToCompHaus compHausToTop
#align Profinite.to_Top.reflective Profinite.toTopCat.reflective

noncomputable instance toTopCat.createsLimits : CreatesLimits Profinite.toTopCat :=
  monadicCreatesLimits _
#align Profinite.to_Top.creates_limits Profinite.toTopCat.createsLimits

instance hasLimits : Limits.HasLimits Profinite :=
  hasLimits_of_hasLimits_createsLimits Profinite.toTopCat
#align Profinite.has_limits Profinite.hasLimits

instance hasColimits : Limits.HasColimits Profinite :=
  hasColimits_of_reflective profiniteToCompHaus
#align Profinite.has_colimits Profinite.hasColimits

noncomputable instance forgetPreservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply Limits.compPreservesLimits Profinite.toTopCat (forget TopCat)
#align Profinite.forget_preserves_limits Profinite.forgetPreservesLimits

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- Any morphism of profinite spaces is a closed map. -/
theorem isClosedMap : IsClosedMap f :=
  CompHaus.isClosedMap _
#align Profinite.is_closed_map Profinite.isClosedMap

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
theorem isIso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHaus.isIso_of_bijective (profiniteToCompHaus.map f) bij
  isIso_of_fully_faithful profiniteToCompHaus _
#align Profinite.is_iso_of_bijective Profinite.isIso_of_bijective

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := Profinite.isIso_of_bijective f bij
  asIso f
#align Profinite.iso_of_bijective Profinite.isoOfBijective

instance forget_reflectsIsomorphisms : (forget Profinite).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  exact Profinite.isIso_of_bijective _ ((isIso_iff_bijective f).mp hf)
#align Profinite.forget_reflects_isomorphisms Profinite.forget_reflectsIsomorphisms

/-- Construct an isomorphism from a homeomorphism. -/
@[simps! hom inv]
noncomputable
def isoOfHomeo (f : X ≃ₜ Y) : X ≅ Y :=
  @asIso _ _ _ _ ⟨f, f.continuous⟩ (@isIso_of_reflects_iso _ _ _ _ _ _ _ profiniteToCompHaus
    (CompHaus.isoOfHomeo f).isIso_hom _)
#align Profinite.iso_of_homeo Profinite.isoOfHomeo

/-- Construct a homeomorphism from an isomorphism. -/
@[simps!]
def homeoOfIso (f : X ≅ Y) : X ≃ₜ Y := CompHaus.homeoOfIso (profiniteToCompHaus.mapIso f)
#align Profinite.homeo_of_iso Profinite.homeoOfIso

/-- The equivalence between isomorphisms in `Profinite` and homeomorphisms
of topological spaces. -/
@[simps!]
noncomputable
def isoEquivHomeo : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
#align Profinite.iso_equiv_homeo Profinite.isoEquivHomeo

theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · -- Porting note: in mathlib3 `contrapose` saw through `Function.Surjective`.
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [g, LocallyConstant.ofIsClopen]
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [comp_apply, ContinuousMap.coe_mk, comp_apply, ContinuousMap.coe_mk,
          Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp only [U, C, Set.mem_range_self, not_true, not_false_iff, Set.mem_compl_iff]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map
#align Profinite.epi_iff_surjective Profinite.epi_iff_surjective

instance {X Y : Profinite} (f : X ⟶ Y) [Epi f] : @Epi CompHaus _ _ _ f := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [CompHaus.epi_iff_surjective, ← epi_iff_surjective]; assumption

instance {X Y : Profinite} (f : X ⟶ Y) [@Epi CompHaus _ _ _ f] : Epi f := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [epi_iff_surjective, ← CompHaus.epi_iff_surjective]; assumption

theorem mono_iff_injective {X Y : Profinite.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro h
    haveI : Limits.PreservesLimits profiniteToCompHaus := inferInstance
    haveI : Mono (profiniteToCompHaus.map f) := inferInstance
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [← CompHaus.mono_iff_injective]
    assumption
  · rw [← CategoryTheory.mono_iff_injective]
    exact (forget Profinite).mono_of_mono_map (f := f)
#align Profinite.mono_iff_injective Profinite.mono_iff_injective

end Profinite

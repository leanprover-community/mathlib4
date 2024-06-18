/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.ClopenBox
/-!

# Light profinite spaces

We construct the category `LightProfinite` of light profinite topological spaces. These are
implemented as totally disconnected second countable compact Hausdorff spaces.

This file also defines the category `LightDiagram`, which consists of those spaces that can be
written as a sequential limit (in `Profinite`) of finite sets.

We define an equivalence of categories `LightProfinite ≌ LightDiagram` and prove that these are
essentially small categories.
-/

/- The basic API for `LightProfinite` is largely copied from the API of `Profinite`;
where possible, try to keep them in sync -/

universe v u

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits Opposite FintypeCat Topology TopologicalSpace

/-- `LightProfinite` is the category of second countable profinite spaces. -/
structure LightProfinite where
  /-- The underlying compact Hausdorff space of a light profinite space. -/
  toCompHaus : CompHaus.{u}
  /-- A light profinite space is totally disconnected -/
  [isTotallyDisconnected : TotallyDisconnectedSpace toCompHaus]
  /-- A light profinite space is second countable -/
  [secondCountable : SecondCountableTopology toCompHaus]

namespace LightProfinite

/--
Construct a term of `LightProfinite` from a type endowed with the structure of a compact,
Hausdorff, totally disconnected and second countable topological space.
-/
def of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] : LightProfinite :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

instance : Inhabited LightProfinite :=
  ⟨LightProfinite.of PEmpty⟩

instance category : Category LightProfinite :=
  InducedCategory.category toCompHaus

instance concreteCategory : ConcreteCategory LightProfinite :=
  InducedCategory.concreteCategory _

instance hasForget₂ : HasForget₂ LightProfinite TopCat :=
  InducedCategory.hasForget₂ _

instance : CoeSort LightProfinite (Type*) :=
  ⟨fun X => X.toCompHaus⟩

instance {X : LightProfinite} : TotallyDisconnectedSpace X :=
  X.isTotallyDisconnected

instance {X : LightProfinite} : SecondCountableTopology X :=
  X.secondCountable

-- We check that we automatically infer that light profinite spaces are compact and Hausdorff.
example {X : LightProfinite} : CompactSpace X :=
  inferInstance

example {X : LightProfinite} : T2Space X :=
  inferInstance

-- Porting note: the next four instances were not needed previously.
instance {X : LightProfinite} : TopologicalSpace ((forget LightProfinite).obj X) :=
  show TopologicalSpace X from inferInstance

instance {X : LightProfinite} : TotallyDisconnectedSpace ((forget LightProfinite).obj X) :=
  show TotallyDisconnectedSpace X from inferInstance

instance {X : LightProfinite} : CompactSpace ((forget LightProfinite).obj X) :=
  show CompactSpace X from inferInstance

instance {X : LightProfinite} : T2Space ((forget LightProfinite).obj X) :=
  show T2Space X from inferInstance

instance {X : LightProfinite} : SecondCountableTopology ((forget LightProfinite).obj X) :=
  show SecondCountableTopology X from inferInstance

@[simp]
theorem coe_id (X : LightProfinite) : (𝟙 ((forget LightProfinite).obj X)) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget LightProfinite).map f ≫ (forget LightProfinite).map g) = g ∘ f :=
  rfl

end LightProfinite

/-- The fully faithful embedding of `LightProfinite` in `Profinite`. -/
@[simps]
def lightToProfinite : LightProfinite ⥤ Profinite where
  obj X := Profinite.of X
  map f := f

/-- `lightToProfinite` is fully faithful. -/
def lightToProfiniteFullyFaithful : lightToProfinite.FullyFaithful := fullyFaithfulInducedFunctor _

instance : lightToProfinite.Faithful := lightToProfiniteFullyFaithful.faithful

instance : lightToProfinite.Full := lightToProfiniteFullyFaithful.full

/-- The fully faithful embedding of `LightProfinite` in `CompHaus`. -/
@[simps!]
def lightProfiniteToCompHaus : LightProfinite ⥤ CompHaus :=
  inducedFunctor _

/-- `lightProfiniteToCompHaus` is fully faithful. -/
def lightProfiniteToCompHausFullyFaithful : lightProfiniteToCompHaus.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : lightProfiniteToCompHaus.Full := lightProfiniteToCompHausFullyFaithful.full

instance : lightProfiniteToCompHaus.Faithful := lightProfiniteToCompHausFullyFaithful.faithful

instance {X : LightProfinite} : TotallyDisconnectedSpace (lightProfiniteToCompHaus.obj X) :=
  X.isTotallyDisconnected

instance {X : LightProfinite} : SecondCountableTopology (lightProfiniteToCompHaus.obj X) :=
  X.secondCountable

/-- The fully faithful embedding of `LightProfinite` in `TopCat`.
This is definitionally the same as the obvious composite. -/
@[simps!]
def LightProfinite.toTopCat : LightProfinite ⥤ TopCat :=
  forget₂ _ _
-- Porting note: deriving fails, adding manually.
-- deriving Full, Faithful

/-- `LightProfinite.toTopCat` is fully faithful. -/
def LightProfinite.toTopCatFullyFaithful : LightProfinite.toTopCat.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : LightProfinite.toTopCat.Full := LightProfinite.toTopCatFullyFaithful.full

instance : LightProfinite.toTopCat.Faithful := LightProfinite.toTopCatFullyFaithful.faithful

@[simp]
theorem LightProfinite.toCompHaus_comp_toTop :
    lightProfiniteToCompHaus ⋙ compHausToTop = LightProfinite.toTopCat :=
  rfl

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology
attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `LightProfinite`, endowing a finite type with the
discrete topology. -/
@[simps!]
def FintypeCat.toLightProfinite : FintypeCat ⥤ LightProfinite where
  obj A := LightProfinite.of A
  map f := ⟨f, by continuity⟩

/-- `FintypeCat.toLightProfinite` is fully faithful. -/
def FintypeCat.toLightProfiniteFullyFaithful : toLightProfinite.FullyFaithful where
  preimage f := (f : _ → _)
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : FintypeCat.toLightProfinite.Faithful :=
  FintypeCat.toLightProfiniteFullyFaithful.faithful

instance : FintypeCat.toLightProfinite.Full :=
  FintypeCat.toLightProfiniteFullyFaithful.full

end DiscreteTopology

namespace LightProfinite

instance {J : Type v} [SmallCategory J] (F : J ⥤ LightProfinite.{max u v}) :
    TotallyDisconnectedSpace
      (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop := by
  change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
  exact Subtype.totallyDisconnectedSpace

/-- An explicit limit cone for a functor `F : J ⥤ LightProfinite`, for a countable category `J`
  defined in terms of `CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightProfinite.{max u v}) :
    Limits.Cone F where
  pt :=
    { toCompHaus := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt
      secondCountable := by
        change SecondCountableTopology ({ u : ∀ j : J, F.obj j | _ } : Type _)
        apply inducing_subtype_val.secondCountableTopology }
  π :=
  { app := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).π.app
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/-- The limit cone `LightProfinite.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightProfinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    (CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightProfiniteToCompHaus)).lift
      (lightProfiniteToCompHaus.mapCone S)
  uniq S m h := (CompHaus.limitConeIsLimit.{v, u} _).uniq (lightProfiniteToCompHaus.mapCone S) _ h

noncomputable instance createsCountableLimits {J : Type v} [SmallCategory J] [CountableCategory J] :
    CreatesLimitsOfShape J lightToProfinite.{max v u} where
  CreatesLimit {F} :=
    have : HasLimitsOfSize Profinite := hasLimitsOfSizeShrink _
    createsLimitOfFullyFaithfulOfIso (limitCone.{v, u} F).pt <|
      (Profinite.limitConeIsLimit.{v, u} (F ⋙ lightToProfinite)).conePointUniqueUpToIso
        (limit.isLimit _)

instance : HasCountableLimits LightProfinite where
  out _ := { has_limit := fun F ↦ ⟨limitCone F, limitConeIsLimit F⟩ }

variable {X Y : LightProfinite.{u}} (f : X ⟶ Y)

/-- Any morphism of light profinite spaces is a closed map. -/
theorem isClosedMap : IsClosedMap f :=
  CompHaus.isClosedMap _

/-- Any continuous bijection of light profinite spaces induces an isomorphism. -/
theorem isIso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHaus.isIso_of_bijective (lightProfiniteToCompHaus.map f) bij
  isIso_of_fully_faithful lightProfiniteToCompHaus _

/-- Any continuous bijection of light profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := LightProfinite.isIso_of_bijective f bij
  asIso f

instance forget_reflectsIsomorphisms : (forget LightProfinite).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  exact LightProfinite.isIso_of_bijective _ ((isIso_iff_bijective f).mp hf)

/-- Construct an isomorphism from a homeomorphism. -/
@[simps! hom inv]
noncomputable
def isoOfHomeo (f : X ≃ₜ Y) : X ≅ Y :=
  lightProfiniteToCompHausFullyFaithful.preimageIso (CompHaus.isoOfHomeo f)

/-- Construct a homeomorphism from an isomorphism. -/
@[simps!]
def homeoOfIso (f : X ≅ Y) : X ≃ₜ Y := CompHaus.homeoOfIso (lightProfiniteToCompHaus.mapIso f)

/-- The equivalence between isomorphisms in `LightProfinite` and homeomorphisms
of topological spaces. -/
@[simps!]
noncomputable
def isoEquivHomeo : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

theorem epi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · -- Note: in mathlib3 `contrapose` saw through `Function.Surjective`.
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
        erw [CategoryTheory.comp_apply, ContinuousMap.coe_mk,
          CategoryTheory.comp_apply, ContinuousMap.coe_mk, Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp only [U, C, Set.mem_range_self, not_true, not_false_iff, Set.mem_compl_iff]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

instance {X Y : LightProfinite} (f : X ⟶ Y) [Epi f] : @Epi CompHaus _ _ _ f := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [CompHaus.epi_iff_surjective, ← epi_iff_surjective]; assumption

instance {X Y : LightProfinite} (f : X ⟶ Y) [@Epi CompHaus _ _ _ f] : Epi f := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [epi_iff_surjective, ← CompHaus.epi_iff_surjective]; assumption

theorem mono_iff_injective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : of PUnit.{u+1} ⟶ X := ⟨fun _ => x₁, continuous_const⟩
    let g₂ : of PUnit.{u+1} ⟶ X := ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by
      ext
      exact h
    rw [cancel_mono] at this
    apply_fun fun e => e PUnit.unit at this
    exact this
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget LightProfinite).mono_of_mono_map

end LightProfinite

/-- A structure containing the data of sequential limit in `Profinite` of finite sets. -/
structure LightDiagram : Type (u+1) where
  /-- The indexing diagram. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat
  /-- The limit cone. -/
  cone : Cone (diagram ⋙ FintypeCat.toProfinite.{u})
  /-- The limit cone is limiting. -/
  isLimit : IsLimit cone

namespace LightDiagram

/-- The underlying `Profinite` of a `LightDiagram`. -/
def toProfinite (S : LightDiagram) : Profinite := S.cone.pt

@[simps!]
instance : Category LightDiagram := InducedCategory.category toProfinite

instance concreteCategory : ConcreteCategory LightDiagram := InducedCategory.concreteCategory _

end LightDiagram

/-- The fully faithful embedding `LightDiagram ⥤ Profinite` -/
@[simps!]
def lightDiagramToProfinite : LightDiagram ⥤ Profinite := inducedFunctor _

instance : lightDiagramToProfinite.Faithful := show (inducedFunctor _).Faithful from inferInstance

instance : lightDiagramToProfinite.Full := show (inducedFunctor _).Full from inferInstance

instance {X : LightDiagram} : TopologicalSpace ((forget LightDiagram).obj X) :=
  (inferInstance : TopologicalSpace X.cone.pt)

instance {X : LightDiagram} : TotallyDisconnectedSpace ((forget LightDiagram).obj X) :=
  (inferInstance : TotallyDisconnectedSpace X.cone.pt)

instance {X : LightDiagram} : CompactSpace ((forget LightDiagram).obj X) :=
  (inferInstance : CompactSpace X.cone.pt )

instance {X : LightDiagram} : T2Space ((forget LightDiagram).obj X) :=
  (inferInstance : T2Space X.cone.pt )

namespace LightProfinite

instance (S : LightProfinite) : Countable (Clopens S) := by
  rw [TopologicalSpace.Clopens.countable_iff_second_countable]
  infer_instance

instance instCountableDiscreteQuotient (S : LightProfinite)  :
    Countable (DiscreteQuotient ((lightToProfinite.obj S))) :=
  (DiscreteQuotient.finsetClopens_inj S).countable

/-- A profinite space which is light gives rise to a light profinite space. -/
noncomputable def toLightDiagram (S : LightProfinite.{u}) : LightDiagram.{u} where
  diagram := sequentialFunctor _ ⋙ (lightToProfinite.obj S).fintypeDiagram
  cone := (Functor.Initial.limitConeComp (sequentialFunctor _) (lightToProfinite.obj S).lim).cone
  isLimit :=
    (Functor.Initial.limitConeComp (sequentialFunctor _) (lightToProfinite.obj S).lim).isLimit

end LightProfinite

/-- The functor part of the equivalence `LightProfinite ≌ LightDiagram` -/
@[simps]
noncomputable def lightProfiniteToLightDiagram : LightProfinite.{u} ⥤ LightDiagram.{u} where
  obj X := X.toLightDiagram
  map f := f

open scoped Classical in
instance (S : LightDiagram.{u}) : SecondCountableTopology S.cone.pt := by
  rw [← TopologicalSpace.Clopens.countable_iff_second_countable]
  refine @Countable.of_equiv _ _ ?_ (LocallyConstant.equivClopens (X := S.cone.pt))
  refine @Function.Surjective.countable
    (Σ (n : ℕ), LocallyConstant ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩) (Fin 2)) _ ?_ ?_ ?_
  · apply @instCountableSigma _ _ _ ?_
    intro n
    refine @Finite.to_countable _ ?_
    refine @Finite.of_injective _ ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩ → (Fin 2)) ?_ _
      LocallyConstant.coe_injective
    refine @Pi.finite _ _ ?_ _
    simp only [Functor.comp_obj, toProfinite_obj_toCompHaus_toTop_α]
    infer_instance
  · exact fun a ↦ a.snd.comap (S.cone.π.app ⟨a.fst⟩)
  · intro a
    obtain ⟨n, g, h⟩ := Profinite.exists_locallyConstant S.cone S.isLimit a
    exact ⟨⟨unop n, g⟩, h.symm⟩

/-- The inverse part of the equivalence `LightProfinite ≌ LightDiagram` -/
@[simps]
def lightDiagramToLightProfinite : LightDiagram.{u} ⥤ LightProfinite.{u} where
  obj X := LightProfinite.of X.cone.pt
  map f := f

/-- The equivalence of categories `LightProfinite ≌ LightDiagram` -/
noncomputable def LightProfinite.equivDiagram : LightProfinite.{u} ≌ LightDiagram.{u} where
  functor := lightProfiniteToLightDiagram
  inverse := lightDiagramToLightProfinite
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun X ↦ lightDiagramToProfinite.preimageIso (Iso.refl _)) (by
      intro _ _ f
      simp only [Functor.comp_obj, lightDiagramToLightProfinite_obj,
        lightProfiniteToLightDiagram_obj, Functor.id_obj, Functor.comp_map,
        lightDiagramToLightProfinite_map, lightProfiniteToLightDiagram_map,
        lightDiagramToProfinite_obj, Functor.preimageIso_hom, Iso.refl_hom, Functor.id_map]
      erw [lightDiagramToProfinite.preimage_id, lightDiagramToProfinite.preimage_id,
        Category.comp_id f])
  functor_unitIso_comp _ := by simpa using lightDiagramToProfinite.preimage_id

instance : lightProfiniteToLightDiagram.IsEquivalence :=
  show LightProfinite.equivDiagram.functor.IsEquivalence from inferInstance

instance : lightDiagramToLightProfinite.IsEquivalence :=
  show LightProfinite.equivDiagram.inverse.IsEquivalence from inferInstance

noncomputable section EssentiallySmall

open LightDiagram

/--
This is an auxiliary definition used to show that `LightDiagram` is essentially small.

Note that below we put a category instance on this structure which is completely different from the
category instance on `ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}`. Neither the morphisms nor the objects are the
same.
-/
structure LightDiagram' : Type u where
  /-- The diagram takes values in a small category equivalent to `FintypeCat`. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}

/-- A `LightDiagram'` yields a `Profinite`. -/
def LightDiagram'.toProfinite (S : LightDiagram') : Profinite :=
  limit (S.diagram  ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

instance : Category LightDiagram' := InducedCategory.category LightDiagram'.toProfinite

/-- The functor part of the equivalence of categories `LightDiagram' ≌ LightDiagram`. -/
def LightDiagram'.toLightFunctor : LightDiagram'.{u} ⥤ LightDiagram.{u} where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

instance : LightDiagram'.toLightFunctor.{u}.Faithful := ⟨id⟩

instance : LightDiagram'.toLightFunctor.{u}.Full where
  map_surjective f := ⟨f, rfl⟩

instance : LightDiagram'.toLightFunctor.{u}.EssSurj where
  mem_essImage Y :=
    ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨lightDiagramToProfinite.preimageIso (
      (Limits.lim.mapIso (isoWhiskerRight ((isoWhiskerLeft Y.diagram
      Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso Y.isLimit)⟩⟩

instance : LightDiagram'.toLightFunctor.IsEquivalence where

/-- The equivalence beween `LightDiagram` and a small category. -/
def LightDiagram.equivSmall : LightDiagram.{u} ≌ LightDiagram'.{u} :=
  LightDiagram'.toLightFunctor.asEquivalence.symm

instance : EssentiallySmall LightDiagram.{u} where
  equiv_smallCategory := ⟨LightDiagram', inferInstance, ⟨LightDiagram.equivSmall⟩⟩

instance : EssentiallySmall LightProfinite.{u} where
  equiv_smallCategory := ⟨LightDiagram', inferInstance,
    ⟨LightProfinite.equivDiagram.trans LightDiagram.equivSmall⟩⟩

end EssentiallySmall

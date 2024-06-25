/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected compact Hausdorff spaces.

## Overview

This file defines the type `Stonean` of all extremally (note: not "extremely"!)
disconnected compact Hausdorff spaces, gives it the structure of a large category,
and proves some basic observations about this category and various functors from it.

The Lean implementation: a term of type `Stonean` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

## Main definitions

* `Stonean` : the category of extremally disconnected compact Hausdorff spaces.
* `Stonean.toCompHaus` : the forgetful functor `Stonean ⥤ CompHaus` from Stonean
  spaces to compact Hausdorff spaces
* `Stonean.toProfinite` : the functor from Stonean spaces to profinite spaces.

-/
universe u

open CategoryTheory
open scoped Topology

-- This was a global instance prior to #13170. We may experiment with removing it.
attribute [local instance] ConcreteCategory.instFunLike

/-- `Stonean` is the category of extremally disconnected compact Hausdorff spaces. -/
structure Stonean where
  /-- The underlying compact Hausdorff space of a Stonean space. -/
  compHaus : CompHaus.{u}
  /-- A Stonean space is extremally disconnected -/
  [extrDisc : ExtremallyDisconnected compHaus]

namespace CompHaus

/-- `Projective` implies `ExtremallyDisconnected`. -/
instance (X : CompHaus.{u}) [Projective X] : ExtremallyDisconnected X := by
  apply CompactT2.Projective.extremallyDisconnected
  intro A B _ _ _ _ _ _ f g hf hg hsurj
  have : CompactSpace (TopCat.of A) := by assumption
  have : T2Space (TopCat.of A) := by assumption
  have : CompactSpace (TopCat.of B) := by assumption
  have : T2Space (TopCat.of B) := by assumption
  let A' : CompHaus := ⟨TopCat.of A⟩
  let B' : CompHaus := ⟨TopCat.of B⟩
  let f' : X ⟶ B' := ⟨f, hf⟩
  let g' : A' ⟶ B' := ⟨g,hg⟩
  have : Epi g' := by
    rw [CompHaus.epi_iff_surjective]
    assumption
  obtain ⟨h, hh⟩ := Projective.factors f' g'
  refine ⟨h, h.2, ?_⟩
  ext t
  apply_fun (fun e => e t) at hh
  exact hh

/-- `Projective` implies `Stonean`. -/
@[simps!]
def toStonean (X : CompHaus.{u}) [Projective X] :
    Stonean where
  compHaus := X

end CompHaus

namespace Stonean

/-- Stonean spaces form a large category. -/
instance : LargeCategory Stonean.{u} :=
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

/-- The (forgetful) functor from Stonean spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : Stonean.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

/-- The forgetful functor `Stonean ⥤ CompHaus` is fully faithful. -/
def fullyFaithfulToCompHaus : toCompHaus.FullyFaithful  :=
  fullyFaithfulInducedFunctor _

/-- Construct a term of `Stonean` from a type endowed with the structure of a
compact, Hausdorff and extremally disconnected topological space.
-/
def of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : Stonean :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

/-- The forgetful functor `Stonean ⥤ CompHaus` is full. -/
instance : toCompHaus.Full := fullyFaithfulToCompHaus.full

/-- The forgetful functor `Stonean ⥤ CompHaus` is faithful. -/
instance : toCompHaus.Faithful := fullyFaithfulToCompHaus.faithful

/-- Stonean spaces are a concrete category. -/
instance : ConcreteCategory Stonean where
  forget := toCompHaus ⋙ forget _

instance : CoeSort Stonean.{u} (Type u) := ConcreteCategory.hasCoeToSort _
instance {X Y : Stonean.{u}} : FunLike (X ⟶ Y) X Y := ConcreteCategory.instFunLike

/-- Stonean spaces are topological spaces. -/
instance instTopologicalSpace (X : Stonean.{u}) : TopologicalSpace X :=
  show TopologicalSpace X.compHaus from inferInstance

/-- Stonean spaces are compact. -/
instance (X : Stonean.{u}) : CompactSpace X :=
  show CompactSpace X.compHaus from inferInstance

/-- Stonean spaces are Hausdorff. -/
instance (X : Stonean.{u}) : T2Space X :=
  show T2Space X.compHaus from inferInstance

instance (X : Stonean.{u}) : ExtremallyDisconnected X :=
  X.2

/-- The functor from Stonean spaces to profinite spaces. -/
@[simps]
def toProfinite : Stonean.{u} ⥤ Profinite.{u} where
  obj X :=
    { toCompHaus := X.compHaus,
      isTotallyDisconnected := show TotallyDisconnectedSpace X from inferInstance }
  map f := f

/-- The functor from Stonean spaces to profinite spaces is full. -/
instance : toProfinite.Full where
  map_surjective f := ⟨f, rfl⟩

/-- The functor from Stonean spaces to profinite spaces is faithful. -/
instance : toProfinite.Faithful := {}

/-- The functor from Stonean spaces to compact Hausdorff spaces
    factors through profinite spaces. -/
example : toProfinite ⋙ profiniteToCompHaus = toCompHaus :=
  rfl

/-- Construct an isomorphism from a homeomorphism. -/
@[simps! hom inv]
noncomputable
def isoOfHomeo {X Y : Stonean} (f : X ≃ₜ Y) : X ≅ Y :=
  @asIso _ _ _ _ ⟨f, f.continuous⟩
  (@isIso_of_reflects_iso _ _ _ _ _ _ _ toCompHaus (CompHaus.isoOfHomeo f).isIso_hom _)

/-- Construct a homeomorphism from an isomorphism. -/
@[simps!]
def homeoOfIso {X Y : Stonean} (f : X ≅ Y) : X ≃ₜ Y := CompHaus.homeoOfIso (toCompHaus.mapIso f)

/-- The equivalence between isomorphisms in `Stonean` and homeomorphisms
of topological spaces. -/
@[simps!]
noncomputable
def isoEquivHomeo {X Y : Stonean} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

/--
A finite discrete space as a Stonean space.
-/
def mkFinite (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X] : Stonean where
  compHaus := CompHaus.of X
  extrDisc := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)

/--
A morphism in `Stonean` is an epi iff it is surjective.

TODO: prove that `forget Stonean` preserves pushouts (in fact it preserves all finite colimits)
and deduce this from general lemmas about concrete categories.
-/
lemma epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  refine ⟨?_, ConcreteCategory.epi_of_surjective _⟩
  dsimp [Function.Surjective]
  intro h y
  by_contra! hy
  let C := Set.range f
  have hC : IsClosed C := (isCompact_range f.continuous).isClosed
  let U := Cᶜ
  have hUy : U ∈ 𝓝 y := by
    simp only [C, Set.mem_range, hy, exists_false, not_false_eq_true, hC.compl_mem_nhds]
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) :=
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext -- why is `ext` not doing this automatically?
    change 1 = ite _ _ _ -- why is `dsimp` not getting me here?
    rw [if_neg]
    refine mt (hVU ·) ?_ -- what would be an idiomatic tactic for this step?
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H -- why is `dsimp at H` not getting me here?
  rw [if_pos hyV] at H
  exact one_ne_zero H

instance {X Y : Stonean} (f : X ⟶ Y) [Epi f] : @Epi CompHaus _ _ _ f := by
  rw [CompHaus.epi_iff_surjective]
  rwa [Stonean.epi_iff_surjective] at *

instance {X Y : Stonean} (f : X ⟶ Y) [@Epi CompHaus _ _ _ f] : Epi f := by
  rw [Stonean.epi_iff_surjective]
  rwa [CompHaus.epi_iff_surjective] at *

/-- Every Stonean space is projective in `CompHaus` -/
instance instProjectiveCompHausCompHaus (X : Stonean) : Projective X.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Profinite` -/
instance (X : Stonean) : Projective (toProfinite.obj X) where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected (toProfinite.obj X) := X.extrDisc
    have hf : Function.Surjective f := by rwa [← Profinite.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Stonean`. -/
instance (X : Stonean) : Projective X where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : Function.Surjective f := by rwa [← Stonean.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is a Stonean space equipped with an epimorphism
  down to `X` (see `CompHaus.presentation.π` and `CompHaus.presentation.epi_π`). It is a
  "constructive" witness to the fact that `CompHaus` has enough projectives. -/
noncomputable
def presentation (X : CompHaus) : Stonean where
  compHaus := (projectivePresentation X).p
  extrDisc := by
    refine CompactT2.Projective.extremallyDisconnected
      (@fun Y Z _ _ _ _ _ _ f g hfcont hgcont hgsurj => ?_)
    let g₁ : (CompHaus.of Y) ⟶ (CompHaus.of Z) := ⟨g, hgcont⟩
    let f₁ : (projectivePresentation X).p ⟶ (CompHaus.of Z) := ⟨f, hfcont⟩
    have hg₁ : Epi g₁ := (epi_iff_surjective _).2 hgsurj
    refine ⟨Projective.factorThru f₁ g₁, (Projective.factorThru f₁ g₁).2, funext (fun _ => ?_)⟩
    change (Projective.factorThru f₁ g₁ ≫ g₁) _ = f _
    rw [Projective.factorThru_comp]
    rfl

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : CompHaus) : X.presentation.compHaus ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `CompHaus` and `e : Z ⟶ Y` is arbitrary, then
`lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It exists because
`Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X⟩
    show Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus

end CompHaus

namespace Profinite

/-- If `X` is profinite, `presentation X` is a Stonean space equipped with an epimorphism down to
    `X` (see `Profinite.presentation.π` and `Profinite.presentation.epi_π`). -/
noncomputable
def presentation (X : Profinite) : Stonean where
  compHaus := X.toCompHaus.projectivePresentation.p
  extrDisc := X.toCompHaus.presentation.extrDisc

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : Profinite) : Stonean.toProfinite.obj X.presentation ⟶ X :=
  X.toCompHaus.projectivePresentation.f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : Profinite) : Epi (π X) := by
  have := X.toCompHaus.projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `Profinite` and `e : Z ⟶ Y` is arbitrary,
then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It is
`CompHaus.lift e f` as a morphism in `Profinite`.
-/
noncomputable
def lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Stonean.toProfinite.obj Z ⟶ X := CompHaus.lift e f

@[simp, reassoc]
lemma lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
    [Epi f] : lift e f ≫ f = e := CompHaus.lift_lifts _ _

lemma projective_of_extrDisc {X : Profinite.{u}} (hX : ExtremallyDisconnected X) :
    Projective X := by
  show Projective (Stonean.toProfinite.obj ⟨X.toCompHaus⟩)
  exact inferInstance

end Profinite

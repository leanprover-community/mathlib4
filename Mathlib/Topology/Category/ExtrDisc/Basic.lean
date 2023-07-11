/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected sets.

## Overview

This file defines the type `ExtrDisc` of all extremally (note: not "extremely"!)
disconnected spaces, and gives it the structure of a large category.

The Lean implementation: a term of type `ExtrDisc` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

This file defines the type of all extremally disconnected spaces, gives it the
structure of a large category, and proves some basic observations about this
category and various functors from it.

## Main definitions

* `ExtrDisc` : the category of extremally disconnected spaces.
* `ExtrDisc.toCompHaus` : the forgetful functor `ExtrDisc ⥤ CompHaus` from extremally disconnected
  spaces to compact Hausdorff spaces
* `ExtrDisc.toProfinite` : the functor from extremally disconnected spaces to profinite spaces.

-/
universe u

open CategoryTheory

/-- `ExtrDisc` is the category of extremally disconnected spaces. -/
structure ExtrDisc where
  compHaus : CompHaus.{u}
  [extrDisc : ExtremallyDisconnected compHaus]

-- the fields of the structure don't need docstrings
attribute [nolint docBlame] ExtrDisc.compHaus ExtrDisc.extrDisc

namespace CompHaus

/-- Projective implies ExtrDisc. -/
@[simps!]
def toExtrDisc (X : CompHaus.{u}) [Projective X] :
    ExtrDisc where
  compHaus := X
  extrDisc := by
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
    obtain ⟨h,hh⟩ := Projective.factors f' g'
    refine ⟨h,h.2,?_⟩
    ext t
    apply_fun (fun e => e t) at hh
    exact hh


end CompHaus

namespace ExtrDisc

/-- Extremally disconnected spaces form a large category. -/
instance : LargeCategory ExtrDisc.{u} :=
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

/-- The (forgetful) functor from extremally disconnected spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

/-- Construct a term of `ExtrDisc` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : ExtrDisc :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

/-- The forgetful functor `ExtrDisc ⥤ CompHaus` is full. -/
instance : Full toCompHaus where
  preimage := fun f => f
  witness := fun f => by simp


/-- The forgetful functor `ExtrDisc ⥤ CompHaus` is faithful. -/
instance : Faithful toCompHaus where
  map_injective := by
    intro X Y a b h
    simp only [inducedFunctor_obj, inducedFunctor_map] at h
    exact h

/-- Extremally disconnected spaces are a concrete category. -/
instance : ConcreteCategory ExtrDisc where
  forget := toCompHaus ⋙ forget _

instance : CoeSort ExtrDisc.{u} (Type u) := ConcreteCategory.hasCoeToSort _
instance {X Y : ExtrDisc.{u}} : FunLike (X ⟶ Y) X (fun _ => Y) := ConcreteCategory.funLike

/-- Extremally disconnected spaces are topological spaces. -/
instance instTopologicalSpace (X : ExtrDisc.{u}) : TopologicalSpace X :=
  show TopologicalSpace X.compHaus from inferInstance

/-- Extremally disconnected spaces are compact. -/
instance (X : ExtrDisc.{u}) : CompactSpace X :=
  show CompactSpace X.compHaus from inferInstance

/-- Extremally disconnected spaces are Hausdorff. -/
instance (X : ExtrDisc.{u}) : T2Space X :=
  show T2Space X.compHaus from inferInstance

instance (X : ExtrDisc.{u}) : ExtremallyDisconnected X :=
  X.2

/-- The functor from extremally disconnected spaces to profinite spaces. -/
@[simps]
def toProfinite : ExtrDisc.{u} ⥤ Profinite.{u} where
  obj X := {
    toCompHaus := X.compHaus,
    IsTotallyDisconnected := show TotallyDisconnectedSpace X from inferInstance }
  map f := f

/-- The functor from extremally disconnected spaces to profinite spaces is full. -/
instance : Full toProfinite := by
  fconstructor; intro X Y f; exact f; simp

/-- The functor from extremally disconnected spaces to profinite spaces is faithful. -/
instance : Faithful toProfinite := by
  fconstructor; intro X Y f g h; assumption

/-- The functor from extremally disconnected spaces to compact Hausdorff spaces
    factors through profinite spaces. -/
instance : toProfinite ⋙ profiniteToCompHaus = toCompHaus :=
  rfl

/-- Every extremally disconnected space is projective in `CompHaus` -/
instance (X : ExtrDisc) : Projective X.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : f.1.Surjective
    · rwa [CompHaus.epi_iff_surjective] at *
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end ExtrDisc

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is an extremally disconnected space
  equipped with an epimorphism down to `X`. It is a "constructive" witness to the
  fact that `CompHaus` has enough projectives.  -/
noncomputable
def presentation (X : CompHaus) : ExtrDisc where
  compHaus := (projectivePresentation X).p
  extrDisc := by
    refine' CompactT2.Projective.extremallyDisconnected
      (@fun Y Z _ _ _ _ _ _ f g hfcont hgcont hgsurj => _)
    let g₁ : (CompHaus.of Y) ⟶ (CompHaus.of Z) := ⟨g, hgcont⟩
    let f₁ : (projectivePresentation X).p ⟶ (CompHaus.of Z) := ⟨f, hfcont⟩
    have hg₁ : Epi g₁ := (epi_iff_surjective _).2 hgsurj
    refine' ⟨Projective.factorThru f₁ g₁, (Projective.factorThru f₁ g₁).2, funext (fun _ => _)⟩
    change (Projective.factorThru f₁ g₁ ≫ g₁) _ = f _
    rw [Projective.factorThru_comp]
    rfl

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentationπ (X : CompHaus) : X.presentation.compHaus ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance epiPresentπ (X : CompHaus) : Epi X.presentationπ :=
  (projectivePresentation X).epi

/--

               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y

If `Z` is extremally disconnected, X, Y are compact Hausdorff, if `f : X ⟶ Y` is an epi and
`e : Z ⟶ Y` is arbitrary, then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism
`Z ⟶ X`. It exists because `Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] : Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

namespace CompHaus

lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toExtrDisc
    infer_instance
  · intro h
    let X' : ExtrDisc := ⟨X⟩
    show Projective X'.compHaus
    apply ExtrDisc.instProjectiveCompHausCategoryCompHaus

end CompHaus

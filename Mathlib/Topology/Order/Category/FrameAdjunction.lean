/-
Copyright (c) 2023 Anne Baanen, Sam v. Gool, Leo Mayer, Brendan S. Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Sam v. Gool, Leo Mayer, Brendan S. Murphy
-/
import Mathlib.Topology.Category.Locale

/-!
# Adjunction between Locales and Topological Spaces

This file defines contravariant functors between the categories of Frames and Topological Spaces
and proves that they form an adjunction.

## Main declarations

* `pt`: the *points* functor from the category of locales to the category of topological spaces.
* `topToLocale`: the forgetful functor from the category of topological spaces to the category of
  locales.

- `locale_top_adjunction`: the theorem that topToLocale is left adjoint to pt.

## Motivation

This adjunction provides a framework in which several Stone-type dualities fit.

## Implementation notes

- In naming the various functions below, we follow common terminology and reserve the word *point*
  for an inhabitant of a type `X` which is a topological space, while we use the word *element* for
  an inhabitant of a type `L` which is a frame.


## References

* [J. Picado and A. Pultr, Frames and Locales: topology without points][picado2011frames]

## Tags

topological space, frame, Stone duality, adjunction, points
-/

open CategoryTheory Order Set Topology TopologicalSpace

/- ### Definition of the points functor `pt` --/

section pt_definition
variable (L L' : Type*) [CompleteLattice L] [CompleteLattice L']

/-- The type of points of a frame `L`, where a *point* of a frame is, by definition, a frame
homomorphism from `L` to the frame `Prop`. -/
@[reducible]
def PT := FrameHom L Prop

/-- The frame homomorphism from a frame `L` to the frame of sets of points of `L`. -/
def open_of_element_hom : FrameHom L (Set (PT L)) where
  toFun u := {x | x u}
  map_inf' a b := by simp; rfl
  map_top' := by simp; rfl
  map_sSup' S := by ext; simp

-- TODO: Merging those `variable` breaks
variable {L L'}
variable {U : Set (PT L)}

namespace PT

/-- The topology on the set of points of the frame `L`. -/
instance instTopologicalSpace : TopologicalSpace (PT L) where
  IsOpen s := ∃ u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp [Prop.top_eq_true]⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, setOf_exists, hf, sUnion_eq_biUnion]

/-- Characterizes when a subset of the space of points is open. -/
lemma isOpen_iff : IsOpen U ↔ ∃ u : L, {x | x u} = U := Iff.rfl

/-- The action of the functor `PT` on frame homomorphisms. -/
@[reducible]
def map (f : FrameHom L' L) : C(PT L, PT L') where
  toFun := fun p ↦ p.comp f
  continuous_toFun := continuous_def.2 $ by rintro s ⟨u, rfl⟩; use f u; rfl

end PT

/-- The contravariant functor from the category of frames to the category of topological spaces,
which sends a frame `L` to the topological space `PT L` of homomorphisms from `L` to `Prop`
and a frame homomorphism `f` to the continuous function `PT.map f`. -/
def pt : Locale ⥤ TopCat where
  obj L := ⟨PT L.unop, by infer_instance⟩
  map f := PT.map f.unop

end pt_definition

section locale_top_adjunction
variable (X : Type*) [TopologicalSpace X] (L : FrmCat)

/-- The function that associates with a point `x` of the space `X` a point of the frame of opens
of `X`. -/
@[simps]
def frame_point_of_space_point (x : X) : PT (Opens X) where
  toFun := (x ∈ ·)
  map_inf' a b := rfl
  map_top' := rfl
  map_sSup' S := by simp

/-- The continuous function from a topological space `X` to the points of its frame of opens. -/
def neighborhoods : C(X, PT (Opens X)) where
  toFun := frame_point_of_space_point X
  continuous_toFun := continuous_def.2 $ by rintro _ ⟨u, rfl⟩; simpa using u.2

/-- The function underlying the counit. -/
def counit_fun (u : L) : Opens (PT L) where
  carrier := open_of_element_hom L u
  is_open' := by use u; rfl

/-- The counit is a frame homomorphism. -/
def counit_app_cont : FrameHom L (Opens $ PT L) where
  toFun := counit_fun L
  map_inf' a b := by simp [counit_fun]
  map_top' := by simp [counit_fun]; rfl
  map_sSup' S := by simp [counit_fun]; ext x; simp

/-- The component of the counit at an object of `Locale`. -/
def counit_app (Lop : Locale) : (pt.comp topToLocale).obj Lop ⟶ Lop where
  unop := counit_app_cont Lop.unop

/-- The counit as a natural transformation. -/
def counit : pt.comp topToLocale ⟶ 𝟭 Locale where
  app := counit_app

/-- The unit as a natural transformation. -/
def unit : 𝟭 TopCat ⟶ topToLocale.comp pt where
  app X := neighborhoods X

/-- The pair of unit and counit. -/
def unitCounit : Adjunction.CoreUnitCounit topToLocale pt where
  unit := unit
  counit := counit

/-- The forgetful functor `topToLocale` is left adjoint to the functor `pt`. -/
def adjunctionTopToLocalePT : topToLocale ⊣ pt := Adjunction.mkOfUnitCounit unitCounit

end locale_top_adjunction

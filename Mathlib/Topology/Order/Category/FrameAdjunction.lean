/-
Copyright (c) 2023 Anne Baanen, Sam v. Gool, Leo Mayer, Brendan S. Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Sam v. Gool, Leo Mayer, Brendan S. Murphy
-/
import Mathlib.Topology.Category.Locale

/-!
# Adjunction between Frames and Topological Spaces

This file defines contravariant functors between the categories of Frames and Topological Spaces
and proves that they form an adjunction.

## Main definitions and statement

- `pt`: the *points* functor from the opposite of the category of Frames (`FrmCat`) to the
  category of Topological Spaces (`TopCat`).

- `topToLocale`: the *open sets* functor from the category of Topological Spaces to the category of Frames.

- `frame_top_adjunction`: the theorem that topToLocale is left adjoint to pt.

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

-- TODO: should this be moved somewhere else?
@[simp] lemma elim_exists_prop (A : Prop → Prop) : (∃ p, A p ∧ p) ↔ A True := by aesop

open CategoryTheory Topology TopologicalSpace

/- ### Definition of the points functor `pt` --/

section pt_definition
variable (L : Type*) [Order.Frame L]

/-- The type of points of a frame `L`, where a *point* of a frame is, by definition, a frame
    homomorphism from `L` to the frame `Prop`. -/
@[reducible]
def pt_obj  := FrameHom L Prop

/-- The frame homomorphism from a frame `L` to the frame of sets of points of `L`. -/
def open_of_element_hom : FrameHom L (Set (pt_obj L)) where
  toFun u := {x | x u}
  map_inf' a b := by simp; rfl
  map_top' := by simp; rfl
  map_sSup' S := by
    dsimp
    -- simp only [map_sSup, sSup_Prop_eq, Set.mem_image, eq_iff_iff,
    --            Set.sSup_eq_sUnion, Set.sUnion_image]
    -- ext Z
    -- constructor
    -- . rintro ⟨p, ⟨x, hx, hp⟩, h⟩
    --   aesop_subst hp
    --   simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    --   exact ⟨x, hx, h⟩
    -- . rintro ⟨S', ⟨x, h⟩, hxZ⟩
    --   subst h
    --   use true
    --   simp only [iff_true, and_true]
    --   obtain ⟨S', h⟩ := hxZ
    --   simp only [Set.mem_range, exists_prop] at h
    --   obtain ⟨⟨hx, hS'⟩, hxZ⟩ := h
    --   subst hS'
    --   exact ⟨x, hx, hxZ⟩

/-- The topology on the set of points of the frame `L`. -/
instance ptTop : TopologicalSpace (pt_obj L) where
  IsOpen s := ∃ u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp [Prop.top_eq_true]⟩
  isOpen_inter := by
    rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩
    use u ⊓ v
    ext p
    simp only [ge_iff_le, map_inf, le_Prop_eq, inf_Prop_eq, Set.mem_setOf_eq, Set.mem_inter_iff]
  isOpen_sUnion := by
    intro U hU
    use (sSup { u | { x | x u } ∈ U })
    ext p
    simp only [map_sSup, sSup_Prop_eq, Set.mem_image, Set.mem_setOf_eq,
               eq_iff_iff, Set.mem_sUnion]
    constructor
    . rintro ⟨P, ⟨u, hu, hP⟩, h⟩
      aesop_subst hP
      exact ⟨{ x | x u }, hu, h⟩
    . rintro ⟨t, ht, hp⟩
      use true
      simp only [iff_true, and_true]
      obtain ⟨u, h⟩ := hU t ht
      subst h
      exact ⟨u, ht, hp⟩

/-- Characterizes when a subset of the space of points is open. -/
lemma open_in_pt_space_iff (U : Set (pt_obj L)) : IsOpen U ↔ ∃ u : L, U = {x | x u} := by
  unfold IsOpen TopologicalSpace.IsOpen ptTop Set.range setOf; tauto

/-- The action of the functor `pt` on frame homomorphisms. -/
@[reducible]
def pt_map {L L' : Type _} [Order.Frame L] [Order.Frame L'] (f : FrameHom L' L) :
  C(pt_obj L, pt_obj L') where
  toFun := fun p ↦ p.comp f
  continuous_toFun := ⟨by
    rintro s ⟨u, rfl⟩
    use f u
    ext p
    simp only [Set.mem_setOf_eq, Set.preimage_setOf_eq, FrameHom.comp_apply]⟩

/-- The contravariant functor from the category of frames to the category of topological spaces,
    which sends a frame `L` to the topological space `pt_obj L` of homomorphisms from `L` to `Prop`
    and a frame homomorphism `f` to the continuous function `pt_map f`. -/
def pt : Locale ⥤ TopCat where
  obj L := ⟨pt_obj L.unop, by infer_instance⟩
  map f := pt_map f.unop

end pt_definition

section frame_top_adjunction

variable (X : Type*) [TopologicalSpace X] (L : FrmCat)

/-- The function that associates with a point `x` of the space `X` a point of the frame of
    opens of `X` -/
def frame_point_of_space_point (x : X) : FrameHom (Opens X) Prop where
  toFun u := x ∈ u
  map_inf' a b := by simp; rfl
  map_top' := by simp; rfl
  map_sSup' S := by simp

/-- The continuous function from a topological space `X` to `pt topToLocale X`.-/
def neighborhoods : C(X, pt_obj (Opens X)) where
  toFun := frame_point_of_space_point X
  continuous_toFun := by
    rw [continuous_def]; intro U; rw[open_in_pt_space_iff]
    intro h
    cases' h with u hu
    rw [hu]
    have key : frame_point_of_space_point X ⁻¹' { x | x u } = u := by
      ext x
      simp
      aesop_subst hu
      tauto
    rw [key]
    exact u.2

/-- The function underlying the counit. -/
def counit_fun (u : L) : Opens (pt_obj L) where
  carrier := open_of_element_hom L u
  is_open' := by use u; rfl

/-- The counit is a frame homomorphism. -/
def counit_app_cont : FrameHom L (Opens (FrameHom L Prop)) where
  toFun := counit_fun L
  map_inf' a b := by simp [counit_fun]
  map_top' := by simp [counit_fun]; rfl
  map_sSup' S := by simp [counit_fun]; ext x; simp

/-- The component of the counit at an object of Locale. -/
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

/-- The forgetful functor `topToLocale` is left adjoint to the contravariant functor `pt`. -/
def adjunctionTopToLocalePT : topToLocale ⊣ pt := Adjunction.mkOfUnitCounit unitCounit

end frame_top_adjunction

/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.stalks
! leanprover-community/mathlib commit d39590fc8728fbf6743249802486f8c91ffe07bc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.Topology.Sheaves.Stalks

/-!
# Stalks for presheaved spaces

This file lifts constructions of stalks and pushforwards of stalks to work with
the category of presheafed spaces. Additionally, we prove that restriction of
presheafed spaces does not change the stalks.
-/


noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Functor

open AlgebraicGeometry

open TopologicalSpace

open Opposite

variable {C : Type u} [Category.{v} C] [HasColimits C]

attribute [local tidy] tactic.op_induction' tactic.auto_cases_opens

open TopCat.Presheaf

namespace AlgebraicGeometry.PresheafedSpace

/-- The stalk at `x` of a `PresheafedSpace`.
-/
abbrev stalk (X : PresheafedSpace C) (x : X) : C :=
  X.Presheaf.stalk x
#align algebraic_geometry.PresheafedSpace.stalk AlgebraicGeometry.PresheafedSpace.stalk

/-- A morphism of presheafed spaces induces a morphism of stalks.
-/
def stalkMap {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) (x : X) : Y.stalk (α.base x) ⟶ X.stalk x :=
  (stalkFunctor C (α.base x)).map α.c ≫ X.Presheaf.stalkPushforward C α.base x
#align algebraic_geometry.PresheafedSpace.stalk_map AlgebraicGeometry.PresheafedSpace.stalkMap

@[simp, elementwise, reassoc]
theorem stalkMap_germ {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) (U : Opens Y.carrier)
    (x : (Opens.map α.base).obj U) :
    Y.Presheaf.germ ⟨α.base x, x.2⟩ ≫ stalkMap α ↑x = α.c.app (op U) ≫ X.Presheaf.germ x := by
  rw [stalk_map, stalk_functor_map_germ_assoc, stalk_pushforward_germ]
#align algebraic_geometry.PresheafedSpace.stalk_map_germ AlgebraicGeometry.PresheafedSpace.stalkMap_germ

section Restrict

/-- For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at t `x`.
-/
def restrictStalkIso {U : TopCat} (X : PresheafedSpace.{v} C) {f : U ⟶ (X : TopCat.{v})}
    (h : OpenEmbedding f) (x : U) : (X.restrict h).stalk x ≅ X.stalk (f x) :=
  haveI-- As a left adjoint, the functor `h.is_open_map.functor_nhds x` is initial.
   := initial_of_adjunction (h.is_open_map.adjunction_nhds x)
  -- Typeclass resolution knows that the opposite of an initial functor is final. The result
    -- follows from the general fact that postcomposing with a final functor doesn't change colimits.
    final.colimit_iso
    (h.is_open_map.functor_nhds x).op ((open_nhds.inclusion (f x)).op ⋙ X.presheaf)
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso AlgebraicGeometry.PresheafedSpace.restrictStalkIso

@[simp, elementwise, reassoc]
theorem restrictStalkIso_hom_eq_germ {U : TopCat} (X : PresheafedSpace.{v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (V : Opens U) (x : U) (hx : x ∈ V) :
    (X.restrict h).Presheaf.germ ⟨x, hx⟩ ≫ (restrictStalkIso X h x).Hom =
      X.Presheaf.germ ⟨f x, show f x ∈ h.IsOpenMap.Functor.obj V from ⟨x, hx, rfl⟩⟩ :=
  colimit.ι_pre ((OpenNhds.inclusion (f x)).op ⋙ X.Presheaf) (h.IsOpenMap.functorNhds x).op
    (op ⟨V, hx⟩)
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso_hom_eq_germ AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ

@[simp, elementwise, reassoc]
theorem restrictStalkIso_inv_eq_germ {U : TopCat} (X : PresheafedSpace.{v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (V : Opens U) (x : U) (hx : x ∈ V) :
    X.Presheaf.germ ⟨f x, show f x ∈ h.IsOpenMap.Functor.obj V from ⟨x, hx, rfl⟩⟩ ≫
        (restrictStalkIso X h x).inv =
      (X.restrict h).Presheaf.germ ⟨x, hx⟩ :=
  by rw [← restrict_stalk_iso_hom_eq_germ, category.assoc, iso.hom_inv_id, category.comp_id]
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_germ AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ

theorem restrictStalkIso_inv_eq_ofRestrict {U : TopCat} (X : PresheafedSpace.{v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (x : U) :
    (X.restrictStalkIso h x).inv = stalkMap (X.of_restrict h) x :=
  by
  ext V
  induction V using Opposite.rec'
  let i : (h.is_open_map.functor_nhds x).obj ((open_nhds.map f x).obj V) ⟶ V :=
    hom_of_le (Set.image_preimage_subset f _)
  erw [iso.comp_inv_eq, colimit.ι_map_assoc, colimit.ι_map_assoc, colimit.ι_pre]
  simp_rw [category.assoc]
  erw [colimit.ι_pre ((open_nhds.inclusion (f x)).op ⋙ X.presheaf)
      (h.is_open_map.functor_nhds x).op]
  erw [← X.presheaf.map_comp_assoc]
  exact (colimit.w ((open_nhds.inclusion (f x)).op ⋙ X.presheaf) i.op).symm
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_of_restrict AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict

instance ofRestrict_stalkMap_isIso {U : TopCat} (X : PresheafedSpace.{v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (x : U) :
    IsIso (stalkMap (X.of_restrict h) x) := by rw [← restrict_stalk_iso_inv_eq_of_restrict];
  infer_instance
#align algebraic_geometry.PresheafedSpace.of_restrict_stalk_map_is_iso AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso

end Restrict

namespace StalkMap

@[simp]
theorem id (X : PresheafedSpace.{v} C) (x : X) : stalkMap (𝟙 X) x = 𝟙 (X.stalk x) :=
  by
  dsimp [stalk_map]
  simp only [stalk_pushforward.id]
  rw [← map_comp]
  convert(stalk_functor C x).map_id X.presheaf
  tidy
#align algebraic_geometry.PresheafedSpace.stalk_map.id AlgebraicGeometry.PresheafedSpace.stalkMap.id

-- TODO understand why this proof is still gross (i.e. requires using `erw`)
@[simp]
theorem comp {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
    stalkMap (α ≫ β) x =
      (stalkMap β (α.base x) : Z.stalk (β.base (α.base x)) ⟶ Y.stalk (α.base x)) ≫
        (stalkMap α x : Y.stalk (α.base x) ⟶ X.stalk x) :=
  by
  dsimp [stalk_map, stalk_functor, stalk_pushforward]
  ext U
  induction U using Opposite.rec'
  cases U
  simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc, colimit.ι_pre, whisker_left_app,
    whisker_right_app, assoc, id_comp, map_id, map_comp]
  dsimp
  simp only [map_id, assoc, pushforward.comp_inv_app]
  -- FIXME Why doesn't simp do this:
  erw [CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id]
  erw [id_comp, id_comp]
#align algebraic_geometry.PresheafedSpace.stalk_map.comp AlgebraicGeometry.PresheafedSpace.stalkMap.comp

/-- If `α = β` and `x = x'`, we would like to say that `stalk_map α x = stalk_map β x'`.
Unfortunately, this equality is not well-formed, as their types are not _definitionally_ the same.
To get a proper congruence lemma, we therefore have to introduce these `eq_to_hom` arrows on
either side of the equality.
-/
theorem congr {X Y : PresheafedSpace.{v} C} (α β : X ⟶ Y) (h₁ : α = β) (x x' : X) (h₂ : x = x') :
    stalkMap α x ≫ eqToHom (show X.stalk x = X.stalk x' by rw [h₂]) =
      eqToHom (show Y.stalk (α.base x) = Y.stalk (β.base x') by rw [h₁, h₂]) ≫ stalkMap β x' :=
  stalk_hom_ext _ fun U hx => by subst h₁; subst h₂; simp
#align algebraic_geometry.PresheafedSpace.stalk_map.congr AlgebraicGeometry.PresheafedSpace.stalkMap.congr

theorem congr_hom {X Y : PresheafedSpace.{v} C} (α β : X ⟶ Y) (h : α = β) (x : X) :
    stalkMap α x =
      eqToHom (show Y.stalk (α.base x) = Y.stalk (β.base x) by rw [h]) ≫ stalkMap β x :=
  by rw [← stalk_map.congr α β h x x rfl, eq_to_hom_refl, category.comp_id]
#align algebraic_geometry.PresheafedSpace.stalk_map.congr_hom AlgebraicGeometry.PresheafedSpace.stalkMap.congr_hom

theorem congr_point {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) (x x' : X) (h : x = x') :
    stalkMap α x ≫ eqToHom (show X.stalk x = X.stalk x' by rw [h]) =
      eqToHom (show Y.stalk (α.base x) = Y.stalk (α.base x') by rw [h]) ≫ stalkMap α x' :=
  by rw [stalk_map.congr α α rfl x x' h]
#align algebraic_geometry.PresheafedSpace.stalk_map.congr_point AlgebraicGeometry.PresheafedSpace.stalkMap.congr_point

instance isIso {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) [IsIso α] (x : X) : IsIso (stalkMap α x)
    where out := by
    let β : Y ⟶ X := CategoryTheory.inv α
    have h_eq : (α ≫ β).base x = x := by rw [is_iso.hom_inv_id α, id_base, TopCat.id_app]
    -- Intuitively, the inverse of the stalk map of `α` at `x` should just be the stalk map of `β`
    -- at `α x`. Unfortunately, we have a problem with dependent type theory here: Because `x`
    -- is not *definitionally* equal to `β (α x)`, the map `stalk_map β (α x)` has not the correct
    -- type for an inverse.
    -- To get a proper inverse, we need to compose with the `eq_to_hom` arrow
    -- `X.stalk x ⟶ X.stalk ((α ≫ β).base x)`.
    refine'
      ⟨eq_to_hom (show X.stalk x = X.stalk ((α ≫ β).base x) by rw [h_eq]) ≫
          (stalk_map β (α.base x) : _),
        _, _⟩
    · rw [← category.assoc, congr_point α x ((α ≫ β).base x) h_eq.symm, category.assoc]
      erw [← stalk_map.comp β α (α.base x)]
      rw [congr_hom _ _ (is_iso.inv_hom_id α), stalk_map.id, eq_to_hom_trans_assoc, eq_to_hom_refl,
        category.id_comp]
    ·
      rw [category.assoc, ← stalk_map.comp, congr_hom _ _ (is_iso.hom_inv_id α), stalk_map.id,
        eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp]
#align algebraic_geometry.PresheafedSpace.stalk_map.is_iso AlgebraicGeometry.PresheafedSpace.stalkMap.isIso

/-- An isomorphism between presheafed spaces induces an isomorphism of stalks.
-/
def stalkIso {X Y : PresheafedSpace.{v} C} (α : X ≅ Y) (x : X) :
    Y.stalk (α.Hom.base x) ≅ X.stalk x :=
  asIso (stalkMap α.Hom x)
#align algebraic_geometry.PresheafedSpace.stalk_map.stalk_iso AlgebraicGeometry.PresheafedSpace.stalkMap.stalkIso

@[simp, reassoc, elementwise]
theorem stalkSpecializes_stalkMap {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) {x y : X} (h : x ⤳ y) :
    Y.Presheaf.stalkSpecializes (f.base.map_specializes h) ≫ stalkMap f x =
      stalkMap f y ≫ X.Presheaf.stalkSpecializes h :=
  by delta PresheafedSpace.stalk_map; simp [stalk_map]
#align algebraic_geometry.PresheafedSpace.stalk_map.stalk_specializes_stalk_map AlgebraicGeometry.PresheafedSpace.stalkMap.stalkSpecializes_stalkMap

end StalkMap

end AlgebraicGeometry.PresheafedSpace


/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.stalks
! leanprover-community/mathlib commit d39590fc8728fbf6743249802486f8c91ffe07bc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicGeometry.PresheafedSpace
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks for presheaved spaces

This file lifts constructions of stalks and pushforwards of stalks to work with
the category of presheafed spaces. Additionally, we prove that restriction of
presheafed spaces does not change the stalks.
-/


noncomputable section

universe v u v' u'

open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry TopologicalSpace

variable {C : Type u} [Category.{v} C] [HasColimits C]

-- Porting note : no tidy tactic
-- attribute [local tidy] tactic.op_induction' tactic.auto_cases_opens
-- this could be replaced by
-- attribute [local aesop safe cases (rule_sets [CategoryTheory])] Opens
-- but it doesn't appear to be needed here.

open TopCat.Presheaf

namespace AlgebraicGeometry.PresheafedSpace

/-- The stalk at `x` of a `PresheafedSpace`.
-/
abbrev stalk (X : PresheafedSpace C) (x : X) : C :=
  X.presheaf.stalk x
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk AlgebraicGeometry.PresheafedSpace.stalk

/-- A morphism of presheafed spaces induces a morphism of stalks.
-/
def stalkMap {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (x : X) :
    Y.stalk (α.base x) ⟶ X.stalk x :=
  (stalkFunctor C (α.base x)).map α.c ≫ X.presheaf.stalkPushforward C α.base x
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map AlgebraicGeometry.PresheafedSpace.stalkMap

@[elementwise (attr := simp), reassoc (attr := simp)]
theorem stalkMap_germ {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (U : Opens Y)
    (x : (Opens.map α.base).obj U) :
    Y.presheaf.germ ⟨α.base x.1, x.2⟩ ≫ stalkMap α ↑x = α.c.app (op U) ≫ X.presheaf.germ x := by
  rw [stalkMap, stalkFunctor_map_germ_assoc, stalkPushforward_germ]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map_germ AlgebraicGeometry.PresheafedSpace.stalkMap_germ

section Restrict

/-- For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at t `x`.
-/
def restrictStalkIso {U : TopCat} (X : PresheafedSpace.{_, _, v} C) {f : U ⟶ (X : TopCat.{v})}
    (h : OpenEmbedding f) (x : U) : (X.restrict h).stalk x ≅ X.stalk (f x) :=
  haveI := initial_of_adjunction (h.isOpenMap.adjunctionNhds x)
  Final.colimitIso (h.isOpenMap.functorNhds x).op ((OpenNhds.inclusion (f x)).op ⋙ X.presheaf)
  -- As a left adjoint, the functor `h.is_open_map.functor_nhds x` is initial.
  -- Typeclass resolution knows that the opposite of an initial functor is final. The result
  -- follows from the general fact that postcomposing with a final functor doesn't change colimits.
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso AlgebraicGeometry.PresheafedSpace.restrictStalkIso

-- Porting note : removed `simp` attribute, for left hand side is not in simple normal form.
@[elementwise, reassoc]
theorem restrictStalkIso_hom_eq_germ {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (V : Opens U) (x : U) (hx : x ∈ V) :
    (X.restrict h).presheaf.germ ⟨x, hx⟩ ≫ (restrictStalkIso X h x).hom =
    X.presheaf.germ ⟨f x, show f x ∈ h.isOpenMap.functor.obj V from ⟨x, hx, rfl⟩⟩ :=
  colimit.ι_pre ((OpenNhds.inclusion (f x)).op ⋙ X.presheaf) (h.isOpenMap.functorNhds x).op
    (op ⟨V, hx⟩)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso_hom_eq_germ AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ

@[elementwise (attr := simp), reassoc (attr := simp)]
theorem restrictStalkIso_inv_eq_germ {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (V : Opens U) (x : U) (hx : x ∈ V) :
    X.presheaf.germ ⟨f x, show f x ∈ h.isOpenMap.functor.obj V from ⟨x, hx, rfl⟩⟩ ≫
        (restrictStalkIso X h x).inv =
      (X.restrict h).presheaf.germ ⟨x, hx⟩ :=
  by rw [← restrictStalkIso_hom_eq_germ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_germ AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ

theorem restrictStalkIso_inv_eq_ofRestrict {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (x : U) :
    (X.restrictStalkIso h x).inv = stalkMap (X.ofRestrict h) x := by
  refine colimit.hom_ext fun V => ?_
  induction V with | h V => ?_
  let i : (h.isOpenMap.functorNhds x).obj ((OpenNhds.map f x).obj V) ⟶ V :=
    homOfLE (Set.image_preimage_subset f _)
  erw [Iso.comp_inv_eq, colimit.ι_map_assoc, colimit.ι_map_assoc, colimit.ι_pre]
  simp_rw [Category.assoc]
  erw [colimit.ι_pre ((OpenNhds.inclusion (f x)).op ⋙ X.presheaf)
      (h.isOpenMap.functorNhds x).op]
  erw [← X.presheaf.map_comp_assoc]
  exact (colimit.w ((OpenNhds.inclusion (f x)).op ⋙ X.presheaf) i.op).symm
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_of_restrict AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict

instance ofRestrict_stalkMap_isIso {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (x : U) :
    IsIso (stalkMap (X.ofRestrict h) x) := by
  rw [← restrictStalkIso_inv_eq_ofRestrict]; infer_instance
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.of_restrict_stalk_map_is_iso AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso

end Restrict

namespace stalkMap

@[simp]
theorem id (X : PresheafedSpace.{_, _, v} C) (x : X) :
    stalkMap (𝟙 X) x = 𝟙 (X.stalk x) := by
  dsimp [stalkMap]
  simp only [stalkPushforward.id]
  erw [← map_comp]
  convert (stalkFunctor C x).map_id X.presheaf
  refine NatTrans.ext _ _ <| funext fun x => ?_
  simp only [id_c, id_comp, Pushforward.id_hom_app, op_obj, eqToHom_refl, map_id]
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.id AlgebraicGeometry.PresheafedSpace.stalkMap.id

@[simp]
theorem comp {X Y Z : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
    stalkMap (α ≫ β) x =
      (stalkMap β (α.base x) : Z.stalk (β.base (α.base x)) ⟶ Y.stalk (α.base x)) ≫
        (stalkMap α x : Y.stalk (α.base x) ⟶ X.stalk x) := by
  dsimp [stalkMap, stalkFunctor, stalkPushforward]
  refine colimit.hom_ext fun U => ?_
  induction U with | h U => ?_
  cases U
  simp only [whiskeringLeft_obj_obj, comp_obj, op_obj, unop_op, OpenNhds.inclusion_obj,
    ι_colimMap_assoc, pushforwardObj_obj, Opens.map_comp_obj, whiskerLeft_app, comp_c_app,
    OpenNhds.map_obj, whiskerRight_app, NatTrans.id_app, map_id, colimit.ι_pre, id_comp, assoc,
    colimit.ι_pre_assoc]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.comp AlgebraicGeometry.PresheafedSpace.stalkMap.comp

/-- If `α = β` and `x = x'`, we would like to say that `stalk_map α x = stalk_map β x'`.
Unfortunately, this equality is not well-formed, as their types are not _definitionally_ the same.
To get a proper congruence lemma, we therefore have to introduce these `eq_to_hom` arrows on
either side of the equality.
-/
theorem congr {X Y : PresheafedSpace.{_, _, v} C} (α β : X ⟶ Y)
    (h₁ : α = β) (x x' : X) (h₂ : x = x') :
    stalkMap α x ≫ eqToHom (show X.stalk x = X.stalk x' by rw [h₂]) =
      eqToHom (show Y.stalk (α.base x) = Y.stalk (β.base x') by rw [h₁, h₂]) ≫ stalkMap β x' :=
  stalk_hom_ext _ fun U hx => by subst h₁; subst h₂; simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.congr AlgebraicGeometry.PresheafedSpace.stalkMap.congr

theorem congr_hom {X Y : PresheafedSpace.{_, _, v} C} (α β : X ⟶ Y) (h : α = β) (x : X) :
    stalkMap α x =
      eqToHom (show Y.stalk (α.base x) = Y.stalk (β.base x) by rw [h]) ≫ stalkMap β x :=
  by rw [← stalkMap.congr α β h x x rfl, eqToHom_refl, Category.comp_id]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.congr_hom AlgebraicGeometry.PresheafedSpace.stalkMap.congr_hom

theorem congr_point {X Y : PresheafedSpace.{_, _, v} C}
    (α : X ⟶ Y) (x x' : X) (h : x = x') :
    stalkMap α x ≫ eqToHom (show X.stalk x = X.stalk x' by rw [h]) =
      eqToHom (show Y.stalk (α.base x) = Y.stalk (α.base x') by rw [h]) ≫ stalkMap α x' :=
  by rw [stalkMap.congr α α rfl x x' h]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.congr_point AlgebraicGeometry.PresheafedSpace.stalkMap.congr_point

instance isIso {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) [IsIso α] (x : X) :
    IsIso (stalkMap α x) where
  out := by
    let β : Y ⟶ X := CategoryTheory.inv α
    have h_eq : (α ≫ β).base x = x := by rw [IsIso.hom_inv_id α, id_base, TopCat.id_app]
    -- Intuitively, the inverse of the stalk map of `α` at `x` should just be the stalk map of `β`
    -- at `α x`. Unfortunately, we have a problem with dependent type theory here: Because `x`
    -- is not *definitionally* equal to `β (α x)`, the map `stalk_map β (α x)` has not the correct
    -- type for an inverse.
    -- To get a proper inverse, we need to compose with the `eq_to_hom` arrow
    -- `X.stalk x ⟶ X.stalk ((α ≫ β).base x)`.
    refine'
      ⟨eqToHom (show X.stalk x = X.stalk ((α ≫ β).base x) by rw [h_eq]) ≫
          (stalkMap β (α.base x) : _),
        _, _⟩
    · rw [← Category.assoc, congr_point α x ((α ≫ β).base x) h_eq.symm, Category.assoc]
      erw [← stalkMap.comp β α (α.base x)]
      rw [congr_hom _ _ (IsIso.inv_hom_id α), stalkMap.id, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
    · rw [Category.assoc, ← stalkMap.comp, congr_hom _ _ (IsIso.hom_inv_id α), stalkMap.id,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.is_iso AlgebraicGeometry.PresheafedSpace.stalkMap.isIso

/-- An isomorphism between presheafed spaces induces an isomorphism of stalks.
-/
def stalkIso {X Y : PresheafedSpace.{_, _, v} C} (α : X ≅ Y) (x : X) :
    Y.stalk (α.hom.base x) ≅ X.stalk x :=
  asIso (stalkMap α.hom x)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.stalk_iso AlgebraicGeometry.PresheafedSpace.stalkMap.stalkIso

@[simp, reassoc, elementwise]
theorem stalkSpecializes_stalkMap {X Y : PresheafedSpace.{_, _, v} C}
    (f : X ⟶ Y) {x y : X} (h : x ⤳ y) :
    Y.presheaf.stalkSpecializes (f.base.map_specializes h) ≫ stalkMap f x =
      stalkMap f y ≫ X.presheaf.stalkSpecializes h := by
  -- Porting note : the original one liner `dsimp [stalkMap]; simp [stalkMap]` doesn't work,
  -- I had to uglify this
  dsimp [stalkSpecializes, stalkMap, stalkFunctor, stalkPushforward]
  refine colimit.hom_ext fun j => ?_
  induction j with | h j => ?_
  dsimp
  simp only [colimit.ι_desc_assoc, comp_obj, op_obj, unop_op, ι_colimMap_assoc, colimit.map_desc,
    OpenNhds.inclusion_obj, pushforwardObj_obj, whiskerLeft_app, OpenNhds.map_obj, whiskerRight_app,
    NatTrans.id_app, map_id, colimit.ι_pre, id_comp, assoc, colimit.pre_desc]
  erw [colimit.ι_desc]
  dsimp
  erw [X.presheaf.map_id, id_comp]
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.stalk_map.stalk_specializes_stalk_map AlgebraicGeometry.PresheafedSpace.stalkMap.stalkSpecializes_stalkMap

end stalkMap

end AlgebraicGeometry.PresheafedSpace

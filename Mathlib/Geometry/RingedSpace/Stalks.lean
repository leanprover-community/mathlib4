/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Geometry.RingedSpace.PresheafedSpace
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

-- Porting note: no tidy tactic
-- attribute [local tidy] tactic.auto_cases_opens
-- this could be replaced by
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- but it doesn't appear to be needed here.

open TopCat.Presheaf

namespace AlgebraicGeometry.PresheafedSpace

/-- A morphism of presheafed spaces induces a morphism of stalks.
-/
def Hom.stalkMap {X Y : PresheafedSpace.{_, _, v} C} (α : Hom X Y) (x : X) :
    Y.presheaf.stalk (α.base x) ⟶ X.presheaf.stalk x :=
  (stalkFunctor C (α.base x)).map α.c ≫ X.presheaf.stalkPushforward C α.base x

@[elementwise, reassoc]
theorem stalkMap_germ {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (U : Opens Y)
    (x : X) (hx : α x ∈ U) :
    Y.presheaf.germ U (α x) hx ≫ α.stalkMap x = α.c.app (op U) ≫
      X.presheaf.germ ((Opens.map α.base).obj U) x hx := by
  rw [Hom.stalkMap, stalkFunctor_map_germ_assoc, stalkPushforward_germ]

@[deprecated (since := "2024-07-30")] alias stalkMap_germ' := stalkMap_germ
@[deprecated (since := "2024-07-30")] alias stalkMap_germ'_assoc := stalkMap_germ

section Restrict

/-- For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at t `x`.
-/
def restrictStalkIso {U : TopCat} (X : PresheafedSpace.{_, _, v} C) {f : U ⟶ (X : TopCat.{v})}
    (h : OpenEmbedding f) (x : U) : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x) :=
  haveI := initial_of_adjunction (h.isOpenMap.adjunctionNhds x)
  Final.colimitIso (h.isOpenMap.functorNhds x).op ((OpenNhds.inclusion (f x)).op ⋙ X.presheaf)
  -- As a left adjoint, the functor `h.is_open_map.functor_nhds x` is initial.
  -- Typeclass resolution knows that the opposite of an initial functor is final. The result
  -- follows from the general fact that postcomposing with a final functor doesn't change colimits.

-- Porting note (#11119): removed `simp` attribute, for left hand side is not in simple normal form.
@[elementwise, reassoc]
theorem restrictStalkIso_hom_eq_germ {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (V : Opens U) (x : U) (hx : x ∈ V) :
    (X.restrict h).presheaf.germ _ x hx ≫ (restrictStalkIso X h x).hom =
    X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ :=
  colimit.ι_pre ((OpenNhds.inclusion (f x)).op ⋙ X.presheaf) (h.isOpenMap.functorNhds x).op
    (op ⟨V, hx⟩)

-- We intentionally leave `simp` off the lemmas generated by `elementwise` and `reassoc`,
-- as the simpNF linter claims they never apply.
@[simp, elementwise, reassoc]
theorem restrictStalkIso_inv_eq_germ {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (V : Opens U) (x : U) (hx : x ∈ V) :
    X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ ≫
        (restrictStalkIso X h x).inv =
      (X.restrict h).presheaf.germ _ x hx := by
  rw [← restrictStalkIso_hom_eq_germ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem restrictStalkIso_inv_eq_ofRestrict {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (x : U) :
    (X.restrictStalkIso h x).inv = (X.ofRestrict h).stalkMap x := by
  -- We can't use `ext` here due to https://github.com/leanprover/std4/pull/159
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

instance ofRestrict_stalkMap_isIso {U : TopCat} (X : PresheafedSpace.{_, _, v} C)
    {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) (x : U) :
    IsIso ((X.ofRestrict h).stalkMap x) := by
  rw [← restrictStalkIso_inv_eq_ofRestrict]; infer_instance

end Restrict

namespace stalkMap

@[simp]
theorem id (X : PresheafedSpace.{_, _, v} C) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) := by
  dsimp [Hom.stalkMap]
  simp only [stalkPushforward.id]
  rw [← map_comp]
  convert (stalkFunctor C x).map_id X.presheaf
  ext
  simp only [id_c, id_comp, Pushforward.id_hom_app, op_obj, eqToHom_refl, map_id]
  rfl

@[simp]
theorem comp {X Y Z : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
    (α ≫ β).stalkMap x =
      (β.stalkMap (α.base x) : Z.presheaf.stalk (β.base (α.base x)) ⟶ Y.presheaf.stalk (α.base x)) ≫
        (α.stalkMap x : Y.presheaf.stalk (α.base x) ⟶ X.presheaf.stalk x) := by
  dsimp [Hom.stalkMap, stalkFunctor, stalkPushforward]
  -- We can't use `ext` here due to https://github.com/leanprover/std4/pull/159
  apply colimit.hom_ext
  rintro ⟨U, hU⟩
  simp

/-- If `α = β` and `x = x'`, we would like to say that `stalk_map α x = stalk_map β x'`.
Unfortunately, this equality is not well-formed, as their types are not _definitionally_ the same.
To get a proper congruence lemma, we therefore have to introduce these `eqToHom` arrows on
either side of the equality.
-/
theorem congr {X Y : PresheafedSpace.{_, _, v} C} (α β : X ⟶ Y)
    (h₁ : α = β) (x x' : X) (h₂ : x = x') :
    α.stalkMap x ≫ eqToHom (show X.presheaf.stalk x = X.presheaf.stalk x' by rw [h₂]) =
      eqToHom (show Y.presheaf.stalk (α.base x) = Y.presheaf.stalk (β.base x') by rw [h₁, h₂]) ≫
        β.stalkMap x' := by
  ext
  substs h₁ h₂
  simp

theorem congr_hom {X Y : PresheafedSpace.{_, _, v} C} (α β : X ⟶ Y) (h : α = β) (x : X) :
    α.stalkMap x =
      eqToHom (show Y.presheaf.stalk (α.base x) =
        Y.presheaf.stalk (β.base x) by rw [h]) ≫ β.stalkMap x := by
  rw [← stalkMap.congr α β h x x rfl, eqToHom_refl, Category.comp_id]

theorem congr_point {X Y : PresheafedSpace.{_, _, v} C}
    (α : X ⟶ Y) (x x' : X) (h : x = x') :
    α.stalkMap x ≫ eqToHom (show X.presheaf.stalk x = X.presheaf.stalk x' by rw [h]) =
      eqToHom (show Y.presheaf.stalk (α.base x) =
        Y.presheaf.stalk (α.base x') by rw [h]) ≫ α.stalkMap x' := by
  rw [stalkMap.congr α α rfl x x' h]

instance isIso {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) [IsIso α] (x : X) :
    IsIso (α.stalkMap x) where
  out := by
    let β : Y ⟶ X := CategoryTheory.inv α
    have h_eq : (α ≫ β).base x = x := by rw [IsIso.hom_inv_id α, id_base, TopCat.id_app]
    -- Intuitively, the inverse of the stalk map of `α` at `x` should just be the stalk map of `β`
    -- at `α x`. Unfortunately, we have a problem with dependent type theory here: Because `x`
    -- is not *definitionally* equal to `β (α x)`, the map `stalk_map β (α x)` has not the correct
    -- type for an inverse.
    -- To get a proper inverse, we need to compose with the `eqToHom` arrow
    -- `X.stalk x ⟶ X.stalk ((α ≫ β).base x)`.
    refine
      ⟨eqToHom (show X.presheaf.stalk x = X.presheaf.stalk ((α ≫ β).base x) by rw [h_eq]) ≫
          (β.stalkMap (α.base x) : _),
        ?_, ?_⟩
    · rw [← Category.assoc, congr_point α x ((α ≫ β).base x) h_eq.symm, Category.assoc]
      erw [← stalkMap.comp β α (α.base x)]
      rw [congr_hom _ _ (IsIso.inv_hom_id α), stalkMap.id, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
    · rw [Category.assoc, ← stalkMap.comp, congr_hom _ _ (IsIso.hom_inv_id α), stalkMap.id,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- An isomorphism between presheafed spaces induces an isomorphism of stalks.
-/
def stalkIso {X Y : PresheafedSpace.{_, _, v} C} (α : X ≅ Y) (x : X) :
    Y.presheaf.stalk (α.hom.base x) ≅ X.presheaf.stalk x :=
  asIso (α.hom.stalkMap x)

@[reassoc, elementwise, simp, nolint simpNF] -- see std4#365 for the simpNF issue
theorem stalkSpecializes_stalkMap {X Y : PresheafedSpace.{_, _, v} C}
    (f : X ⟶ Y) {x y : X} (h : x ⤳ y) :
    Y.presheaf.stalkSpecializes (f.base.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap y ≫ X.presheaf.stalkSpecializes h := by
  -- Porting note: the original one liner `dsimp [stalkMap]; simp [stalkMap]` doesn't work,
  -- I had to uglify this
  dsimp [stalkSpecializes, Hom.stalkMap, stalkFunctor, stalkPushforward]
  -- We can't use `ext` here due to https://github.com/leanprover/std4/pull/159
  refine colimit.hom_ext fun j => ?_
  induction j with | h j => ?_
  dsimp
  simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, whiskerLeft_app,
    whiskerRight_app, NatTrans.id_app, map_id, colimit.ι_pre, id_comp, assoc,
    colimit.pre_desc, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_ι,
    Cocone.whisker_ι, NatTrans.comp_app]
  erw [X.presheaf.map_id, id_comp]
  rfl

end stalkMap

end AlgebraicGeometry.PresheafedSpace

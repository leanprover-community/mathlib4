/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the composition of the inclusion of categories
`(OpenNhds x)ᵒᵖ ⥤ (Opens X)ᵒᵖ` and the functor `F : (Opens X)ᵒᵖ ⥤ C`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalkFunctor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalkPushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `MonCat`,
`CommRingCat`,...) is that they preserve filtered colimits. Since stalks are filtered colimits,
this ensures that the stalks of presheaves valued in these categories behave exactly as for
`Type`-valued presheaves. For example, in `germ_exist` we prove that in such a category, every
element of the stalk is the germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

-/


noncomputable section

universe v u v' u'

open CategoryTheory

open TopCat

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

variable {C : Type u} [Category.{v} C]
variable [HasColimits.{v} C]
variable {X Y Z : TopCat.{v}}

namespace TopCat.Presheaf

variable (C)

/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalkFunctor (x : X) : X.Presheaf C ⥤ C :=
  (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

variable {C}

/-- The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ

-- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)
@[simp]
theorem stalkFunctor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ.stalk x :=
  rfl

/-- The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.Presheaf C) {U : Opens X} (x : U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((OpenNhds.inclusion x.1).op ⋙ F) (op ⟨U, x.2⟩)

/-- The germ of a global section of a presheaf at a point. -/
def Γgerm (F : X.Presheaf C) (x : X) : F.obj (op ⊤) ⟶ stalk F x :=
  F.germ ⟨x, show x ∈ ⊤ by trivial⟩

@[reassoc (attr := simp)]
theorem germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : U) :
    F.map i.op ≫ germ F x = germ F (i x : V) :=
  let i' : (⟨U, x.2⟩ : OpenNhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i
  colimit.w ((OpenNhds.inclusion x.1).op ⋙ F) i'.op

@[reassoc]
lemma map_germ_eq_Γgerm (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : U) :
    F.map i.op ≫ germ F x = Γgerm F (i x) :=
  germ_res F i x

-- Porting note: `@[elementwise]` did not generate the best lemma when applied to `germ_res`
attribute [local instance] ConcreteCategory.instFunLike in
theorem germ_res_apply (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : U) [ConcreteCategory C]
    (s) : germ F x (F.map i.op s) = germ F (i x) s := by rw [← comp_apply, germ_res]

attribute [local instance] ConcreteCategory.instFunLike in
lemma Γgerm_res_apply (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : U) [ConcreteCategory C]
    (s) : germ F x (F.map i.op s) = Γgerm F x.val s := germ_res_apply F i x s

/-- A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
@[ext]
theorem stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
    (ih : ∀ (U : Opens X) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext fun U => by
    induction' U using Opposite.rec with U; cases' U with U hxU; exact ih U hxU

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkFunctor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : U) (f : F ⟶ G) :
    germ F x ≫ (stalkFunctor C x.1).map f = f.app (op U) ≫ germ G x :=
  colimit.ι_map (whiskerLeft (OpenNhds.inclusion x.1).op f) (op ⟨U, x.2⟩)

variable (C)

/-- For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphisms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
def stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x := by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  -- Porting note: The original proof was `trans; swap`, but `trans` does nothing.
  refine ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkPushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
    (x : (Opens.map f).obj U) :
      (f _* F).germ ⟨(f : X → Y) (x : X), x.2⟩ ≫ F.stalkPushforward C f x = F.germ x := by
  simp [germ, stalkPushforward]

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.
-- def stalkPushforward'' (f : X ⟶ Y) (ℱ : X.Presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((Functor.associator _ _ _).inv ≫
--   whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) ℱ) ≫
-- colimit.pre ((OpenNhds.inclusion x).op ⋙ ℱ) (OpenNhds.map f x).op
-- def stalkPushforward''' (f : X ⟶ Y) (ℱ : X.Presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) ℱ) :
--   colim.obj ((OpenNhds.inclusion (f x) ⋙ Opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((OpenNhds.inclusion x).op ⋙ ℱ) (OpenNhds.map f x).op

namespace stalkPushforward

@[simp]
theorem id (ℱ : X.Presheaf C) (x : X) :
    ℱ.stalkPushforward C (𝟙 X) x = (stalkFunctor C x).map (Pushforward.id ℱ).hom := by
  ext
  simp only [stalkPushforward, germ, colim_map, ι_colimMap_assoc, whiskerRight_app]
  erw [CategoryTheory.Functor.map_id]
  simp [stalkFunctor]

@[simp]
theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ℱ.stalkPushforward C (f ≫ g) x =
      (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x := by
  ext
  simp [germ, stalkPushforward]

theorem stalkPushforward_iso_of_openEmbedding {f : X ⟶ Y} (hf : OpenEmbedding f) (F : X.Presheaf C)
    (x : X) : IsIso (F.stalkPushforward _ f x) := by
  haveI := Functor.initial_of_adjunction (hf.isOpenMap.adjunctionNhds x)
  convert
      ((Functor.Final.colimitIso (hf.isOpenMap.functorNhds x).op
              ((OpenNhds.inclusion (f x)).op ⋙ f _* F) :
            _).symm ≪≫
        colim.mapIso _).isIso_hom
  swap
  · fapply NatIso.ofComponents
    · intro U
      refine F.mapIso (eqToIso ?_)
      dsimp only [Functor.op]
      exact congr_arg op (Opens.ext <| Set.preimage_image_eq (unop U).1.1 hf.inj)
    · intro U V i; erw [← F.map_comp, ← F.map_comp]; congr 1
  · change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
    ext U
    rw [← Iso.comp_inv_eq]
    erw [colimit.ι_map_assoc]
    rw [colimit.ι_pre, Category.assoc]
    erw [colimit.ι_map_assoc, colimit.ι_pre, ← F.map_comp_assoc]
    apply colimit.w ((OpenNhds.inclusion (f x)).op ⋙ f _* F) _
    dsimp only [Functor.op]
    refine ((homOfLE ?_).op : op (unop U) ⟶ _)
    exact Set.image_preimage_subset _ _

end stalkPushforward

section stalkPullback

/-- The morphism `ℱ_{f x} ⟶ (f⁻¹ℱ)ₓ` that factors through `(f_*f⁻¹ℱ)_{f x}`. -/
def stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ⟶ ((pullback C f).obj F).stalk x :=
  (stalkFunctor _ (f x)).map ((pushforwardPullbackAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x

@[reassoc (attr := simp)]
lemma germ_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (U : Opens Y) (hU : f x ∈ U) :
    F.germ ⟨f x, hU⟩ ≫ stalkPullbackHom C f F x =
      ((pushforwardPullbackAdjunction C f).unit.app F).app _ ≫
        ((pullback C f).obj F).germ ⟨x, show x ∈ (Opens.map f).obj U from hU⟩ := by
  simp [stalkPullbackHom, germ, stalkFunctor, stalkPushforward]

/-- The morphism `(f⁻¹ℱ)(U) ⟶ ℱ_{f(x)}` for some `U ∋ x`. -/
def germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : U) :
    ((pullback C f).obj F).obj (op U) ⟶ F.stalk ((f : X → Y) (x : X)) :=
  ((Opens.map f).op.isPointwiseLeftKanExtensionLanUnit F (op U)).desc
    { pt := F.stalk ((f : X → Y) (x : X))
      ι :=
        { app := fun V => F.germ ⟨((f : X → Y) (x : X)), V.hom.unop.le x.2⟩
          naturality := fun _ _ i => by erw [Category.comp_id]; exact F.germ_res i.left.unop _ } }

variable {C} in
@[ext]
lemma pullback_obj_obj_ext {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ)
    {φ ψ : ((pullback C f).obj F).obj U ⟶ Z}
    (h : ∀ (V : Opens Y) (hV : U.unop ≤ (Opens.map f).obj V),
      ((pushforwardPullbackAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ φ =
      ((pushforwardPullbackAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ ψ) : φ = ψ := by
  obtain ⟨U⟩ := U
  apply ((Opens.map f).op.isPointwiseLeftKanExtensionLanUnit F _).hom_ext
  rintro ⟨⟨V⟩, ⟨⟩, ⟨b⟩⟩
  simpa [pushforwardPullbackAdjunction, Functor.lanAdjunction_unit]
    using h V (leOfHom b)

@[reassoc (attr := simp)]
lemma pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : U) (V : Opens Y)
    (hV : U ≤ (Opens.map f).obj V) :
    ((pushforwardPullbackAdjunction C f).unit.app F).app (op V) ≫
      ((pullback C f).obj F).map (homOfLE hV).op ≫ germToPullbackStalk C f F U x =
        F.germ ⟨f x, hV x.2⟩ := by
  simpa [pushforwardPullbackAdjunction] using
    ((Opens.map f).op.isPointwiseLeftKanExtensionLanUnit F (op U)).fac _
      (CostructuredArrow.mk (homOfLE hV).op)

@[reassoc (attr := simp)]
lemma germToPullbackStalk_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : U) :
    germToPullbackStalk C f F U x ≫ stalkPullbackHom C f F x =
      ((pullback C f).obj F).germ x := by
  ext V hV
  dsimp
  simp only [pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk_assoc,
    germ_stalkPullbackHom, germ_res]

@[reassoc (attr := simp)]
lemma pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (V : (Opens Y)ᵒᵖ) (x : (Opens.map f).obj V.unop) :
    ((pushforwardPullbackAdjunction C f).unit.app F).app V ≫ germToPullbackStalk C f F _ x =
      F.germ ⟨f x, x.2⟩ := by
  simpa using pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk
    C f F ((Opens.map f).obj V.unop) x V.unop (by rfl)

/-- The morphism `(f⁻¹ℱ)ₓ ⟶ ℱ_{f(x)}`. -/
def stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    ((pullback C f).obj F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (Presheaf.pullback C f).obj F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 ⟨x, (unop U).2⟩
          naturality := fun U V i => by
            dsimp
            ext W hW
            dsimp [OpenNhds.inclusion]
            rw [Category.comp_id, ← Functor.map_comp_assoc,
              pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk]
            erw [pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk] } }

@[reassoc (attr := simp)]
lemma germ_stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X) (hV : x ∈ V) :
    ((pullback C f).obj F).germ ⟨x, hV⟩ ≫ stalkPullbackInv C f F x =
    F.germToPullbackStalk _ f V ⟨x, hV⟩ := by
  apply colimit.ι_desc

/-- The isomorphism `ℱ_{f(x)} ≅ (f⁻¹ℱ)ₓ`. -/
def stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ≅ ((pullback C f).obj F).stalk x where
  hom := stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    ext U hU
    dsimp
    rw [germ_stalkPullbackHom_assoc, germ_stalkPullbackInv, Category.comp_id,
      pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk]
  inv_hom_id := by
    ext V hV
    dsimp
    rw [germ_stalkPullbackInv_assoc, Category.comp_id, germToPullbackStalk_stalkPullbackHom]

end stalkPullback

section stalkSpecializes

variable {C}

/-- If `x` specializes to `y`, then there is a natural map `F.stalk y ⟶ F.stalk x`. -/
noncomputable def stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    F.stalk y ⟶ F.stalk x := by
  refine colimit.desc _ ⟨_, fun U => ?_, ?_⟩
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩)
  · intro U V i
    dsimp
    rw [Category.comp_id]
    let U' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩
    let V' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 : _)⟩
    exact colimit.w ((OpenNhds.inclusion x).op ⋙ F) (show V' ⟶ U' from i.unop).op

@[reassoc (attr := simp), elementwise nosimp]
theorem germ_stalkSpecializes (F : X.Presheaf C) {U : Opens X} {y : U} {x : X} (h : x ⤳ y) :
    F.germ y ≫ F.stalkSpecializes h = F.germ (⟨x, h.mem_open U.isOpen y.prop⟩ : U) :=
  colimit.ι_desc _ _

@[reassoc, elementwise nosimp]
theorem germ_stalkSpecializes' (F : X.Presheaf C) {U : Opens X} {x y : X} (h : x ⤳ y)
    (hy : y ∈ U) : F.germ ⟨y, hy⟩ ≫ F.stalkSpecializes h = F.germ ⟨x, h.mem_open U.isOpen hy⟩ :=
  colimit.ι_desc _ _

@[simp]
theorem stalkSpecializes_refl {C : Type*} [Category C] [Limits.HasColimits C] {X : TopCat}
    (F : X.Presheaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _ := by
  ext
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkSpecializes_comp {C : Type*} [Category C] [Limits.HasColimits C] {X : TopCat}
    (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z) :
    F.stalkSpecializes h' ≫ F.stalkSpecializes h = F.stalkSpecializes (h.trans h') := by
  ext
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkSpecializes_stalkFunctor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (stalkFunctor C x).map f =
      (stalkFunctor C y).map f ≫ G.stalkSpecializes h := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  ext; delta stalkFunctor; simpa [stalkSpecializes] using by rfl

@[reassoc, elementwise, simp, nolint simpNF] -- see std4#365 for the simpNF issue
theorem stalkSpecializes_stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    (f _* F).stalkSpecializes (f.map_specializes h) ≫ F.stalkPushforward _ f x =
      F.stalkPushforward _ f y ≫ F.stalkSpecializes h := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  ext; delta stalkPushforward
  simp only [stalkSpecializes, colimit.ι_desc_assoc, colimit.ι_map_assoc, colimit.ι_pre,
    Category.assoc, colimit.pre_desc, colimit.ι_desc]
  rfl

/-- The stalks are isomorphic on inseparable points -/
@[simps]
def stalkCongr {X : TopCat} {C : Type*} [Category C] [HasColimits C] (F : X.Presheaf C) {x y : X}
    (e : Inseparable x y) : F.stalk x ≅ F.stalk y :=
  ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩

end stalkSpecializes

section Concrete

variable {C}
variable [ConcreteCategory.{v} C]

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

-- Porting note (#11215): TODO: @[ext] attribute only applies to structures or lemmas proving x = y
-- @[ext]
theorem germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V}
    (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : F.obj (op U)} {sV : F.obj (op V)}
    (ih : F.map iWU.op sU = F.map iWV.op sV) :
      F.germ ⟨x, hxU⟩ sU = F.germ ⟨x, hxV⟩ sV := by
  erw [← F.germ_res iWU ⟨x, hxW⟩, ← F.germ_res iWV ⟨x, hxW⟩, comp_apply, comp_apply, ih]

variable [PreservesFilteredColimits (forget C)]

/--
For presheaves valued in a concrete category whose forgetful functor preserves filtered colimits,
every element of the stalk is the germ of a section.
-/
theorem germ_exist (F : X.Presheaf C) (x : X) (t : (stalk.{v, u} F x : Type v)) :
    ∃ (U : Opens X) (m : x ∈ U) (s : F.obj (op U)), F.germ ⟨x, m⟩ s = t := by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{v, v} _ (isColimitOfPreserves (forget C) (colimit.isColimit _)) t
  revert s e
  induction U with | h U => ?_
  cases' U with V m
  intro s e
  exact ⟨V, m, s, e⟩

theorem germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
    (s : F.obj (op U)) (t : F.obj (op V)) (h : germ F ⟨x, mU⟩ s = germ F ⟨x, mV⟩ t) :
    ∃ (W : Opens X) (_m : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff.{v, v} _
          (isColimitOfPreserves _ (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)))).mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

theorem stalkFunctor_map_injective_of_app_injective {F G : Presheaf C X} (f : F ⟶ G)
    (h : ∀ U : Opens X, Function.Injective (f.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor C x).map f) := fun s t hst => by
  rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩
  rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩
  erw [stalkFunctor_map_germ_apply _ ⟨x, _⟩] at hst
  erw [stalkFunctor_map_germ_apply _ ⟨x, _⟩] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← comp_apply, ← comp_apply, ← f.naturality, ← f.naturality, comp_apply, comp_apply] at heq
  replace heq := h W heq
  convert congr_arg (F.germ ⟨x, hxW⟩) heq using 1
  exacts [(F.germ_res_apply iWU₁ ⟨x, hxW⟩ s).symm, (F.germ_res_apply iWU₂ ⟨x, hxW⟩ t).symm]

variable [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]

/-- Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every stalk must be equal.
-/
theorem section_ext (F : Sheaf C X) (U : Opens X) (s t : F.1.obj (op U))
    (h : ∀ x : U, F.presheaf.germ x s = F.presheaf.germ x t) : s = t := by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x)
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁
  · intro x hxU
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  · intro x
    rw [heq, Subsingleton.elim (i₁ x) (i₂ x)]

/-
Note that the analogous statement for surjectivity is false: Surjectivity on stalks does not
imply surjectivity of the components of a sheaf morphism. However it does imply that the morphism
is an epi, but this fact is not yet formalized.
-/
theorem app_injective_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G)
    (U : Opens X) (h : ∀ x : U, Function.Injective ((stalkFunctor C x.val).map f)) :
    Function.Injective (f.app (op U)) := fun s t hst =>
  section_ext F _ _ _ fun x =>
    h x <| by erw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]

theorem app_injective_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X}
    (f : F.1 ⟶ G) :
    (∀ x : X, Function.Injective ((stalkFunctor C x).map f)) ↔
      ∀ U : Opens X, Function.Injective (f.app (op U)) :=
  ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x => h x.1,
    stalkFunctor_map_injective_of_app_injective f⟩

instance stalkFunctor_preserves_mono (x : X) :
    Functor.PreservesMonomorphisms (Sheaf.forget C X ⋙ stalkFunctor C x) :=
  ⟨@fun _𝓐 _𝓑 f _ =>
    ConcreteCategory.mono_of_injective _ <|
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app _ f.1).mp
                (CategoryTheory.presheaf_mono_of_mono ..) <|
              op c))
        x⟩

theorem stalk_mono_of_mono {F G : Sheaf C X} (f : F ⟶ G) [Mono f] :
    ∀ x, Mono <| (stalkFunctor C x).map f.1 :=
  fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f

theorem mono_of_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) [∀ x, Mono <| (stalkFunctor C x).map f.1] :
    Mono f :=
  (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr <|
    (NatTrans.mono_iff_mono_app _ _).mpr fun U =>
      (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr <|
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun ⟨_x, _hx⟩ =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp <| inferInstance

theorem mono_iff_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) :
    Mono f ↔ ∀ x, Mono ((stalkFunctor C x).map f.1) :=
  ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩

/-- For surjectivity, we are given an arbitrary section `t` and need to find a preimage for it.
We claim that it suffices to find preimages *locally*. That is, for each `x : U` we construct
a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V) s` and `t`
agree on `V`. -/
theorem app_surjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F ⟶ G)
    (U : Opens X) (hinj : ∀ x : U, Function.Injective ((stalkFunctor C x.1).map f.1))
    (hsurj : ∀ (t) (x : U), ∃ (V : Opens X) (_ : x.1 ∈ V) (iVU : V ⟶ U) (s : F.1.obj (op V)),
          f.1.app (op V) s = G.1.map iVU.op t) :
    Function.Surjective (f.1.app (op U)) := by
  intro t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- These neighborhoods clearly cover all of `U`.
  have V_cover : U ≤ iSup V := by
    intro x hxU
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices IsCompatible F.val V sf by
    -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
    · use s
      apply G.eq_of_locally_eq' V U iVU V_cover
      intro x
      rw [← comp_apply, ← f.1.naturality, comp_apply, s_spec, heq]
  intro x y
  -- What's left to show here is that the sections `sf` are compatible, i.e. they agree on
  -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
  apply section_ext
  intro z
  -- Here, we need to use injectivity of the stalk maps.
  apply hinj ⟨z, (iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) z.2)⟩
  dsimp only
  erw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  simp_rw [← comp_apply, f.1.naturality, comp_apply, heq, ← comp_apply, ← G.1.map_comp]
  rfl

theorem app_surjective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Bijective ((stalkFunctor C x.val).map f.1)) :
    Function.Surjective (f.1.app (op U)) := by
  refine app_surjective_of_injective_of_locally_surjective f U (fun x => (h x).1) fun t x => ?_
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, hs₀⟩ := (h x).2 (G.presheaf.germ x t)
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁, hxV₁, s₁, hs₁⟩ := F.presheaf.germ_exist x.1 s₀
  subst hs₁; rename' hs₀ => hs₁
  erw [stalkFunctor_map_germ_apply V₁ ⟨x.1, hxV₁⟩ f.1 s₁] at hs₁
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x.1 hxV₁ x.2 _ _ hs₁
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁
  rw [← comp_apply, f.1.naturality, comp_apply, heq]

theorem app_bijective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Bijective ((stalkFunctor C x.val).map f.1)) :
    Function.Bijective (f.1.app (op U)) :=
  ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x => (h x).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩

theorem app_isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    [∀ x : U, IsIso ((stalkFunctor C x.val).map f.1)] : IsIso (f.1.app (op U)) := by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijective]
  apply app_bijective_of_stalkFunctor_map_bijective
  intro x
  apply (isIso_iff_bijective _).mp
  exact Functor.map_isIso (forget C) ((stalkFunctor C x.1).map f.1)

-- Making this an instance would cause a loop in typeclass resolution with `Functor.map_isIso`
/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then if the stalk maps of a morphism
`f : F ⟶ G` are all isomorphisms, `f` must be an isomorphism.
-/
theorem isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G)
    [∀ x : X, IsIso ((stalkFunctor C x).map f.1)] : IsIso f := by
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices IsIso ((Sheaf.forget C X).map f) by exact isIso_of_fully_faithful (Sheaf.forget C X) f
  -- We show that all components of `f` are isomorphisms.
  suffices ∀ U : (Opens X)ᵒᵖ, IsIso (f.1.app U) by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ F.1 G.1 f.1 this
  intro U; induction U
  apply app_isIso_of_stalkFunctor_map_iso

/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
theorem isIso_iff_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor C x).map f.1) :=
  ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩

end Concrete

instance algebra_section_stalk (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ x).toAlgebra

@[simp]
theorem stalk_open_algebraMap {X : TopCat} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    algebraMap (F.obj <| op U) (F.stalk x) = F.germ x :=
  rfl

end TopCat.Presheaf

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
import Mathlib.CategoryTheory.Sites.Pushforward

#align_import topology.sheaves.stalks from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

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
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_functor TopCat.Presheaf.stalkFunctor

variable {C}

/-- The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk TopCat.Presheaf.stalk

-- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)
@[simp]
theorem stalkFunctor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ.stalk x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_functor_obj TopCat.Presheaf.stalkFunctor_obj

/-- The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.Presheaf C) {U : Opens X} (x : U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((OpenNhds.inclusion x.1).op ⋙ F) (op ⟨U, x.2⟩)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ TopCat.Presheaf.germ

theorem germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : U) :
    F.map i.op ≫ germ F x = germ F (i x : V) :=
  let i' : (⟨U, x.2⟩ : OpenNhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i
  colimit.w ((OpenNhds.inclusion x.1).op ⋙ F) i'.op
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_res TopCat.Presheaf.germ_res

-- Porting note : `@[elementwise]` did not generate the best lemma when applied to `germ_res`
theorem germ_res_apply (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : U) [ConcreteCategory C]
  (s) : germ F x (F.map i.op s) = germ F (i x) s := by rw [←comp_apply, germ_res]
                                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_res_apply TopCat.Presheaf.germ_res_apply

/-- A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
@[ext]
theorem stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
    (ih : ∀ (U : Opens X) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext fun U => by
    induction' U using Opposite.rec with U; cases' U with U hxU; exact ih U hxU
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inc …
                                            -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inc …
                                                                 -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_hom_ext TopCat.Presheaf.stalk_hom_ext

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkFunctor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : U) (f : F ⟶ G) :
    germ F x ≫ (stalkFunctor C x.1).map f = f.app (op U) ≫ germ G x :=
  colimit.ι_map (whiskerLeft (OpenNhds.inclusion x.1).op f) (op ⟨U, x.2⟩)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_functor_map_germ TopCat.Presheaf.stalkFunctor_map_germ

variable (C)

/-- For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphisms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
def stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x := by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  -- Porting note: The original proof was `trans; swap`, but `trans` does nothing.
  refine' ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  -- ⊢ stalk (f _* F) (↑f x) ⟶ colimit ((OpenNhds.map f x).op ⋙ ((whiskeringLeft (O …
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pushforward TopCat.Presheaf.stalkPushforward

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkPushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
    (x : (Opens.map f).obj U) :
      (f _* F).germ ⟨(f : X → Y) (x : X), x.2⟩ ≫ F.stalkPushforward C f x = F.germ x := by
  rw [stalkPushforward, germ, colimit.ι_map_assoc, colimit.ι_pre, whiskerRight_app]
  -- ⊢ F.map (NatTrans.app (NatTrans.op (OpenNhds.inclusionMapIso f ↑x).inv) (op {  …
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds ↑x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.in …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pushforward_germ TopCat.Presheaf.stalkPushforward_germ

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
  -- Porting note: We need to this to help ext tactic.
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  -- ⊢ stalkPushforward C (𝟙 X) ℱ x = (stalkFunctor C x).map (Pushforward.id ℱ).hom
  ext1 j
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑(𝟙 X) x))ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (Ope …
  induction' j with j
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑(𝟙 X) x))ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (Ope …
  rcases j with ⟨⟨_, _⟩, _⟩
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑(𝟙 X) x))ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (Ope …
  erw [colimit.ι_map_assoc]
  -- ⊢ NatTrans.app (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso (𝟙 X) x).i …
  simp [stalkFunctor, stalkPushforward]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pushforward.id TopCat.Presheaf.stalkPushforward.id

-- This proof is sadly not at all robust:
-- having to use `erw` at all is a bad sign.
@[simp]
theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ℱ.stalkPushforward C (f ≫ g) x =
      (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  -- ⊢ stalkPushforward C (f ≫ g) ℱ x = stalkPushforward C g (f _* ℱ) (↑f x) ≫ stal …
  ext U
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑(f ≫ g) x))ᵒᵖ (Opens ↑Z)ᵒᵖ C).obj (O …
  rcases U with ⟨⟨_, _⟩, _⟩
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑(f ≫ g) x))ᵒᵖ (Opens ↑Z)ᵒᵖ C).obj (O …
  simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc, whiskerRight_app, Category.assoc]
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑(f ≫ g) x))ᵒᵖ (Opens ↑Z)ᵒᵖ C).obj (O …
  simp [stalkFunctor, stalkPushforward]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pushforward.comp TopCat.Presheaf.stalkPushforward.comp

theorem stalkPushforward_iso_of_openEmbedding {f : X ⟶ Y} (hf : OpenEmbedding f) (F : X.Presheaf C)
    (x : X) : IsIso (F.stalkPushforward _ f x) := by
  haveI := Functor.initial_of_adjunction (hf.isOpenMap.adjunctionNhds x)
  -- ⊢ IsIso (stalkPushforward C f F x)
  convert IsIso.of_iso
      ((Functor.Final.colimitIso (hf.isOpenMap.functorNhds x).op
              ((OpenNhds.inclusion (f x)).op ⋙ f _* F) :
            _).symm ≪≫
        colim.mapIso _)
  swap
  -- ⊢ (IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).op ⋙ (OpenNhds.inclusion (↑f x) …
  · fapply NatIso.ofComponents
    -- ⊢ (X_1 : (OpenNhds x)ᵒᵖ) → ((IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).op ⋙  …
    · intro U
      -- ⊢ ((IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).op ⋙ (OpenNhds.inclusion (↑f x …
      refine' F.mapIso (eqToIso _)
      -- ⊢ (Opens.map f).op.obj ((OpenNhds.inclusion (↑f x)).op.obj ((IsOpenMap.functor …
      dsimp only [Functor.op]
      -- ⊢ op ((Opens.map f).obj (op ((OpenNhds.inclusion (↑f x)).obj (op ((IsOpenMap.f …
      exact congr_arg op (Opens.ext <| Set.preimage_image_eq (unop U).1.1 hf.inj)
      -- 🎉 no goals
    · intro U V i; erw [← F.map_comp, ← F.map_comp]; congr 1
      -- ⊢ ((IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).op ⋙ (OpenNhds.inclusion (↑f x …
                   -- ⊢ F.map ((Opens.map f).op.map ((OpenNhds.inclusion (↑f x)).op.map ((IsOpenMap. …
                                                     -- 🎉 no goals
  · change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
    -- ⊢ stalkPushforward C f F x = ((Functor.Final.colimitIso (IsOpenMap.functorNhds …
    ext U
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑f x))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhd …
    rw [← Iso.comp_inv_eq]
    -- ⊢ (colimit.ι (((whiskeringLeft (OpenNhds (↑f x))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNh …
    erw [colimit.ι_map_assoc]
    -- ⊢ (NatTrans.app (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) …
    rw [colimit.ι_pre, Category.assoc]
    -- ⊢ NatTrans.app (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv)  …
    erw [colimit.ι_map_assoc, colimit.ι_pre, ← F.map_comp_assoc]
    -- ⊢ F.map (NatTrans.app (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) U ≫ (eq …
    apply colimit.w ((OpenNhds.inclusion (f x)).op ⋙ f _* F) _
    -- ⊢ U ⟶ (IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).op.obj ((OpenNhds.map f x). …
    dsimp only [Functor.op]
    -- ⊢ U ⟶ op ((IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).obj (op ((OpenNhds.map  …
    refine' ((homOfLE _).op : op (unop U) ⟶ _)
    -- ⊢ (IsOpenMap.functorNhds (_ : IsOpenMap ↑f) x).obj (op ((OpenNhds.map f x).obj …
    exact Set.image_preimage_subset _ _
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pushforward.stalk_pushforward_iso_of_open_embedding TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_openEmbedding

end stalkPushforward

section stalkPullback

/-- The morphism `ℱ_{f x} ⟶ (f⁻¹ℱ)ₓ` that factors through `(f_*f⁻¹ℱ)_{f x}`. -/
def stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ⟶ (pullbackObj f F).stalk x :=
  (stalkFunctor _ (f x)).map ((pushforwardPullbackAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pullback_hom TopCat.Presheaf.stalkPullbackHom

/-- The morphism `(f⁻¹ℱ)(U) ⟶ ℱ_{f(x)}` for some `U ∋ x`. -/
def germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : U) :
    (pullbackObj f F).obj (op U) ⟶ F.stalk ((f : X → Y) (x : X)) :=
  colimit.desc (Lan.diagram (Opens.map f).op F (op U))
    { pt := F.stalk ((f : X → Y) (x : X))
      ι :=
        { app := fun V => F.germ ⟨((f : X → Y) (x : X)), V.hom.unop.le x.2⟩
          naturality := fun _ _ i => by erw [Category.comp_id]; exact F.germ_res i.left.unop _ } }
                                        -- ⊢ (Lan.diagram (Opens.map f).op F (op U)).map i ≫ (fun V => germ F { val := ↑f …
                                                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_to_pullback_stalk TopCat.Presheaf.germToPullbackStalk

/-- The morphism `(f⁻¹ℱ)ₓ ⟶ ℱ_{f(x)}`. -/
def stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    (pullbackObj f F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ Presheaf.pullbackObj f F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 ⟨x, (unop U).2⟩
          naturality := fun _ _ _ => by erw [colimit.pre_desc, Category.comp_id]; congr } }
                                        -- ⊢ colimit.desc (CostructuredArrow.map ((OpenNhds.inclusion x).op.map x✝) ⋙ Lan …
                                                                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pullback_inv TopCat.Presheaf.stalkPullbackInv

/-- The isomorphism `ℱ_{f(x)} ≅ (f⁻¹ℱ)ₓ`. -/
def stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ≅ (pullbackObj f F).stalk x where
  hom := stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    delta
      stalkPullbackHom stalkPullbackInv stalkFunctor Presheaf.pullback stalkPushforward
      germToPullbackStalk germ
    change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
    -- ⊢ (((whiskeringLeft (OpenNhds (↑f x))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhds.inclusio …
    ext j
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑f x))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhd …
    induction' j with j
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑f x))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhd …
    cases j
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑f x))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhd …
    simp only [TopologicalSpace.OpenNhds.inclusionMapIso_inv, whiskerRight_app, whiskerLeft_app,
      whiskeringLeft_obj_map, Functor.comp_map, colimit.ι_map_assoc, NatTrans.op_id, lan_obj_map,
      pushforwardPullbackAdjunction_unit_app_app, Category.assoc, colimit.ι_pre_assoc]
    erw [colimit.ι_desc, colimit.pre_desc, colimit.ι_desc, Category.comp_id]
    -- ⊢ NatTrans.app (Cocone.whisker (CostructuredArrow.map (NatTrans.app (𝟙 (OpenNh …
    simp
    -- 🎉 no goals
  inv_hom_id := by
    delta stalkPullbackHom stalkPullbackInv stalkFunctor Presheaf.pullback stalkPushforward
    -- ⊢ colimit.desc ((OpenNhds.inclusion x).op ⋙ pullbackObj f F) { pt := stalk F ( …
    change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
    -- ⊢ colimit.desc ((OpenNhds.inclusion x).op ⋙ pullbackObj f F) { pt := stalk F ( …
    ext ⟨U_obj, U_property⟩
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inc …
    change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
    -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inc …
    ext ⟨j_left, ⟨⟨⟩⟩, j_hom⟩
    -- ⊢ colimit.ι (Lan.diagram (Opens.map f).op F ((OpenNhds.inclusion x).op.obj { u …
    erw [colimit.map_desc, colimit.map_desc, colimit.ι_desc_assoc, colimit.ι_desc_assoc,
      colimit.ι_desc, Category.comp_id]
    simp only [Cocone.whisker_ι, colimit.cocone_ι, OpenNhds.inclusionMapIso_inv,
      Cocones.precompose_obj_ι, whiskerRight_app, whiskerLeft_app, NatTrans.comp_app,
      whiskeringLeft_obj_map, NatTrans.op_id, lan_obj_map,
      pushforwardPullbackAdjunction_unit_app_app]
    erw [←
      colimit.w _
        (@homOfLE (OpenNhds x) _ ⟨_, U_property⟩
            ⟨(Opens.map f).obj (unop j_left), j_hom.unop.le U_property⟩ j_hom.unop.le).op]
    erw [colimit.ι_pre_assoc (Lan.diagram _ F _) (CostructuredArrow.map _)]
    -- ⊢ colimit.ι (Lan.diagram (Opens.map f).op F (op ((Opens.map f).obj ((OpenNhds. …
    erw [colimit.ι_pre_assoc (Lan.diagram _ F (op U_obj)) (CostructuredArrow.map _)]
    -- ⊢ colimit.ι (Lan.diagram (Opens.map f).op F (op U_obj)) ((CostructuredArrow.ma …
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_pullback_iso TopCat.Presheaf.stalkPullbackIso

end stalkPullback

section stalkSpecializes

variable {C}

/-- If `x` specializes to `y`, then there is a natural map `F.stalk y ⟶ F.stalk x`. -/
noncomputable def stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    F.stalk y ⟶ F.stalk x := by
  refine' colimit.desc _ ⟨_, fun U => _, _⟩
  -- ⊢ (((whiskeringLeft (OpenNhds y)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inclusion y). …
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩)
  · intro U V i
    -- ⊢ (((whiskeringLeft (OpenNhds y)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inclusion y). …
    dsimp
    -- ⊢ F.map ((OpenNhds.inclusion y).map i.unop).op ≫ colimit.ι ((OpenNhds.inclusio …
    rw [Category.comp_id]
    -- ⊢ F.map ((OpenNhds.inclusion y).map i.unop).op ≫ colimit.ι ((OpenNhds.inclusio …
    let U' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩
    -- ⊢ F.map ((OpenNhds.inclusion y).map i.unop).op ≫ colimit.ι ((OpenNhds.inclusio …
    let V' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 : _)⟩
    -- ⊢ F.map ((OpenNhds.inclusion y).map i.unop).op ≫ colimit.ι ((OpenNhds.inclusio …
    exact colimit.w ((OpenNhds.inclusion x).op ⋙ F) (show V' ⟶ U' from i.unop).op
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_specializes TopCat.Presheaf.stalkSpecializes

@[reassoc (attr := simp), elementwise nosimp]
theorem germ_stalkSpecializes (F : X.Presheaf C) {U : Opens X} {y : U} {x : X} (h : x ⤳ y) :
    F.germ y ≫ F.stalkSpecializes h = F.germ (⟨x, h.mem_open U.isOpen y.prop⟩ : U) :=
  colimit.ι_desc _ _
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_stalk_specializes TopCat.Presheaf.germ_stalkSpecializes

@[reassoc, elementwise nosimp]
theorem germ_stalk_specializes' (F : X.Presheaf C) {U : Opens X} {x y : X} (h : x ⤳ y)
    (hy : y ∈ U) : F.germ ⟨y, hy⟩ ≫ F.stalkSpecializes h = F.germ ⟨x, h.mem_open U.isOpen hy⟩ :=
  colimit.ι_desc _ _
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_stalk_specializes' TopCat.Presheaf.germ_stalk_specializes'

@[simp]
theorem stalkSpecializes_refl {C : Type*} [Category C] [Limits.HasColimits C] {X : TopCat}
    (F : X.Presheaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _ := by
  ext
  -- ⊢ germ F { val := x, property := hxU✝ } ≫ stalkSpecializes F (_ : x ⤳ x) = ger …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_specializes_refl TopCat.Presheaf.stalkSpecializes_refl

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkSpecializes_comp {C : Type*} [Category C] [Limits.HasColimits C] {X : TopCat}
    (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z) :
    F.stalkSpecializes h' ≫ F.stalkSpecializes h = F.stalkSpecializes (h.trans h') := by
  ext
  -- ⊢ germ F { val := z, property := hxU✝ } ≫ stalkSpecializes F h' ≫ stalkSpecial …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_specializes_comp TopCat.Presheaf.stalkSpecializes_comp

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkSpecializes_stalkFunctor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (stalkFunctor C x).map f =
      (stalkFunctor C y).map f ≫ G.stalkSpecializes h := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  -- ⊢ stalkSpecializes F h ≫ (stalkFunctor C x).map f = (stalkFunctor C y).map f ≫ …
  ext; delta stalkFunctor; simpa [stalkSpecializes] using by rfl
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds y)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inc …
       -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds y)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inc …
                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_specializes_stalk_functor_map TopCat.Presheaf.stalkSpecializes_stalkFunctor_map

@[simp, reassoc, elementwise]
theorem stalkSpecializes_stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    (f _* F).stalkSpecializes (f.map_specializes h) ≫ F.stalkPushforward _ f x =
      F.stalkPushforward _ f y ≫ F.stalkSpecializes h := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  -- ⊢ stalkSpecializes (f _* F) (_ : ↑f x ⤳ ↑f y) ≫ stalkPushforward C f F x = sta …
  ext; delta stalkPushforward
  -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑f y))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhd …
       -- ⊢ colimit.ι (((whiskeringLeft (OpenNhds (↑f y))ᵒᵖ (Opens ↑Y)ᵒᵖ C).obj (OpenNhd …
  simp only [stalkSpecializes, colimit.ι_desc_assoc, colimit.ι_map_assoc, colimit.ι_pre,
    Category.assoc, colimit.pre_desc, colimit.ι_desc]
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_specializes_stalk_pushforward TopCat.Presheaf.stalkSpecializes_stalkPushforward

/-- The stalks are isomorphic on inseparable points -/
@[simps]
def stalkCongr {X : TopCat} {C : Type*} [Category C] [HasColimits C] (F : X.Presheaf C) {x y : X}
    (e : Inseparable x y) : F.stalk x ≅ F.stalk y :=
  ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩
                                                        -- 🎉 no goals
                                                                 -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_congr TopCat.Presheaf.stalkCongr

end stalkSpecializes

section Concrete

variable {C}

variable [ConcreteCategory.{v} C]

attribute [local instance] ConcreteCategory.hasCoeToSort
-- Porting note: The following does not seem to be needed.
-- ConcreteCategory.hasCoeToFun

-- Porting note: Todo: @[ext] attribute only applies to structures or lemmas proving x = y
-- @[ext]
theorem germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V}
    (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : F.obj (op U)} {sV : F.obj (op V)}
    (ih : F.map iWU.op sU = F.map iWV.op sV) :
      F.germ ⟨x, hxU⟩ sU = F.germ ⟨x, hxV⟩ sV := by
  erw [← F.germ_res iWU ⟨x, hxW⟩, ← F.germ_res iWV ⟨x, hxW⟩, comp_apply, comp_apply, ih]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_ext TopCat.Presheaf.germ_ext

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
  -- ⊢ ∀ (s : (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inclus …
  induction U with | h U => ?_
  -- ⊢ ∀ (s : (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inclus …
  -- ⊢ ∀ (s : (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inclus …
  cases' U with V m
  -- ⊢ ∀ (s : (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ C).obj (OpenNhds.inclus …
  intro s e
  -- ⊢ ∃ U m s, ↑(germ F { val := x, property := m }) s = t
  exact ⟨V, m, s, e⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_exist TopCat.Presheaf.germ_exist

theorem germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
    (s : F.obj (op U)) (t : F.obj (op V)) (h : germ F ⟨x, mU⟩ s = germ F ⟨x, mV⟩ t) :
    ∃ (W : Opens X) (_m : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff.{v, v} _
          (isColimitOfPreserves _ (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)))).mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.germ_eq TopCat.Presheaf.germ_eq

theorem stalkFunctor_map_injective_of_app_injective {F G : Presheaf C X} (f : F ⟶ G)
    (h : ∀ U : Opens X, Function.Injective (f.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor C x).map f) := fun s t hst => by
  rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = t
  rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  erw [stalkFunctor_map_germ_apply _ ⟨x, _⟩] at hst
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  erw [stalkFunctor_map_germ_apply _ ⟨x, _⟩] at hst
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  rw [← comp_apply, ← comp_apply, ← f.naturality, ← f.naturality, comp_apply, comp_apply] at heq
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  replace heq := h W heq
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  convert congr_arg (F.germ ⟨x, hxW⟩) heq using 1
  -- ⊢ ↑(germ F { val := x, property := hxU₁ }) s = ↑(germ F { val := x, property : …
  exacts [(F.germ_res_apply iWU₁ ⟨x, hxW⟩ s).symm, (F.germ_res_apply iWU₂ ⟨x, hxW⟩ t).symm]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_functor_map_injective_of_app_injective TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective

variable [HasLimits C] [PreservesLimits (forget C)] [ReflectsIsomorphisms (forget C)]

/-- Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every stalk must be equal.
-/
theorem section_ext (F : Sheaf C X) (U : Opens X) (s t : F.1.obj (op U))
    (h : ∀ x : U, F.presheaf.germ x s = F.presheaf.germ x t) : s = t := by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x)
  -- ⊢ s = t
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁
  -- ⊢ U ≤ iSup V
  · intro x hxU
    -- ⊢ x ∈ ↑(iSup V)
    erw [Opens.mem_iSup]
    -- ⊢ ∃ i, x ∈ V i
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
    -- 🎉 no goals
  · intro x
    -- ⊢ ↑(F.val.map (i₁ x).op) s = ↑(F.val.map (i₁ x).op) t
    rw [heq, Subsingleton.elim (i₁ x) (i₂ x)]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.section_ext TopCat.Presheaf.section_ext

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
              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.app_injective_of_stalk_functor_map_injective TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective

theorem app_injective_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X}
    (f : F.1 ⟶ G) :
    (∀ x : X, Function.Injective ((stalkFunctor C x).map f)) ↔
      ∀ U : Opens X, Function.Injective (f.app (op U)) :=
  ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x => h x.1,
    stalkFunctor_map_injective_of_app_injective f⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.app_injective_iff_stalk_functor_map_injective TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective

instance stalkFunctor_preserves_mono (x : X) :
    Functor.PreservesMonomorphisms (Sheaf.forget C X ⋙ stalkFunctor C x) :=
  ⟨@fun _𝓐 _𝓑 f m =>
    ConcreteCategory.mono_of_injective _ <|
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (@ConcreteCategory.mono_iff_injective_of_preservesPullback _ _ _ _ _ (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app _ f.1).mp
                (@CategoryTheory.presheaf_mono_of_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) <|
              op c))
        x⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_functor_preserves_mono TopCat.Presheaf.stalkFunctor_preserves_mono

theorem stalk_mono_of_mono {F G : Sheaf C X} (f : F ⟶ G) [Mono f] :
    ∀ x, Mono <| (stalkFunctor C x).map f.1 :=
  fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_mono_of_mono TopCat.Presheaf.stalk_mono_of_mono

theorem mono_of_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) [∀ x, Mono <| (stalkFunctor C x).map f.1] :
    Mono f :=
  (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr <|
    (NatTrans.mono_iff_mono_app _ _).mpr fun U =>
      (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr <|
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun ⟨_x, _hx⟩ =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp <| inferInstance
set_option linter.uppercaseLean3 false in
#align Top.presheaf.mono_of_stalk_mono TopCat.Presheaf.mono_of_stalk_mono

theorem mono_iff_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) :
    Mono f ↔ ∀ x, Mono ((stalkFunctor C x).map f.1) :=
  ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.mono_iff_stalk_mono TopCat.Presheaf.mono_iff_stalk_mono

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
  -- ⊢ ∃ a, ↑(NatTrans.app f.val (op U)) a = t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- ⊢ ∃ a, ↑(NatTrans.app f.val (op U)) a = t
  -- These neighborhoods clearly cover all of `U`.
  have V_cover : U ≤ iSup V := by
    intro x hxU
    erw [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices IsCompatible F.val V sf by
    -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
    · use s
      apply G.eq_of_locally_eq' V U iVU V_cover
      intro x
      rw [← comp_apply, ← f.1.naturality, comp_apply, s_spec, heq]
  intro x y
  -- ⊢ ↑(F.val.map (Opens.infLELeft (V x) (V y)).op) (sf x) = ↑(F.val.map (Opens.in …
  -- What's left to show here is that the sections `sf` are compatible, i.e. they agree on
  -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
  apply section_ext
  -- ⊢ ∀ (x_1 : { x_1 // x_1 ∈ V x ⊓ V y }), ↑(germ (Sheaf.presheaf F) x_1) (↑(F.va …
  intro z
  -- ⊢ ↑(germ (Sheaf.presheaf F) z) (↑(F.val.map (Opens.infLELeft (V x) (V y)).op)  …
  -- Here, we need to use injectivity of the stalk maps.
  apply hinj ⟨z, (iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) z.2)⟩
  -- ⊢ ↑((stalkFunctor C ↑{ val := ↑z, property := (_ : ↑z ∈ ↑U) }).map f.val) (↑(g …
  dsimp only
  -- ⊢ ↑((stalkFunctor C ↑z).map f.val) (↑(germ (Sheaf.presheaf F) z) (↑(F.val.map  …
  erw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  -- ⊢ ↑(colimit.ι ((OpenNhds.inclusion ↑z).op ⋙ G.val) (op { obj := V x ⊓ V y, pro …
  simp_rw [← comp_apply, f.1.naturality, comp_apply, heq, ← comp_apply, ← G.1.map_comp]
  -- ⊢ ↑(colimit.ι ((OpenNhds.inclusion ↑z).op ⋙ G.val) (op { obj := V x ⊓ V y, pro …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.app_surjective_of_injective_of_locally_surjective TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective

theorem app_surjective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Bijective ((stalkFunctor C x.val).map f.1)) :
    Function.Surjective (f.1.app (op U)) := by
  refine' app_surjective_of_injective_of_locally_surjective f U (fun x => (h x).1) fun t x => _
  -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, hs₀⟩ := (h x).2 (G.presheaf.germ x t)
  -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁, hxV₁, s₁, hs₁⟩ := F.presheaf.germ_exist x.1 s₀
  -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
  subst hs₁; rename' hs₀ => hs₁
  -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
             -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
  erw [stalkFunctor_map_germ_apply V₁ ⟨x.1, hxV₁⟩ f.1 s₁] at hs₁
  -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x.1 hxV₁ x.2 _ _ hs₁
  -- ⊢ ∃ V x iVU s, ↑(NatTrans.app f.val (op V)) s = ↑(G.val.map iVU.op) t
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁
  -- ⊢ ↑(NatTrans.app f.val (op V₂)) (↑(F.val.map iV₂V₁.op) s₁) = ↑(G.val.map iV₂U. …
  rw [← comp_apply, f.1.naturality, comp_apply, heq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.app_surjective_of_stalk_functor_map_bijective TopCat.Presheaf.app_surjective_of_stalkFunctor_map_bijective

theorem app_bijective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Bijective ((stalkFunctor C x.val).map f.1)) :
    Function.Bijective (f.1.app (op U)) :=
  ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x => (h x).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.app_bijective_of_stalk_functor_map_bijective TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective

theorem app_isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    [∀ x : U, IsIso ((stalkFunctor C x.val).map f.1)] : IsIso (f.1.app (op U)) := by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijective]
  -- ⊢ Function.Bijective ((forget C).map (NatTrans.app f.val (op U)))
  apply app_bijective_of_stalkFunctor_map_bijective
  -- ⊢ ∀ (x : { x // x ∈ U }), Function.Bijective ↑((stalkFunctor C ↑x).map f.val)
  intro x
  -- ⊢ Function.Bijective ↑((stalkFunctor C ↑x).map f.val)
  apply (isIso_iff_bijective _).mp
  -- ⊢ IsIso ↑((stalkFunctor C ↑x).map f.val)
  exact Functor.map_isIso (forget C) ((stalkFunctor C x.1).map f.1)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.app_is_iso_of_stalk_functor_map_iso TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso

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
  -- ⊢ IsIso ((Sheaf.forget C X).map f)
  -- We show that all components of `f` are isomorphisms.
  suffices ∀ U : (Opens X)ᵒᵖ, IsIso (f.1.app U) by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ F.1 G.1 f.1 this
  intro U; induction U
  -- ⊢ IsIso (NatTrans.app f.val U)
           -- ⊢ IsIso (NatTrans.app f.val (op X✝))
  apply app_isIso_of_stalkFunctor_map_iso
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_iso_of_stalk_functor_map_iso TopCat.Presheaf.isIso_of_stalkFunctor_map_iso

/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
theorem isIso_iff_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor C x).map f.1) :=
  ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_iso_iff_stalk_functor_map_iso TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso

end Concrete

instance algebra_section_stalk (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ x).toAlgebra

@[simp]
theorem stalk_open_algebraMap {X : TopCat} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    algebraMap (F.obj <| op U) (F.stalk x) = F.germ x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.stalk_open_algebra_map TopCat.Presheaf.stalk_open_algebraMap

end TopCat.Presheaf

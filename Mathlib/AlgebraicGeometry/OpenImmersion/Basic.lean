/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.open_immersion.basic
! leanprover-community/mathlib commit 533f62f4dd62a5aad24a04326e6e787c8f7e98b1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Top.Limits.Pullbacks
import Mathbin.AlgebraicGeometry.LocallyRingedSpace

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersion if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `algebraic_geometry.PresheafedSpace.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `algebraic_geometry.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.lift`: Any morphism whose range is
  contained in an open immersion factors though the open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `to_SheafedSpace_hom`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `to_LocallyRingedSpace_hom`.

## Main results

* `algebraic_geometry.PresheafedSpace.is_open_immersion.comp`: The composition of two open
  immersions is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso`: An iso is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `Top` preserves it).
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left`: Open immersions
  are stable under pullbacks.
* `algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso` An (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/


open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) : Prop where
  base_open : OpenEmbedding f.base
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.IsOpenMap.Functor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f
#align algebraic_geometry.SheafedSpace.is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

local notation "is_open_immersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] is_open_immersion.c_iso

section

variable {X Y : PresheafedSpace.{v} C} {f : X ⟶ Y} (H : is_open_immersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev openFunctor :=
  H.base_open.IsOpenMap.Functor
#align algebraic_geometry.PresheafedSpace.is_open_immersion.open_functor AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.openFunctor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _)
    (by
      symm
      fapply nat_iso.of_components
      intro U
      refine'
        as_iso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eq_to_iso _)
      · induction U using Opposite.rec'
        cases U
        dsimp only [IsOpenMap.functor, functor.op, opens.map]
        congr 2
        erw [Set.preimage_image_eq _ H.base_open.inj]
        rfl
      · intro U V i
        simp only [CategoryTheory.eqToIso.hom, TopCat.Presheaf.pushforwardObj_map, category.assoc,
          functor.op_map, iso.trans_hom, as_iso_hom, functor.map_iso_hom, ← X.presheaf.map_comp]
        erw [f.c.naturality_assoc, ← X.presheaf.map_comp]
        congr)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict

@[simp]
theorem isoRestrict_hom_ofRestrict : H.isoRestrict.Hom ≫ Y.of_restrict _ = f :=
  by
  ext
  · simp only [comp_c_app, iso_restrict_hom_c_app, nat_trans.comp_app, eq_to_hom_refl,
      of_restrict_c_app, category.assoc, whisker_right_id']
    erw [category.comp_id, f.c.naturality_assoc, ← X.presheaf.map_comp]
    trans f.c.app x ≫ X.presheaf.map (𝟙 _)
    · congr
    · erw [X.presheaf.map_id, category.comp_id]
  · rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_hom_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict

@[simp]
theorem isoRestrict_inv_ofRestrict : H.isoRestrict.inv ≫ f = Y.of_restrict _ := by
  rw [iso.inv_comp_eq, iso_restrict_hom_of_restrict]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_inv_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict

instance mono [H : is_open_immersion f] : Mono f := by rw [← H.iso_restrict_hom_of_restrict];
  apply mono_comp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.mono AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : is_open_immersion f] (g : Y ⟶ Z)
    [hg : is_open_immersion g] : is_open_immersion (f ≫ g)
    where
  base_open := hg.base_open.comp hf.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, functor.op, comp_base,
      TopCat.Presheaf.pushforwardObj_obj, opens.map_comp_obj]
    apply (config := { instances := false }) is_iso.comp_is_iso
    swap
    · have : (opens.map g.base).obj (h.functor.obj U) = hf.open_functor.obj U :=
        by
        ext1
        dsimp only [opens.map_coe, IsOpenMap.functor_obj_coe, comp_base]
        rw [coe_comp, ← Set.image_image, Set.preimage_image_eq _ hg.base_open.inj]
      rw [this]
      infer_instance
    · have : h.functor.obj U = hg.open_functor.obj (hf.open_functor.obj U) :=
        by
        ext1
        dsimp only [IsOpenMap.functor_obj_coe]
        rw [comp_base, coe_comp, ← Set.image_image]
      rw [this]
      infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.comp AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.Presheaf.obj (op U) ⟶ Y.Presheaf.obj (op (H.openFunctor.obj U)) :=
  X.Presheaf.map (eqToHom (by simp [opens.map, Set.preimage_image_eq _ H.base_open.inj])) ≫
    inv (f.c.app (op (H.openFunctor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp

@[simp, reassoc]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.Presheaf.map i ≫ H.invApp (unop V) =
      H.invApp (unop U) ≫ Y.Presheaf.map (H.openFunctor.op.map i) :=
  by
  simp only [inv_app, ← category.assoc]
  rw [is_iso.comp_inv_eq]
  simp only [category.assoc, f.c.naturality, is_iso.inv_hom_id_assoc, ← X.presheaf.map_comp]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_naturality AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality

instance (U : Opens X) : IsIso (H.invApp U) := by delta inv_app; infer_instance

theorem inv_invApp (U : Opens X) :
    inv (H.invApp U) =
      f.c.app (op (H.openFunctor.obj U)) ≫
        X.Presheaf.map (eqToHom (by simp [opens.map, Set.preimage_image_eq _ H.base_open.inj])) :=
  by
  rw [← cancel_epi (H.inv_app U)]
  rw [is_iso.hom_inv_id]
  delta inv_app
  simp [← functor.map_comp]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp

@[simp, reassoc, elementwise]
theorem invApp_app (U : Opens X) :
    H.invApp U ≫ f.c.app (op (H.openFunctor.obj U)) =
      X.Presheaf.map (eqToHom (by simp [opens.map, Set.preimage_image_eq _ H.base_open.inj])) :=
  by rw [inv_app, category.assoc, is_iso.inv_hom_id, category.comp_id]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app

@[simp, reassoc]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.Presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U)).op :
          op U ⟶ op (H.openFunctor.obj ((Opens.map f.base).obj U))) :=
  by erw [← category.assoc]; rw [is_iso.comp_inv_eq, f.c.naturality]; congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp

/-- A variant of `app_inv_app` that gives an `eq_to_hom` instead of `hom_of_le`. -/
@[reassoc]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.Presheaf.map
        (eqToHom
            (by
              apply le_antisymm
              · exact Set.image_preimage_subset f.base U.1
              · rw [← SetLike.coe_subset_coe]
                refine' LE.le.trans_eq _ (@Set.image_preimage_eq_inter_range _ _ f.base U.1).symm
                exact set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op :=
  by erw [← category.assoc]; rw [is_iso.comp_inv_eq, f.c.naturality]; congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app' AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_inv_app'

/-- An isomorphism is an open immersion. -/
instance ofIso {X Y : PresheafedSpace.{v} C} (H : X ≅ Y) : is_open_immersion H.Hom
    where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).OpenEmbedding
  c_iso _ := inferInstance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso

instance (priority := 100) ofIsIso {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    is_open_immersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIsIso

instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : OpenEmbedding f) : is_open_immersion (Y.of_restrict hf)
    where
  base_open := hf
  c_iso U := by
    dsimp
    have : (opens.map f).obj (hf.is_open_map.functor.obj U) = U :=
      by
      ext1
      exact Set.preimage_image_eq _ hf.inj
    convert show is_iso (Y.presheaf.map (𝟙 _)) from inferInstance
    · apply Subsingleton.helim
      rw [this]
    · rw [Y.presheaf.map_id]
      infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict

@[elementwise, simp]
theorem ofRestrict_invApp {C : Type _} [Category C] (X : PresheafedSpace C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp U = 𝟙 _ :=
  by
  delta PresheafedSpace.is_open_immersion.inv_app
  rw [is_iso.comp_inv_eq, category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso (f : X ⟶ Y) [h : is_open_immersion f] [h' : Epi f.base] : IsIso f :=
  by
  apply (config := { instances := false }) is_iso_of_components
  · let this.1 : X ≃ₜ Y :=
      (Homeomorph.ofEmbedding _ h.base_open.to_embedding).trans
        { toFun := Subtype.val
          invFun := fun x =>
            ⟨x, by rw [set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp h')]; trivial⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
    convert is_iso.of_iso (TopCat.isoOfHomeo this)
    · ext; rfl
  · apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
    intro U
    have : U = op (h.open_functor.obj ((opens.map f.base).obj (unop U))) :=
      by
      induction U using Opposite.rec'
      cases U
      dsimp only [functor.op, opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert @is_open_immersion.c_iso _ h ((opens.map f.base).obj (unop U))
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso

instance stalk_iso [HasColimits C] [H : is_open_immersion f] (x : X) : IsIso (stalkMap f x) :=
  by
  rw [← H.iso_restrict_hom_of_restrict]
  rw [PresheafedSpace.stalk_map.comp]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso

end

section Pullback

noncomputable section

variable {X Y Z : PresheafedSpace.{v} C} (f : X ⟶ Z) [hf : is_open_immersion f] (g : Y ⟶ Z)

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base) ⟶ X
    where
  base := pullback.fst
  c :=
    { app := fun U =>
        hf.invApp (unop U) ≫
          g.c.app (op (hf.base_open.IsOpenMap.Functor.obj (unop U))) ≫
            Y.Presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, Subtype.mk_eq_mk, unop_op, op_inj_iff, opens.map,
                    Subtype.coe_mk, functor.op_obj, Subtype.val_eq_coe]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    simpa using h₁
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, concrete_category.congr_hom pullback.condition x⟩))
      naturality' := by
        intro U V i
        induction U using Opposite.rec'
        induction V using Opposite.rec'
        simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforwardObj_map, category.assoc,
          nat_trans.naturality_assoc, functor.op_map, inv_naturality_assoc, ← Y.presheaf.map_comp]
        erw [← Y.presheaf.map_comp]
        congr }
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.of_restrict _ ≫ g :=
  by
  ext U
  · induction U using Opposite.rec'
    dsimp only [comp_c_app, nat_trans.comp_app, unop_op, whisker_right_app,
      pullback_cone_of_left_fst]
    simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforwardObj_map, app_inv_app_assoc,
      eq_to_hom_app, eq_to_hom_unop, category.assoc, nat_trans.naturality_assoc, functor.op_map]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr
  · simpa using pullback.condition
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.of_restrict _)
    (pullback_cone_of_left_condition f g)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft

variable (s : PullbackCone f g)

/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullbackConeOfLeftLift : s.pt ⟶ (pullbackConeOfLeft f g).pt
    where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.Presheaf.map
            (eqToHom
              (by
                dsimp only [opens.map, IsOpenMap.functor, functor.op]
                congr 2
                let s' : pullback_cone f.base g.base := pullback_cone.mk s.fst.base s.snd.base _
                have : _ = s.snd.base := limit.lift_π s' walking_cospan.right
                conv_lhs =>
                  erw [← this]
                  rw [coe_comp]
                  erw [← Set.preimage_preimage]
                erw [Set.preimage_image_eq _
                    (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base).inj]))
      naturality' := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [category.assoc]
        erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
        congr }
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst :=
  by
  ext x
  · induction x using Opposite.rec'
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [category.assoc]
    erw [← s.X.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (hf.open_functor.obj x))
    dsimp only [comp_c_app, unop_op] at this 
    rw [← is_iso.comp_inv_eq] at this 
    reassoc! this
    erw [← this, hf.inv_app_app_assoc, s.fst.c.naturality_assoc]
    simpa [eq_to_hom_map]
  · change pullback.lift _ _ _ ≫ pullback.fst = _
    simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd :=
  by
  ext x
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.X.presheaf.map (𝟙 _)
    · congr
    · rw [s.X.presheaf.map_id]; erw [category.comp_id]
  · change pullback.lift _ _ _ ≫ pullback.snd = _
    simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd

instance pullbackConeSndIsOpenImmersion : is_open_immersion (pullbackConeOfLeft f g).snd :=
  by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_snd_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeSndIsOpenImmersion

/-- The constructed pullback cone is indeed the pullback. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  by
  apply pullback_cone.is_limit_aux'
  intro s
  use pullback_cone_of_left_lift f g s
  use pullback_cone_of_left_lift_fst f g s
  use pullback_cone_of_left_lift_snd f g s
  intro m h₁ h₂
  rw [← cancel_mono (pullback_cone_of_left f g).snd]
  exact h₂.trans (pullback_cone_of_left_lift_snd f g s).symm
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullbackSndOfLeft : is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft

/-- Open immersions are stable under base-change. -/
instance pullbackFstOfRight : is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackFstOfRight

instance pullbackToBaseIsOpenImmersion [is_open_immersion g] :
    is_open_immersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackToBaseIsOpenImmersion

instance forgetPreservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit.postcompose_hom_equiv (diagramIsoCospan.{v} _) _).toFun
      refine' (is_limit.equiv_iso_limit _).toFun (limit.is_limit (cospan f.base g.base))
      fapply cones.ext
      exact iso.refl _
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [category.id_comp]
      rintro (_ | _ | _) <;> symm
      · erw [category.comp_id]
        exact limit.w (cospan f.base g.base) walking_cospan.hom.inl
      · exact category.comp_id _
      · exact category.comp_id _)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfLeft

instance forgetPreservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullbackSymmetry (forget C) f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfRight

theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  haveI := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.to_embedding g.base H
  have : is_iso (pullback.snd : pullback f g ⟶ _).base :=
    by
    delta pullback.snd
    rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
    change is_iso (_ ≫ pullback.snd)
    infer_instance
  apply to_iso
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_is_iso_of_range_subset f g H
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g := by
  erw [category.assoc]; rw [is_iso.inv_comp_eq]; exact pullback.condition
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_fac AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
def isoOfRangeEq [is_open_immersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y
    where
  Hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id' := by rw [← cancel_mono f]; simp
  inv_hom_id' := by rw [← cancel_mono g]; simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_of_range_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace.{v} C} (Y : SheafedSpace C)

variable (f : X ⟶ Y.toPresheafedSpace) [H : is_open_immersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace : SheafedSpace C
    where
  IsSheaf :=
    by
    apply TopCat.Presheaf.isSheaf_of_iso (sheaf_iso_of_iso H.iso_restrict.symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace

@[simp]
theorem toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_to_PresheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_toPresheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom

@[simp]
theorem toSheafedSpaceHom_base : (toSheafedSpaceHom Y f).base = f.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_base AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_base

@[simp]
theorem toSheafedSpaceHom_c : (toSheafedSpaceHom Y f).c = f.c :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_c AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_c

instance toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_isOpenImmersion

@[simp]
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [is_open_immersion f] :
    toSheafedSpace Y f = X := by cases X; rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.SheafedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.sheafedSpace_toSheafedSpace

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace.{u} CommRingCat.{u}} (Y : LocallyRingedSpace.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : is_open_immersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpace
    where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  LocalRing x :=
    haveI : LocalRing (Y.to_SheafedSpace.to_PresheafedSpace.stalk (f.base x)) := Y.local_ring _
    (as_iso (stalk_map f x)).commRingCatIsoToRingEquiv.LocalRing
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace

@[simp]
theorem toLocallyRingedSpace_toSheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_toSheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun x => inferInstance⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom

@[simp]
theorem toLocallyRingedSpaceHom_val : (toLocallyRingedSpaceHom Y f).val = f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom_val AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom_val

instance toLocallyRingedSpace_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_isOpenImmersion

@[simp]
theorem locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.1 = X := by cases X;
  delta to_LocallyRingedSpace; simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.LocallyRingedSpace_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.locallyRingedSpace_toLocallyRingedSpace

end ToLocallyRingedSpace

theorem isIso_of_subset {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) :=
  by
  have : U = H.base_open.is_open_map.functor.obj ((opens.map f.base).obj U) :=
    by
    ext1
    exact (set.inter_eq_left_iff_subset.mpr hU).symm.trans set.image_preimage_eq_inter_range.symm
  convert PresheafedSpace.is_open_immersion.c_iso ((opens.map f.base).obj U)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.is_iso_of_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isIso_of_subset

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

instance (priority := 100) of_isIso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ f (SheafedSpace.forgetToPresheafedSpace.map_isIso _)
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_isIso

instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f g
#align algebraic_geometry.SheafedSpace.is_open_immersion.comp AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp

section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : SheafedSpace.IsOpenImmersion f]

local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

instance : Mono f :=
  forget.mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f by infer_instance)

instance forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion (forget.map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion

instance hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) :=
  by
  apply has_limit_of_iso (diagramIsoCospan.{v} _).symm
  change has_limit (cospan (forget.map f) (forget.map g))
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map f) (forget.map g)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left'

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) :=
  by
  apply has_limit_of_iso (diagramIsoCospan.{v} _).symm
  change has_limit (cospan (forget.map g) (forget.map f))
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map g) (forget.map f)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right'

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfLeft

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfRight

instance sheafedSpaceForgetPreservesOfLeft : PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.compPreservesLimit _ _ _ _ forget (PresheafedSpace.forget C) _
    (by
      apply (config := { instances := true })
        preserves_limit_of_iso_diagram _ (diagramIsoCospan.{v} _).symm
      dsimp
      infer_instance)
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpaceForgetPreservesOfLeft

instance sheafedSpaceForgetPreservesOfRight : PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpaceForgetPreservesOfRight

instance sheafedSpace_hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_left

instance sheafedSpace_hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance sheafedSpace_pullback_snd_of_left :
    SheafedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  have : _ = limit.π (cospan f g) right := preserves_limits_iso_hom_π forget (cospan f g) right
  rw [← this]
  have := has_limit.iso_of_nat_iso_hom_π (diagramIsoCospan.{v} (cospan f g ⋙ forget)) right
  erw [category.comp_id] at this 
  rw [← this]
  dsimp
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_snd_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_snd_of_left

instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  delta pullback.fst
  have : _ = limit.π (cospan g f) left := preserves_limits_iso_hom_π forget (cospan g f) left
  rw [← this]
  have := has_limit.iso_of_nat_iso_hom_π (diagramIsoCospan.{v} (cospan g f ⋙ forget)) left
  erw [category.comp_id] at this 
  rw [← this]
  dsimp
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_fst_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_right

instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) :=
  by
  rw [← limit.w (cospan f g) hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_to_base_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_to_base_isOpenImmersion

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] [ConcreteCategory.{v} C]

variable [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)]

variable [PreservesFilteredColimits (forget C)]

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : OpenEmbedding f.base)
    [H : ∀ x : X, IsIso (PresheafedSpace.stalkMap f x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U =>
      by
      apply (config := { instances := false })
        TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward f.base).obj X.sheaf from ⟨f.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.stalk_map at H 
      haveI H' :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_openEmbedding C hf X.presheaf y
      have := @is_iso.comp_is_iso _ H (@is_iso.inv_is_iso _ H')
      rw [category.assoc, is_iso.hom_inv_id, category.comp_id] at this 
      exact this }
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso

end OfStalkIso

section Prod

variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace C) [HasColimit F]
  (i : Discrete ι)

theorem sigma_ι_openEmbedding : OpenEmbedding (colimit.ι F i).base :=
  by
  rw [← show _ = (colimit.ι F i).base from ι_preserves_colimits_iso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ discrete.mk)) i :=
    has_colimit.iso_of_nat_iso_ι_hom discrete.nat_iso_functor i
  rw [← iso.eq_comp_inv] at this 
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ discrete.mk) i.as
  rw [← iso.eq_comp_inv] at this 
  cases i
  rw [this]
  simp_rw [← category.assoc, TopCat.openEmbedding_iff_comp_isIso,
    TopCat.openEmbedding_iff_isIso_comp]
  dsimp
  exact openEmbedding_sigmaMk
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_open_embedding AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_openEmbedding

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_openEmbedding F i).IsOpenMap.Functor.obj U)) =
      ⊥ :=
  by
  ext
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq :=
    concrete_category.congr_arg
      (preserves_colimit_iso (SheafedSpace.forget C) F ≪≫
          has_colimit.iso_of_nat_iso discrete.nat_iso_functor ≪≫ TopCat.sigmaIsoSigma.{v} _).Hom
      Eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq 
  rw [ι_preserves_colimits_iso_inv] at eq 
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at
    eq 
  cases i; cases j
  rw [ι_preserves_colimits_iso_hom_assoc, ι_preserves_colimits_iso_hom_assoc,
    has_colimit.iso_of_nat_iso_ι_hom_assoc, has_colimit.iso_of_nat_iso_ι_hom_assoc,
    TopCat.sigmaIsoSigma_hom_ι.{v}, TopCat.sigmaIsoSigma_hom_ι.{v}] at eq 
  exact h (congr_arg discrete.mk (congr_arg Sigma.fst Eq))
#align algebraic_geometry.SheafedSpace.is_open_immersion.image_preimage_is_empty AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty

instance sigma_ι_isOpenImmersion [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i)
    where
  base_open := sigma_ι_openEmbedding F i
  c_iso U :=
    by
    have e : colimit.ι F i = _ :=
      (ι_preserves_colimits_iso_inv SheafedSpace.forget_to_PresheafedSpace F i).symm
    have H :
      OpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) i ≫
            (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv).base :=
      e ▸ sigma_ι_open_embedding F i
    suffices
      is_iso
        ((colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) i ≫
                (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv).c.app
          (op (H.is_open_map.functor.obj U)))
      by convert this
    rw [PresheafedSpace.comp_c_app, ←
      PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π]
    rsuffices :
      is_iso
        (limit.π
          (PresheafedSpace.componentwise_diagram (F ⋙ SheafedSpace.forget_to_PresheafedSpace)
            ((opens.map
                  (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv.base).obj
              (unop <| op <| H.is_open_map.functor.obj U)))
          (op i))
    · infer_instance
    apply limit_π_is_iso_of_is_strict_terminal
    intro j hj
    induction j using Opposite.rec'
    dsimp
    convert (F.obj j).Sheaf.isTerminalOfEmpty
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U
    exact (congr_arg PresheafedSpace.hom.base e).symm
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

section Pullback

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_val]; rw [is_iso.hom_inv_id]
        erw [← LocallyRingedSpace.comp_val]; rw [is_iso.inv_hom_id]; constructor <;> simpa⟩⟩
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso

instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.comp AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp

instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.1 by infer_instance)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.mono AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono

instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullbackConeOfLeft : PullbackCone f g :=
  by
  refine'
    pullback_cone.mk _
      (Y.of_restrict (TopCat.snd_openEmbedding_of_left_openEmbedding H.base_open g.1.base)) _
  · use PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst f.1 g.1
    intro x
    have :=
      PresheafedSpace.stalk_map.congr_hom _ _
        (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalk_map.comp, PresheafedSpace.stalk_map.comp] at this 
    rw [← is_iso.eq_inv_comp] at this 
    rw [this]
    infer_instance
  ·
    exact
      LocallyRingedSpace.hom.ext _ _
        (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition _ _)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeft

instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.of_restrict _) by infer_instance

/-- The constructed `pullback_cone_of_left` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s =>
    by
    use
      PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift f.1 g.1
        (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.hom.val s.condition))
    · intro x
      have :=
        PresheafedSpace.stalk_map.congr_hom _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
            (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.hom.val s.condition)))
          x
      change _ = _ ≫ PresheafedSpace.stalk_map s.snd.1 x at this 
      rw [PresheafedSpace.stalk_map.comp, ← is_iso.eq_inv_comp] at this 
      rw [this]
      infer_instance
    constructor
    ·
      exact
        LocallyRingedSpace.hom.ext _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst f.1 g.1 _)
    constructor
    ·
      exact
        LocallyRingedSpace.hom.ext _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1 _)
    intro m h₁ h₂
    rw [← cancel_mono (pullback_cone_of_left f g).snd]
    exact
      h₂.trans
        (LocallyRingedSpace.hom.ext _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
              (pullback_cone.mk s.fst.1 s.snd.1
                (congr_arg LocallyRingedSpace.hom.val s.condition))).symm)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_to_base_isOpenImmersion

instance forgetPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.toFun
      apply is_limit_of_is_limit_pullback_cone_map SheafedSpace.forget_to_PresheafedSpace
      exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.toFun
      exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesOpenImmersion

instance forgetToTopPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) :=
  by
  change
    preserves_limit _
      ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) ⋙
        PresheafedSpace.forget _)
  apply (config := { instances := false }) limits.comp_preserves_limit
  infer_instance
  apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{u} _).symm
  dsimp [SheafedSpace.forget_to_PresheafedSpace]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_Top_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToTopPreservesPullbackOfLeft

instance forgetReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfLeft

instance forgetPreservesPullbackOfRight :
    PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfRight

instance forgetToPresheafedSpacePreservesPullbackOfRight :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfRight

instance forgetReflectsPullbackOfRight :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfRight

instance forgetToPresheafedSpaceReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfLeft

instance forgetToPresheafedSpaceReflectsPullbackOfRight :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfRight

theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  apply (config := { instances := false })
    reflects_isomorphisms.reflects LocallyRingedSpace.forget_to_SheafedSpace
  apply (config := { instances := false })
    reflects_isomorphisms.reflects SheafedSpace.forget_to_PresheafedSpace
  erw [←
    preserves_pullback.iso_hom_snd
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) f g]
  haveI := PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset _ _ H'
  infer_instance
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  haveI := pullback_snd_is_iso_of_range_subset f g H'
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g := by
  erw [category.assoc]; rw [is_iso.inv_comp_eq]; exact pullback.condition
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_fac AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq

theorem lift_range (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    Set.range (lift f g H').1.base = f.1.base ⁻¹' Set.range g.1.base :=
  by
  haveI := pullback_snd_is_iso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst : pullback f g ⟶ _).val.base :=
    preserves_pullback.iso_hom_fst
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_val, SheafedSpace.comp_base, ← this, ← category.assoc, coe_comp]
  rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ, TopCat.pullback_fst_range]
  ext
  constructor
  · rintro ⟨y, eq⟩; exact ⟨y, Eq.symm⟩
  · rintro ⟨y, eq⟩; exact ⟨y, Eq.symm⟩
  · rw [← TopCat.epi_iff_surjective]
    rw [show (inv (pullback.snd : pullback f g ⟶ _)).val.base = _ from
        (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_range AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_range

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
def isoRestrict {X Y : LocallyRingedSpace} {f : X ⟶ Y} (H : LocallyRingedSpace.IsOpenImmersion f) :
    X ≅ Y.restrict H.base_open :=
  by
  apply LocallyRingedSpace.iso_of_SheafedSpace_iso
  refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
  exact H.iso_restrict
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict

end LocallyRingedSpace.IsOpenImmersion

section OpenCover

end OpenCover

end AlgebraicGeometry


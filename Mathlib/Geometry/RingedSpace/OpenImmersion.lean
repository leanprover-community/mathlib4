/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

#align_import algebraic_geometry.open_immersion.basic from "leanprover-community/mathlib"@"533f62f4dd62a5aad24a04326e6e787c8f7e98b1"

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersion if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `AlgebraicGeometry.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`: Any morphism whose range is
  contained in an open immersion factors though the open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `to_SheafedSpace_hom`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `to_LocallyRingedSpace_hom`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp`: The composition of two open
  immersions is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso`: An iso is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `TopCat` preserves it).
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft`: Open immersions
  are stable under pullbacks.
* `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso` An (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/

set_option linter.uppercaseLean3 false

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  /-- the underlying continuous map of underlying spaces from the source to an open subset of the
    target. -/
  base_open : OpenEmbedding f.base
  /-- the underlying sheaf morphism is an isomorphism on each open subset-/
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.isOpenMap.functor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
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

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

section

variable {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev openFunctor :=
  H.base_open.isOpenMap.functor
#align algebraic_geometry.PresheafedSpace.is_open_immersion.open_functor AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.openFunctor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _) <| by
    symm
    fapply NatIso.ofComponents
    · intro U
      refine asIso (f.c.app (op (openFunctor f |>.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso ?_)
      induction U using Opposite.rec' with | h U => ?_
      cases U
      dsimp only [IsOpenMap.functor, Functor.op, Opens.map]
      congr 2
      erw [Set.preimage_image_eq _ H.base_open.inj]
      rfl
    · intro U V i
      simp only [CategoryTheory.eqToIso.hom, TopCat.Presheaf.pushforwardObj_map, Category.assoc,
        Functor.op_map, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, ← X.presheaf.map_comp]
      erw [f.c.naturality_assoc, ← X.presheaf.map_comp]
      congr 1
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict

@[simp]
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  -- Porting note: `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ rfl <| NatTrans.ext _ _ <| funext fun x => ?_
  simp only [isoRestrict_hom_c_app, NatTrans.comp_app, eqToHom_refl,
    ofRestrict_c_app, Category.assoc, whiskerRight_id']
  erw [Category.comp_id, comp_c_app, f.c.naturality_assoc, ← X.presheaf.map_comp]
  trans f.c.app x ≫ X.presheaf.map (𝟙 _)
  · congr 1
  · erw [X.presheaf.map_id, Category.comp_id]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_hom_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict

@[simp]
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  rw [Iso.inv_comp_eq, isoRestrict_hom_ofRestrict]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_inv_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict

instance mono : Mono f := by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.mono AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) where
  base_open := hg.base_open.comp H.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      TopCat.Presheaf.pushforwardObj_obj, Opens.map_comp_obj]
    apply (config := { allowSynthFailures := true }) IsIso.comp_isIso
    · rw [show h.functor.obj U = (openFunctor g).obj ((openFunctor f).obj U) by ext; simp]
      infer_instance
    · have : (Opens.map g.base).obj (h.functor.obj U) = (openFunctor f).obj U := by
        ext1
        dsimp only [Opens.map_coe, IsOpenMap.functor_obj_coe, comp_base]
        -- Porting note: slightly more hand holding here: `g ∘ f` and `fun x => g (f x)`
        erw [coe_comp, show g.base ∘ f.base = fun x => g.base (f.base x) from rfl,
          ← Set.image_image g.base f.base, Set.preimage_image_eq _ hg.base_open.inj]
           -- now `erw` after #13170
      rw [this]
      infer_instance

#align algebraic_geometry.PresheafedSpace.is_open_immersion.comp AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (openFunctor f |>.obj U)) :=
  X.presheaf.map (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.inj])) ≫
    inv (f.c.app (op (openFunctor f |>.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp

@[simp, reassoc]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp (unop V) =
      invApp f (unop U) ≫ Y.presheaf.map (openFunctor f |>.op.map i) := by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Functor.op_obj, op_unop, ← X.presheaf.map_comp, Functor.op_map, Category.assoc,
    NatTrans.naturality, TopCat.Presheaf.pushforwardObj_obj, TopCat.Presheaf.pushforwardObj_map,
    Quiver.Hom.unop_op, IsIso.inv_hom_id_assoc]
  congr 1
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_naturality AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality

instance (U : Opens X) : IsIso (invApp f U) := by delta invApp; infer_instance

theorem inv_invApp (U : Opens X) :
    inv (H.invApp U) =
      f.c.app (op (openFunctor f |>.obj U)) ≫
        X.presheaf.map
          (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.inj])) := by
  rw [← cancel_epi (H.invApp U), IsIso.hom_inv_id]
  delta invApp
  simp [← Functor.map_comp]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp

@[simp, reassoc, elementwise]
theorem invApp_app (U : Opens X) :
    invApp f U ≫ f.c.app (op (openFunctor f |>.obj U)) =
      X.presheaf.map (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.inj])) := by
  rw [invApp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app

@[simp, reassoc]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (openFunctor f |>.obj ((Opens.map f.base).obj U))) := by
  erw [← Category.assoc]; rw [IsIso.comp_inv_eq, f.c.naturality]; congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ invApp f ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom
            (le_antisymm (Set.image_preimage_subset f.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op := by
  erw [← Category.assoc]; rw [IsIso.comp_inv_eq, f.c.naturality]; congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app' AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_inv_app'

/-- An isomorphism is an open immersion. -/
instance ofIso {X Y : PresheafedSpace C} (H : X ≅ Y) : IsOpenImmersion H.hom where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).openEmbedding
  -- Porting note: `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := c_isIso_of_iso H.hom; inferInstance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso

instance (priority := 100) ofIsIso {X Y : PresheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsOpenImmersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIsIso

instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : OpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) where
  base_open := hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.isOpenMap.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.inj
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
    · -- Porting note: was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/leanprover/lean4/issues/2273
      congr
      · simp only [unop_op]
        congr
      apply Subsingleton.helim
      rw [this]
    · infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict

@[elementwise, simp]
theorem ofRestrict_invApp {C : Type*} [Category C] (X : PresheafedSpace C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp U = 𝟙 _ := by
  delta invApp
  rw [IsIso.comp_inv_eq, Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr 1
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso [h' : Epi f.base] : IsIso f := by
  have : ∀ (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U) := by
    intro U
    have : U = op (openFunctor f |>.obj ((Opens.map f.base).obj (unop U))) := by
      induction U using Opposite.rec' with | h U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert H.c_iso (Opens.map f.base |>.obj <| unop U)

  have : IsIso f.c := NatIso.isIso_of_isIso_app _

  apply (config := { allowSynthFailures := true }) isIso_of_components
  let t : X ≃ₜ Y := (Homeomorph.ofEmbedding _ H.base_open.toEmbedding).trans
    { toFun := Subtype.val
      invFun := fun x =>
        ⟨x, by rw [Set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp h')]; trivial⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  exact (TopCat.isoOfHomeo t).isIso_hom

#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso

instance stalk_iso [HasColimits C] (x : X) : IsIso (stalkMap f x) := by
  rw [← H.isoRestrict_hom_ofRestrict]
  rw [PresheafedSpace.stalkMap.comp]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso

end

noncomputable section Pullback

variable {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : IsOpenImmersion f] (g : Y ⟶ Z)

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base) ⟶ X where
  base := pullback.fst
  c :=
    { app := fun U =>
        hf.invApp (unop U) ≫
          g.c.app (op (hf.base_open.isOpenMap.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, Subtype.mk_eq_mk, unop_op, op_inj_iff, Opens.map,
                    Subtype.coe_mk, Functor.op_obj]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    -- Porting note: need a slight hand holding
                    -- used to be `simpa using h₁` before #13170
                    change _ ∈ _ ⁻¹' _ ∧ _
                    simp only [TopCat.coe_of, restrict_carrier, Set.preimage_id', Set.mem_preimage,
                      SetLike.mem_coe]
                    constructor
                    · change _ ∈ U.unop at h₁
                      convert h₁
                      erw [TopCat.pullbackIsoProdSubtype_inv_fst_apply]
                    · erw [TopCat.pullbackIsoProdSubtype_inv_snd_apply]
                  · rintro _ ⟨x, h₁, rfl⟩
                    -- next line used to be
                    --  `exact ⟨_, h₁, ConcreteCategory.congr_hom pullback.condition x⟩))`
                    -- before #13170
                    refine ⟨_, h₁, ?_⟩
                    change (_ ≫ f.base) _ = (_ ≫ g.base) _
                    rw [pullback.condition]))
      naturality := by
        intro U V i
        induction U using Opposite.rec'
        induction V using Opposite.rec'
        -- Note: this doesn't fire in `simp` because of reduction of the term via structure eta
        -- before discrimination tree key generation
        rw [inv_naturality_assoc]
        simp only [restrict_carrier, restrict_presheaf, TopCat.Presheaf.pushforwardObj_obj,
          Functor.op_obj, Functor.comp_obj, Functor.op_map, NatTrans.naturality_assoc,
          TopCat.Presheaf.pushforwardObj_map, Quiver.Hom.unop_op, ← Y.presheaf.map_comp,
          Functor.comp_map, Category.assoc]
        rfl }
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g := by
  -- Porting note: `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext _ _ <| funext fun U => ?_
  · simpa using pullback.condition
  · induction U using Opposite.rec'
    -- Porting note: `NatTrans.comp_app` is not picked up by `dsimp`
    -- Perhaps see : https://github.com/leanprover-community/mathlib4/issues/5026
    rw [NatTrans.comp_app]
    dsimp only [comp_c_app, unop_op, whiskerRight_app, pullbackConeOfLeftFst]
    -- simp only [ofRestrict_c_app, NatTrans.comp_app]
    simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforwardObj_map, app_invApp_assoc,
      eqToHom_app, eqToHom_unop, Category.assoc, NatTrans.naturality_assoc, Functor.op_map]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr 1
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft

variable (s : PullbackCone f g)

/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullbackConeOfLeftLift : s.pt ⟶ (pullbackConeOfLeft f g).pt where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map, IsOpenMap.functor, Functor.op]
                congr 2
                let s' : PullbackCone f.base g.base := PullbackCone.mk s.fst.base s.snd.base
                  -- Porting note: in mathlib3, this is just an underscore
                  (congr_arg Hom.base s.condition)

                have : _ = s.snd.base := limit.lift_π s' WalkingCospan.right
                conv_lhs =>
                  erw [← this]
                  dsimp [s']
                  -- Porting note: need a bit more hand holding here about function composition
                  rw [show ∀ f g, f ∘ g = fun x => f (g x) from fun _ _ => rfl]
                  erw [← Set.preimage_preimage]
                erw [Set.preimage_image_eq _
                    (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base).inj]
                rfl))
      naturality := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [Category.assoc]
        erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
        congr 1 }
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst := by
  -- Porting note: `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext _ _ <| funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.fst = _
    simp
  · induction x using Opposite.rec' with | h x => ?_
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [← s.pt.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (openFunctor f |>.obj x))
    dsimp only [comp_c_app, unop_op] at this
    rw [← IsIso.comp_inv_eq] at this
    replace this := reassoc_of% this
    erw [← this, hf.invApp_app_assoc, s.fst.c.naturality_assoc]
    simp [eqToHom_map]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd := by
  -- Porting note: `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext _ _ <| funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.snd = _
    simp
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.pt.presheaf.map (𝟙 _)
    · congr 1
    · rw [s.pt.presheaf.map_id]; erw [Category.comp_id]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd

instance pullbackConeSndIsOpenImmersion : IsOpenImmersion (pullbackConeOfLeft f g).snd := by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_snd_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeSndIsOpenImmersion

/-- The constructed pullback cone is indeed the pullback. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) := by
  apply PullbackCone.isLimitAux'
  intro s
  use pullbackConeOfLeftLift f g s
  use pullbackConeOfLeftLift_fst f g s
  use pullbackConeOfLeftLift_snd f g s
  intro m _ h₂
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullbackSndOfLeft : IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft

/-- Open immersions are stable under base-change. -/
instance pullbackFstOfRight : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackFstOfRight

instance pullbackToBaseIsOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackToBaseIsOpenImmersion

instance forgetPreservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan _) _).toFun
      refine (IsLimit.equivIsoLimit ?_).toFun (limit.isLimit (cospan f.base g.base))
      fapply Cones.ext
      · exact Iso.refl _
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [Category.id_comp]
      rintro (_ | _ | _) <;> symm
      · erw [Category.comp_id]
        exact limit.w (cospan f.base g.base) WalkingCospan.Hom.inl
      · exact Category.comp_id _
      · exact Category.comp_id _)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfLeft

instance forgetPreservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullbackSymmetry (forget C) f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfRight

theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) := by
  haveI := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.toEmbedding g.base H
  have : IsIso (pullback.snd : pullback f g ⟶ _).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd)
    infer_instance
  apply to_iso
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g := by
  erw [Category.assoc]; rw [IsIso.inv_comp_eq]; exact pullback.condition
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_fac AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_of_range_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace C} (Y : SheafedSpace C)
variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace : SheafedSpace C where
  IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
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
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y) [IsOpenImmersion f] :
    toSheafedSpace Y f = X := by cases X; rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.SheafedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.sheafedSpace_toSheafedSpace

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace CommRingCat} (Y : LocallyRingedSpace)
variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  localRing x :=
    haveI : LocalRing (Y.stalk (f.base x)) := Y.localRing _
    (asIso (stalkMap f x)).commRingCatIsoToRingEquiv.localRing
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
  ⟨f, fun _ => inferInstance⟩
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
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.1 = X := by
    cases X; delta toLocallyRingedSpace; simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.LocallyRingedSpace_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.locallyRingedSpace_toLocallyRingedSpace

end ToLocallyRingedSpace

theorem isIso_of_subset {X Y : PresheafedSpace C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) := by
  have : U = H.base_open.isOpenMap.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert H.c_iso ((Opens.map f.base).obj U)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.is_iso_of_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isIso_of_subset

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

instance (priority := 100) of_isIso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ f
    (SheafedSpace.forgetToPresheafedSpace.map_isIso _)
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_isIso

instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f g
#align algebraic_geometry.SheafedSpace.is_open_immersion.comp AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp

noncomputable section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : SheafedSpace.IsOpenImmersion f]

-- Porting note: in mathlib3, this local notation is often followed by a space to avoid confusion
-- with the forgetful functor, now it is often wrapped in a parenthesis
local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

instance : Mono f :=
  (forget).mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f by infer_instance)

instance forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion

instance hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) := by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl)
      ((cospan f g ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map f) ((forget).map g))
    infer_instance
  apply hasLimitOfIso (diagramIsoCospan _).symm
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left'

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl)
      ((cospan g f ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map g) ((forget).map f))
    infer_instance
  apply hasLimitOfIso (diagramIsoCospan _).symm
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance
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
  @Limits.compPreservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
    inferInstance <| by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C) := by
        dsimp
        infer_instance
      apply preservesLimitOfIsoDiagram _ (diagramIsoCospan _).symm
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
    SheafedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta pullback.snd
  have : _ = limit.π (cospan f g) right := preservesLimitsIso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  erw [Category.comp_id] at this
  rw [← this]
  dsimp
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_snd_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_snd_of_left

instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  delta pullback.fst
  have : _ = limit.π (cospan g f) left := preservesLimitsIso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  erw [Category.comp_id] at this
  rw [← this]
  dsimp
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_fst_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_right

instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) := by
  rw [← limit.w (cospan f g) Hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_to_base_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_to_base_isOpenImmersion

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] [ConcreteCategory C]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimits (CategoryTheory.forget C)]

variable [PreservesFilteredColimits (CategoryTheory.forget C)]

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : OpenEmbedding f.base)
    [H : ∀ x : X.1, IsIso (PresheafedSpace.stalkMap f x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U => by
      apply (config := {allowSynthFailures := true})
        TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.base).obj X.sheaf from ⟨f.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.stalkMap at H
      haveI H' :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_openEmbedding C hf X.presheaf y
      have := @IsIso.comp_isIso _ _ _ _ _ _ _ H (@IsIso.inv_isIso _ _ _ _ _ H')
      rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this }
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso

end OfStalkIso

section Prod

-- Porting note: here `ι` should have same universe level as morphism of `C`, so needs explicit
-- universe level now
variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F]
  (i : Discrete ι)

theorem sigma_ι_openEmbedding : OpenEmbedding (colimit.ι F i).base := by
  rw [← show _ = (colimit.ι F i).base from ι_preservesColimitsIso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk) i.as
  rw [← Iso.eq_comp_inv] at this
  cases i
  rw [this, ← Category.assoc]
  -- Porting note: `simp_rw` can't use `TopCat.openEmbedding_iff_comp_isIso` and
  -- `TopCat.openEmbedding_iff_isIso_comp`.
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  erw [TopCat.openEmbedding_iff_comp_isIso, TopCat.openEmbedding_iff_comp_isIso,
    TopCat.openEmbedding_iff_comp_isIso, TopCat.openEmbedding_iff_isIso_comp]
  exact openEmbedding_sigmaMk
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_open_embedding AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_openEmbedding

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_openEmbedding F i).isOpenMap.functor.obj U)) =
      ⊥ := by
  ext x
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preservesColimitsIso_inv] at eq
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at eq
  cases i; cases j
  rw [ι_preservesColimitsIso_hom_assoc, ι_preservesColimitsIso_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    TopCat.sigmaIsoSigma_hom_ι, TopCat.sigmaIsoSigma_hom_ι] at eq
  exact h (congr_arg Discrete.mk (congr_arg Sigma.fst eq))
#align algebraic_geometry.SheafedSpace.is_open_immersion.image_preimage_is_empty AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty

instance sigma_ι_isOpenImmersion [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) where
  base_open := sigma_ι_openEmbedding F i
  c_iso U := by
    have e : colimit.ι F i = _ :=
      (ι_preservesColimitsIso_inv SheafedSpace.forgetToPresheafedSpace F i).symm
    have H :
      OpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
            (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).base :=
      e ▸ sigma_ι_openEmbedding F i
    suffices IsIso <| (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).c.app <|
      op (H.isOpenMap.functor.obj U) by
      -- Porting note (#11083): just `convert` is very slow, so helps it a bit
      convert this using 2 <;> congr
    rw [PresheafedSpace.comp_c_app,
      ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    -- Porting note: this instance created manually to make the `inferInstance` below work
    have inst1 : IsIso (preservesColimitIso forgetToPresheafedSpace F).inv.c :=
      PresheafedSpace.c_isIso_of_iso _
    rsuffices : IsIso
        (limit.π
          (PresheafedSpace.componentwiseDiagram (F ⋙ SheafedSpace.forgetToPresheafedSpace)
            ((Opens.map
                  (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
              (unop <| op <| H.isOpenMap.functor.obj U)))
          (op i))
    · infer_instance
    apply limit_π_isIso_of_is_strict_terminal
    intro j hj
    induction j using Opposite.rec' with | h j => ?_
    dsimp
    convert (F.obj j).sheaf.isTerminalOfEmpty using 3
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U using 6
    exact (congr_arg PresheafedSpace.Hom.base e).symm
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

instance (X : LocallyRingedSpace) {U : TopCat} (f : U ⟶ X.toTopCat) (hf : OpenEmbedding f) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace hf

noncomputable section Pullback

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_val]; rw [IsIso.hom_inv_id]
        erw [← LocallyRingedSpace.comp_val]; rw [IsIso.inv_hom_id]; constructor <;> rfl⟩⟩
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
def pullbackConeOfLeft : PullbackCone f g := by
  refine PullbackCone.mk ?_
      (Y.ofRestrict (TopCat.snd_openEmbedding_of_left_openEmbedding H.base_open g.1.base)) ?_
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at this
    rw [← IsIso.eq_inv_comp] at this
    rw [this]
    infer_instance
  · exact LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition _ _)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeft

instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

/-- The constructed `pullbackConeOfLeft` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.val s.condition))) ?_,
      LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst f.1 g.1 _),
      LocallyRingedSpace.Hom.ext _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 _), ?_⟩
    · intro x
      have :=
        PresheafedSpace.stalkMap.congr_hom _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
            (PullbackCone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.Hom.val s.condition)))
          x
      change _ = _ ≫ PresheafedSpace.stalkMap s.snd.1 x at this
      rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_inv_comp] at this
      rw [this]
      infer_instance
    · intro m _ h₂
      rw [← cancel_mono (pullbackConeOfLeft f g).snd]
      exact h₂.trans <| LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 <|
          PullbackCone.mk s.fst.1 s.snd.1 <| congr_arg LocallyRingedSpace.Hom.val s.condition).symm
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_to_base_isOpenImmersion

instance forgetPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_preserves_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesOpenImmersion

instance forgetToTopPreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) := by
  change PreservesLimit _ <|
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
    PresheafedSpace.forget _
  -- Porting note: was `apply (config := { instances := False }) ...`
  -- See https://github.com/leanprover/lean4/issues/2273
  have : PreservesLimit
      (cospan ((cospan f g ⋙ forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
        WalkingCospan.Hom.inl)
      ((cospan f g ⋙ forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
        WalkingCospan.Hom.inr)) (PresheafedSpace.forget CommRingCat) := by
    dsimp; infer_instance
  have : PreservesLimit (cospan f g ⋙ forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
      (PresheafedSpace.forget CommRingCat) := by
    apply preservesLimitOfIsoDiagram _ (diagramIsoCospan _).symm
  apply Limits.compPreservesLimit
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
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfRight

instance forgetReflectsPullbackOfRight :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfRight

instance forgetToPresheafedSpaceReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfLeft

instance forgetToPresheafedSpaceReflectsPullbackOfRight :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfRight

theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) := by
  apply (config := {allowSynthFailures := true}) Functor.ReflectsIsomorphisms.reflects
    (F := LocallyRingedSpace.forgetToSheafedSpace)
  apply (config := {allowSynthFailures := true}) Functor.ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace)
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) f g]
  -- Porting note: was `inferInstance`
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ _ <|
    PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ H'
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  -- Porting note (#10754): added instance manually
  have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g := by
  erw [Category.assoc]; rw [IsIso.inv_comp_eq]; exact pullback.condition
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_fac AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq

theorem lift_range (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    Set.range (lift f g H').1.base = f.1.base ⁻¹' Set.range g.1.base := by
  -- Porting note (#10754): added instance manually
  have := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst : pullback f g ⟶ _).val.base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  erw [LocallyRingedSpace.comp_val, SheafedSpace.comp_base, ← this, ← Category.assoc, coe_comp]
   -- now `erw` after #13170
  rw [Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
  -- Porting note (#11224): change `rw` to `erw` on this lemma
  · erw [TopCat.pullback_fst_range]
    ext
    constructor
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
  · erw [← TopCat.epi_iff_surjective] -- now `erw` after #13170
    rw [show (inv (pullback.snd : pullback f g ⟶ _)).val.base = _ from
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_range AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_range

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
noncomputable def isoRestrict {X Y : LocallyRingedSpace} {f : X ⟶ Y}
    (H : LocallyRingedSpace.IsOpenImmersion f) :
    X ≅ Y.restrict H.base_open :=
  LocallyRingedSpace.isoOfSheafedSpaceIso <|
    SheafedSpace.forgetToPresheafedSpace.preimageIso <|
      PresheafedSpace.IsOpenImmersion.isoRestrict f.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict

end LocallyRingedSpace.IsOpenImmersion

end AlgebraicGeometry

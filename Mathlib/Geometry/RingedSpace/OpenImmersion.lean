/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

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
  space. The morphism as morphisms of sheafed spaces is given by `toSheafedSpaceHom`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `toLocallyRingedSpaceHom`.

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


open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe w v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  /-- the underlying continuous map of underlying spaces from the source to an open subset of the
  target. -/
  base_open : IsOpenEmbedding f.base
  /-- the underlying sheaf morphism is an isomorphism on each open subset -/
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.isOpenMap.functor.obj U)))

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.1

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

section

variable {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev opensFunctor :=
  H.base_open.isOpenMap.functor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _) <| by
    symm
    fapply NatIso.ofComponents
    · intro U
      refine asIso (f.c.app (op (opensFunctor f |>.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso ?_)
      induction U with | op U => ?_
      cases U
      dsimp only [IsOpenMap.functor, Functor.op, Opens.map]
      congr 2
      erw [Set.preimage_image_eq _ H.base_open.injective]
      rfl
    · intro U V i
      dsimp
      simp only [NatTrans.naturality_assoc, TopCat.Presheaf.pushforward_obj_obj,
        TopCat.Presheaf.pushforward_obj_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
      congr 1

@[reassoc (attr := simp)]
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ rfl <| NatTrans.ext <| funext fun x => ?_
  simp only [eqToHom_refl,
    Functor.whiskerRight_id']
  erw [Category.comp_id, comp_c_app, f.c.naturality_assoc, ← X.presheaf.map_comp]
  trans f.c.app x ≫ X.presheaf.map (𝟙 _)
  · congr 1
  · simp

@[reassoc (attr := simp)]
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  rw [Iso.inv_comp_eq, isoRestrict_hom_ofRestrict]

instance mono : Mono f := by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp

lemma c_iso' {V : Opens Y} (U : Opens X) (h : V = (opensFunctor f).obj U) :
    IsIso (f.c.app (Opposite.op V)) := by
  subst h
  infer_instance

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) where
  base_open := hg.base_open.comp H.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      Opens.map_comp_obj]
    apply IsIso.comp_isIso'
    · exact c_iso' g ((opensFunctor f).obj U) (by ext; simp)
    · apply c_iso' f U
      ext1
      dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj, comp_base, TopCat.coe_comp]
      rw [Set.image_comp, Set.preimage_image_eq _ hg.base_open.injective]

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  X.presheaf.map (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) ≫
    inv (f.c.app (op (opensFunctor f |>.obj U)))

@[simp, reassoc]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) := by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Functor.op_obj, op_unop, ← X.presheaf.map_comp, Functor.op_map, Category.assoc,
    NatTrans.naturality, Quiver.Hom.unop_op, IsIso.inv_hom_id_assoc,
    TopCat.Presheaf.pushforward_obj_map]
  congr 1

instance (U : Opens X) : IsIso (invApp f U) := by delta invApp; infer_instance

theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫
        X.presheaf.map
          (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) := by
  rw [← cancel_epi (H.invApp _ U), IsIso.hom_inv_id]
  delta invApp
  simp [← Functor.map_comp]

@[simp, reassoc, elementwise]
theorem invApp_app (U : Opens X) :
    invApp f U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) := by
  rw [invApp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

@[simp, reassoc]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) := by
  erw [← Category.assoc]; rw [IsIso.comp_inv_eq, f.c.naturality]; congr

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

/-- An isomorphism is an open immersion. -/
instance ofIso {X Y : PresheafedSpace C} (H : X ≅ Y) : IsOpenImmersion H.hom where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).isOpenEmbedding
  -- Porting note: `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := c_isIso_of_iso H.hom; inferInstance

instance (priority := 100) ofIsIso {X Y : PresheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsOpenImmersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)

instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) where
  base_open := hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.isOpenMap.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
    · -- Porting note: was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/leanprover/lean4/issues/2273
      congr
      · simp only
        congr
      apply Subsingleton.helim
      rw [this]
    · infer_instance

@[elementwise, simp]
theorem ofRestrict_invApp {C : Type*} [Category C] (X : PresheafedSpace C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ := by
  delta invApp
  rw [IsIso.comp_inv_eq, Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr 1

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso [h' : Epi f.base] : IsIso f := by
  have : ∀ (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U) := by
    intro U
    have : U = op (opensFunctor f |>.obj ((Opens.map f.base).obj (unop U))) := by
      induction U with | op U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert H.c_iso (Opens.map f.base |>.obj <| unop U)
  have : IsIso f.c := NatIso.isIso_of_isIso_app _
  apply (config := { allowSynthFailures := true }) isIso_of_components
  let t : X ≃ₜ Y := H.base_open.isEmbedding.toHomeomorph.trans
    { toFun := Subtype.val
      invFun := fun x =>
        ⟨x, by rw [Set.range_eq_univ.mpr ((TopCat.epi_iff_surjective _).mp h')]; trivial⟩ }
  exact (TopCat.isoOfHomeo t).isIso_hom

instance stalk_iso [HasColimits C] (x : X) : IsIso (f.stalkMap x) := by
  rw [← H.isoRestrict_hom_ofRestrict, PresheafedSpace.stalkMap.comp]
  infer_instance

end

noncomputable section Pullback

variable {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : IsOpenImmersion f] (g : Y ⟶ Z)

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_isOpenEmbedding_of_left hf.base_open g.base) ⟶ X where
  base := pullback.fst _ _
  c :=
    { app := fun U =>
        hf.invApp _ (unop U) ≫
          g.c.app (op (hf.base_open.isOpenMap.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, op_inj_iff, Opens.map,
                    Functor.op_obj]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    -- Porting note: need a slight hand holding
                    -- used to be `simpa using h₁` before https://github.com/leanprover-community/mathlib4/pull/13170
                    change _ ∈ _ ⁻¹' _ ∧ _
                    simp only [TopCat.coe_of, restrict_carrier, Set.preimage_id', Set.mem_preimage,
                      SetLike.mem_coe]
                    constructor
                    · change _ ∈ U.unop at h₁
                      convert h₁
                      rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply]
                    · rw [TopCat.pullbackIsoProdSubtype_inv_snd_apply]
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, CategoryTheory.congr_fun pullback.condition x⟩))
      naturality := by
        intro U V i
        induction U
        induction V
        -- Note: this doesn't fire in `simp` because of reduction of the term via structure eta
        -- before discrimination tree key generation
        rw [inv_naturality_assoc]
        dsimp
        simp only [NatTrans.naturality_assoc, TopCat.Presheaf.pushforward_obj_map,
          Quiver.Hom.unop_op, ← Functor.map_comp, Category.assoc]
        rfl }

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext <| funext fun U => ?_
  · simpa using pullback.condition
  · induction U
    -- Porting note: `NatTrans.comp_app` is not picked up by `dsimp`
    -- Perhaps see : https://github.com/leanprover-community/mathlib4/issues/5026
    rw [NatTrans.comp_app]
    dsimp only [comp_c_app, unop_op, Functor.whiskerRight_app, pullbackConeOfLeftFst]
    -- simp only [ofRestrict_c_app, NatTrans.comp_app]
    simp only [app_invApp_assoc,
      eqToHom_app, Category.assoc, NatTrans.naturality_assoc]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr 1

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)

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
                  rw [← this]
                  dsimp [s']
                  rw [Function.comp_def, ← Set.preimage_preimage]
                rw [Set.preimage_image_eq _
                    (TopCat.snd_isOpenEmbedding_of_left hf.base_open g.base).injective]
                rfl))
      naturality := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [Category.assoc]
        erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
        congr 1 }

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext <| funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp
  · induction x with | op x => ?_
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [← s.pt.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (opensFunctor f |>.obj x))
    dsimp only [comp_c_app, unop_op] at this
    rw [← IsIso.comp_inv_eq] at this
    replace this := reassoc_of% this
    erw [← this, hf.invApp_app_assoc, s.fst.c.naturality_assoc]
    simp [eqToHom_map]

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext <| funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.pt.presheaf.map (𝟙 _)
    · congr 1
    · simp

instance pullbackConeSndIsOpenImmersion : IsOpenImmersion (pullbackConeOfLeft f g).snd := by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance

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

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullbackSndOfLeft : IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

/-- Open immersions are stable under base-change. -/
instance pullbackFstOfRight : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

instance pullbackToBaseIsOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance

instance forget_preservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g)
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

instance forget_preservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullback_symmetry (forget C) f g

theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd f g) := by
  haveI := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.isEmbedding g.base H
  have : IsIso (pullback.snd f g).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd _ _)
    infer_instance
  apply to_iso

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g := by
  erw [Category.assoc]; rw [IsIso.inv_comp_eq]; exact pullback.condition

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace C} (Y : SheafedSpace C)

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f] : SheafedSpace C where
  IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

@[simp]
theorem toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  f

@[simp]
theorem toSheafedSpaceHom_base : (toSheafedSpaceHom Y f).base = f.base :=
  rfl

@[simp]
theorem toSheafedSpaceHom_c : (toSheafedSpaceHom Y f).c = f.c :=
  rfl

instance toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H

@[simp]
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y) [IsOpenImmersion f] :
    toSheafedSpace Y f = X := by cases X; rfl

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace CommRingCat} (Y : LocallyRingedSpace)
variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  isLocalRing x :=
    haveI : IsLocalRing (Y.presheaf.stalk (f.base x)) := Y.isLocalRing _
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

@[simp]
theorem toLocallyRingedSpace_toSheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun _ => inferInstance⟩

@[simp]
theorem toLocallyRingedSpaceHom_val : (toLocallyRingedSpaceHom Y f).toShHom = f :=
  rfl

instance toLocallyRingedSpace_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H

@[simp]
theorem locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.1 = X := by
    cases X; delta toLocallyRingedSpace; simp

end ToLocallyRingedSpace

theorem isIso_of_subset {X Y : PresheafedSpace C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) := by
  have : U = H.base_open.isOpenMap.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert H.c_iso ((Opens.map f.base).obj U)

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

instance (priority := 100) of_isIso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ f
    (SheafedSpace.forgetToPresheafedSpace.map_isIso _)

instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f g

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

instance hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) := by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl)
      ((cospan f g ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map f) ((forget).map g))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl)
      ((cospan g f ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map g) ((forget).map f))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance sheafedSpace_forgetPreserves_of_left :
    PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.comp_preservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
    inferInstance <| by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C) := by
        dsimp
        infer_instance
      apply preservesLimit_of_iso_diagram _ (diagramIsoCospan _).symm

instance sheafedSpace_forgetPreserves_of_right :
    PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullback_symmetry _ _ _

instance sheafedSpace_hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget

instance sheafedSpace_hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget

/-- Open immersions are stable under base-change. -/
instance sheafedSpace_pullback_snd_of_left :
    SheafedSpace.IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  have : _ = limit.π (cospan f g) right := preservesLimitIso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  erw [Category.comp_id] at this
  rw [← this]
  dsimp
  infer_instance

instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst g f) := by
  delta pullback.fst
  have : _ = limit.π (cospan g f) left := preservesLimitIso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  erw [Category.comp_id] at this
  rw [← this]
  dsimp
  infer_instance

instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) := by
  rw [← limit.w (cospan f g) Hom.inl, cospan_map_inl]
  infer_instance

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [instCC : ConcreteCategory.{v} C FC]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimits (CategoryTheory.forget C)]

variable [PreservesFilteredColimits (CategoryTheory.forget C)]

include instCC in
/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.base)
    [H : ∀ x : X.1, IsIso (f.stalkMap x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U => by
      apply (config := {allowSynthFailures := true})
        TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.base).obj X.sheaf from ⟨f.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.Hom.stalkMap at H
      haveI H' := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing C
        hf.toIsInducing X.presheaf y
      have := IsIso.comp_isIso' H (@IsIso.inv_isIso _ _ _ _ _ H')
      rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this }

end OfStalkIso

section

variable {X Y : SheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev opensFunctor : Opens X ⥤ Opens Y :=
  H.base_open.isOpenMap.functor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  SheafedSpace.isoMk <| PresheafedSpace.IsOpenImmersion.isoRestrict f

@[reassoc (attr := simp)]
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f :=
  PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f

@[reassoc (attr := simp)]
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ :=
  PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict f

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  PresheafedSpace.IsOpenImmersion.invApp f U

@[reassoc (attr := simp)]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality f i

instance (U : Opens X) : IsIso (H.invApp _ U) := by delta invApp; infer_instance

theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫ X.presheaf.map
        (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.inv_invApp f U

@[reassoc (attr := simp)]
theorem invApp_app (U : Opens X) :
    H.invApp _ U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.invApp_app f U

attribute [elementwise] invApp_app

@[reassoc (attr := simp)]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) :=
  PresheafedSpace.IsOpenImmersion.app_invApp f U

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ invApp f ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom <|
            le_antisymm (Set.image_preimage_subset f.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp f U

instance ofRestrict {X : TopCat} (Y : SheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]
theorem ofRestrict_invApp {C : Type*} [Category C] (X : SheafedSpace C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (SheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ :=
  PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso [h' : Epi f.base] : IsIso f := by
  haveI : IsIso (forgetToPresheafedSpace.map f) := PresheafedSpace.IsOpenImmersion.to_iso f
  apply isIso_of_reflects_iso _ (SheafedSpace.forgetToPresheafedSpace)

instance stalk_iso [HasColimits C] (x : X) :
    IsIso (f.stalkMap x) :=
  PresheafedSpace.IsOpenImmersion.stalk_iso f x

end

section Prod

-- Porting note: here `ι` should have same universe level as morphism of `C`, so needs explicit
-- universe level now
variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F]
  (i : Discrete ι)

theorem sigma_ι_isOpenEmbedding : IsOpenEmbedding (colimit.ι F i).base := by
  rw [← show _ = (colimit.ι F i).base from ι_preservesColimitIso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk) i.as
  rw [← Iso.eq_comp_inv] at this
  cases i
  rw [this, ← Category.assoc]
  -- Porting note: `simp_rw` can't use `TopCat.isOpenEmbedding_iff_comp_isIso` and
  -- `TopCat.isOpenEmbedding_iff_isIso_comp`.
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  rw [TopCat.isOpenEmbedding_iff_comp_isIso, TopCat.isOpenEmbedding_iff_comp_isIso,
    TopCat.isOpenEmbedding_iff_comp_isIso, TopCat.isOpenEmbedding_iff_isIso_comp]
  exact .sigmaMk

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_isOpenEmbedding F i).isOpenMap.functor.obj U)) =
      ⊥ := by
  ext x
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preservesColimitIso_inv] at eq
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at eq
  cases i; cases j
  rw [ι_preservesColimitIso_hom_assoc, ι_preservesColimitIso_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    TopCat.sigmaIsoSigma_hom_ι, TopCat.sigmaIsoSigma_hom_ι] at eq
  exact h (congr_arg Discrete.mk (congr_arg Sigma.fst eq))

instance sigma_ι_isOpenImmersion_aux [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) where
  base_open := sigma_ι_isOpenEmbedding F i
  c_iso U := by
    have e : colimit.ι F i = _ :=
      (ι_preservesColimitIso_inv SheafedSpace.forgetToPresheafedSpace F i).symm
    have H :
      IsOpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
            (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).base :=
      e ▸ sigma_ι_isOpenEmbedding F i
    suffices IsIso <| (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).c.app <|
      op (H.isOpenMap.functor.obj U) by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): just `convert` is very slow, so helps it a bit
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
    induction j with | op j => ?_
    dsimp
    convert (F.obj j).sheaf.isTerminalOfEmpty using 3
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U using 6
    exact (congr_arg PresheafedSpace.Hom.base e).symm

instance sigma_ι_isOpenImmersion {ι : Type w} [Small.{v} ι]
    (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F] (i : Discrete ι)
    [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) := by
  obtain ⟨ι', ⟨e⟩⟩ := Small.equiv_small (α := ι)
  let f : Discrete ι' ≌ Discrete ι := Discrete.equivalence e.symm
  have : colimit.ι F i = (colimit.ι F i ≫ (HasColimit.isoOfEquivalence f (Iso.refl _)).inv) ≫
      (HasColimit.isoOfEquivalence f (Iso.refl _)).hom := by
    simp
  rw [this, HasColimit.isoOfEquivalence_inv_π]
  infer_instance

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

instance (X : LocallyRingedSpace) {U : TopCat} (f : U ⟶ X.toTopCat) (hf : IsOpenEmbedding f) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace hf

noncomputable section Pullback

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_toShHom]; rw [IsIso.hom_inv_id]
        erw [← LocallyRingedSpace.comp_toShHom]; rw [IsIso.inv_hom_id]; constructor <;> rfl⟩⟩

instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1

instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.toShHom by infer_instance)

instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullbackConeOfLeft : PullbackCone f g := by
  refine PullbackCone.mk ?_
      (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base)) ?_
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at this
    rw [← IsIso.eq_inv_comp] at this
    rw [this]
    dsimp
    infer_instance
  · exact LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition _ _)

instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

/-- The constructed `pullbackConeOfLeft` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.toShHom s.condition))) ?_,
      LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst f.1 g.1 _),
      LocallyRingedSpace.Hom.ext'
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 _), ?_⟩
    · intro x
      have :=
        PresheafedSpace.stalkMap.congr_hom _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
            (PullbackCone.mk s.fst.1 s.snd.1
              (congr_arg LocallyRingedSpace.Hom.toShHom s.condition)))
          x
      change _ = _ ≫ s.snd.1.stalkMap x at this
      rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_inv_comp] at this
      rw [this]
      infer_instance
    · intro m _ h₂
      rw [← cancel_mono (pullbackConeOfLeft f g).snd]
      exact h₂.trans <| LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 <|
          PullbackCone.mk s.fst.1 s.snd.1 <| congr_arg
            LocallyRingedSpace.Hom.toShHom s.condition).symm

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance

instance forget_preservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

instance forgetToPresheafedSpace_preservesPullback_of_left :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1

instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H

instance forgetToTop_preservesPullback_of_left :
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
    apply preservesLimit_of_iso_diagram _ (diagramIsoCospan _).symm
  apply Limits.comp_preservesLimit

instance forget_reflectsPullback_of_left :
    ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimit_of_reflectsIsomorphisms _ _

instance forget_preservesPullback_of_right :
    PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullback_symmetry _ _ _

instance forgetToPresheafedSpace_preservesPullback_of_right :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesPullback_symmetry _ _ _

instance forget_reflectsPullback_of_right :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimit_of_reflectsIsomorphisms _ _

instance forgetToPresheafedSpace_reflectsPullback_of_left :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimit_of_reflectsIsomorphisms _ _

instance forgetToPresheafedSpace_reflectsPullback_of_right :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimit_of_reflectsIsomorphisms _ _

theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd f g) := by
  apply (config := {allowSynthFailures := true}) Functor.ReflectsIsomorphisms.reflects
    (F := LocallyRingedSpace.forgetToSheafedSpace)
  apply (config := {allowSynthFailures := true}) Functor.ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace)
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) f g]
  -- Porting note: was `inferInstance`
  exact IsIso.comp_isIso' inferInstance <|
    PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ H'

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]
theorem lift_fac (H' : Set.range g.base ⊆ Set.range f.base) : lift f g H' ≫ f = g := by
  erw [Category.assoc]; rw [IsIso.inv_comp_eq]; exact pullback.condition

theorem lift_uniq (H' : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]

theorem lift_range (H' : Set.range g.base ⊆ Set.range f.base) :
    Set.range (lift f g H').base = f.base ⁻¹' Set.range g.base := by
  have := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst f g).base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_base, ← this, ← Category.assoc, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr, Set.image_univ]
  · rw [TopCat.pullback_fst_range]
    ext
    constructor
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
  · rw [← TopCat.epi_iff_surjective, show (inv (pullback.snd f g)).base = _ from
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
noncomputable def isoRestrict {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [H : LocallyRingedSpace.IsOpenImmersion f] :
    X ≅ Y.restrict H.base_open :=
  LocallyRingedSpace.isoOfSheafedSpaceIso <|
    SheafedSpace.forgetToPresheafedSpace.preimageIso <|
      PresheafedSpace.IsOpenImmersion.isoRestrict f.1

/-- The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev opensFunctor {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [H : LocallyRingedSpace.IsOpenImmersion f] : Opens X ⥤ Opens Y :=
  H.base_open.isOpenMap.functor

section OfStalkIso

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) (hf : IsOpenEmbedding f.base)
    [stalk_iso : ∀ x : X.1, IsIso (f.stalkMap x)] :
    LocallyRingedSpace.IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso _ hf (H := stalk_iso)

end OfStalkIso

section

variable {X Y : LocallyRingedSpace} (f : X ⟶ Y) [H : IsOpenImmersion f]

@[reassoc (attr := simp)]
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  ext1
  dsimp [isoRestrict, isoOfSheafedSpaceIso]
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  rw [Functor.map_comp, SheafedSpace.forgetToPresheafedSpace.map_preimage]
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.1

@[reassoc (attr := simp)]
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  simp only [← isoRestrict_hom_ofRestrict f, Iso.inv_hom_id_assoc]
/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  PresheafedSpace.IsOpenImmersion.invApp f.1 U

@[reassoc (attr := simp)]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality f.1 i

instance (U : Opens X) : IsIso (H.invApp _ U) := by delta invApp; infer_instance

theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫ X.presheaf.map
        (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.inv_invApp f.1 U

@[reassoc (attr := simp)]
theorem invApp_app (U : Opens X) :
    H.invApp _ U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.invApp_app f.1 U

attribute [elementwise nosimp] invApp_app

@[reassoc (attr := simp)]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom <|
            le_antisymm (Set.image_preimage_subset f.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

instance ofRestrict {X : TopCat} (Y : LocallyRingedSpace) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]
theorem ofRestrict_invApp (X : LocallyRingedSpace) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (LocallyRingedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ :=
  PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

instance stalk_iso (x : X) : IsIso (f.stalkMap x) :=
  PresheafedSpace.IsOpenImmersion.stalk_iso f.1 x

theorem to_iso [h' : Epi f.base] : IsIso f := by
  suffices IsIso (LocallyRingedSpace.forgetToSheafedSpace.map f) from
    isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace
  exact SheafedSpace.IsOpenImmersion.to_iso f.1

end

end LocallyRingedSpace.IsOpenImmersion

end AlgebraicGeometry

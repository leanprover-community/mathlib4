/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Restriction of Schemes and Morphisms

## Main definition
- `AlgebraicGeometry.Scheme.restrict`: The restriction of a scheme along an open embedding.
  The map `X.restrict f ⟶ X` is `AlgebraicGeometry.Scheme.ofRestrict`.
  `X ∣_ᵤ U` is the notation for restricting onto an open set, and `ιOpens U` is a shorthand
  for `X.restrict U.open_embedding : X ∣_ᵤ U ⟶ X`.
- `AlgebraicGeometry.morphism_restrict`: The restriction of `X ⟶ Y` to `X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U`.

-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

set_option linter.uppercaseLean3 false

noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section

variable (X : Scheme.{u})

/-- `f ⁻¹ᵁ U` is notation for `(Opens.map f.1.base).obj U`,
  the preimage of an open set `U` under `f`. -/
notation3:90 f:91 "⁻¹ᵁ " U:90 => (Opens.map (f : LocallyRingedSpace.Hom _ _).val.base).obj U

/-- `X ∣_ᵤ U` is notation for `X.restrict U.openEmbedding`, the restriction of `X` to an open set
  `U` of `X`. -/
notation3:60 X:60 " ∣_ᵤ " U:61 => Scheme.restrict X (U : Opens X).openEmbedding

/-- The restriction of a scheme to an open subset. -/
abbrev Scheme.ιOpens {X : Scheme.{u}} (U : Opens X.carrier) : X ∣_ᵤ U ⟶ X := X.ofRestrict _

lemma Scheme.ofRestrict_val_c_app_self {X : Scheme.{u}} (U : Opens X) :
    (X.ofRestrict U.openEmbedding).1.c.app (op U) = X.presheaf.map (eqToHom (by simp)).op := rfl

lemma Scheme.eq_restrict_presheaf_map_eqToHom {X : Scheme.{u}} (U : Opens X) {V W : Opens U}
    (e : U.openEmbedding.isOpenMap.functor.obj V = U.openEmbedding.isOpenMap.functor.obj W) :
  X.presheaf.map (eqToHom e).op =
    (X ∣_ᵤ U).presheaf.map (eqToHom <| U.openEmbedding.functor_obj_injective e).op := rfl

instance ΓRestrictAlgebra {X : Scheme.{u}} {Y : TopCat.{u}} {f : Y ⟶ X} (hf : OpenEmbedding f) :
    Algebra (Scheme.Γ.obj (op X)) (Scheme.Γ.obj (op <| X.restrict hf)) :=
  (Scheme.Γ.map (X.ofRestrict hf).op).toAlgebra
#align algebraic_geometry.Γ_restrict_algebra AlgebraicGeometry.ΓRestrictAlgebra

lemma Scheme.map_basicOpen' (X : Scheme.{u}) (U : Opens X) (r : Scheme.Γ.obj (op <| X ∣_ᵤ U)) :
    U.openEmbedding.isOpenMap.functor.obj ((X ∣_ᵤ U).basicOpen r) = X.basicOpen
    (X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op r) := by
  refine (Scheme.image_basicOpen (X.ofRestrict U.openEmbedding) r).trans ?_
  erw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.openEmbedding_obj_top).op]
  rw [← comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
    op_id, CategoryTheory.Functor.map_id]
  congr
  exact PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ _ _

lemma Scheme.map_basicOpen (X : Scheme.{u}) (U : Opens X) (r : Scheme.Γ.obj (op <| X ∣_ᵤ U)) :
    U.openEmbedding.isOpenMap.functor.obj ((X ∣_ᵤ U).basicOpen r) = X.basicOpen r := by
  rw [Scheme.map_basicOpen', Scheme.basicOpen_res_eq]

lemma Scheme.map_basicOpen_map (X : Scheme.{u}) (U : Opens X) (r : X.presheaf.obj (op U)) :
    U.openEmbedding.isOpenMap.functor.obj ((X ∣_ᵤ U).basicOpen <|
    X.presheaf.map (eqToHom U.openEmbedding_obj_top).op r) = X.basicOpen r := by
  rw [Scheme.map_basicOpen', Scheme.basicOpen_res_eq, Scheme.basicOpen_res_eq]


-- Porting note: `simps` can't synthesize `obj_left, obj_hom, mapLeft`
/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
-- @[simps obj_left obj_hom mapLeft]
def Scheme.restrictFunctor : Opens X ⥤ Over X where
  obj U := Over.mk (ιOpens U)
  map {U V} i :=
    Over.homMk
      (IsOpenImmersion.lift (ιOpens V) (ιOpens U) <| by
          dsimp [restrict, ofRestrict, LocallyRingedSpace.ofRestrict, Opens.coe_inclusion]
          rw [Subtype.range_val, Subtype.range_val]
          exact i.le)
      (IsOpenImmersion.lift_fac _ _ _)
  map_id U := by
    ext1
    dsimp only [Over.homMk_left, Over.id_left]
    rw [← cancel_mono (ιOpens U), Category.id_comp,
      IsOpenImmersion.lift_fac]
  map_comp {U V W} i j := by
    ext1
    dsimp only [Over.homMk_left, Over.comp_left]
    rw [← cancel_mono (ιOpens W), Category.assoc]
    iterate 3 rw [IsOpenImmersion.lift_fac]
#align algebraic_geometry.Scheme.restrict_functor AlgebraicGeometry.Scheme.restrictFunctor

@[simp] lemma Scheme.restrictFunctor_obj_left (U : Opens X) :
  (X.restrictFunctor.obj U).left = X ∣_ᵤ U := rfl

@[simp] lemma Scheme.restrictFunctor_obj_hom (U : Opens X) :
  (X.restrictFunctor.obj U).hom = Scheme.ιOpens U := rfl

@[simp] lemma Scheme.restrictFunctor_map_left {U V : Opens X} (i : U ⟶ V) :
  (X.restrictFunctor.map i).left = IsOpenImmersion.lift (ιOpens V) (ιOpens U) (by
    dsimp [ofRestrict, LocallyRingedSpace.ofRestrict, Opens.inclusion]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk]; rw [Subtype.range_val, Subtype.range_val]
    exact i.le) := rfl

-- Porting note: the `by ...` used to be automatically done by unification magic
@[reassoc]
theorem Scheme.restrictFunctor_map_ofRestrict {U V : Opens X} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1 ≫ ιOpens V = ιOpens U :=
  IsOpenImmersion.lift_fac _ _ (by
    dsimp [restrict, ofRestrict, LocallyRingedSpace.ofRestrict]
    rw [Subtype.range_val, Subtype.range_val]
    exact i.le)
#align algebraic_geometry.Scheme.restrict_functor_map_ofRestrict AlgebraicGeometry.Scheme.restrictFunctor_map_ofRestrict

theorem Scheme.restrictFunctor_map_base {U V : Opens X} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1.1.base = (Opens.toTopCat _).map i := by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact (congr_arg (fun f : X.restrict U.openEmbedding ⟶ X => f.1.base a)
        (X.restrictFunctor_map_ofRestrict i))
#align algebraic_geometry.Scheme.restrict_functor_map_base AlgebraicGeometry.Scheme.restrictFunctor_map_base

theorem Scheme.restrictFunctor_map_app_aux {U V : Opens X} (i : U ⟶ V) (W : Opens V) :
    U.openEmbedding.isOpenMap.functor.obj ((X.restrictFunctor.map i).1 ⁻¹ᵁ W) ≤
      V.openEmbedding.isOpenMap.functor.obj W := by
  simp only [← SetLike.coe_subset_coe, IsOpenMap.functor_obj_coe, Set.image_subset_iff,
    Scheme.restrictFunctor_map_base, Opens.map_coe, Opens.inclusion_apply]
  rintro _ h
  exact ⟨_, h, rfl⟩
#align algebraic_geometry.Scheme.restrict_functor_map_app_aux AlgebraicGeometry.Scheme.restrictFunctor_map_app_aux

theorem Scheme.restrictFunctor_map_app {U V : Opens X} (i : U ⟶ V) (W : Opens V) :
    (X.restrictFunctor.map i).1.1.c.app (op W) =
      X.presheaf.map (homOfLE <| X.restrictFunctor_map_app_aux i W).op := by
  have e₁ :=
    Scheme.congr_app (X.restrictFunctor_map_ofRestrict i)
      (op <| V.openEmbedding.isOpenMap.functor.obj W)
  rw [Scheme.comp_val_c_app] at e₁
  -- Porting note: `Opens.map_functor_eq` need more help
  have e₂ := (X.restrictFunctor.map i).1.val.c.naturality (eqToHom <| W.map_functor_eq (U := V)).op
  rw [← IsIso.eq_inv_comp] at e₂
  dsimp [restrict] at e₁ e₂ ⊢
  rw [e₂, W.adjunction_counit_map_functor (U := V), ← IsIso.eq_inv_comp, IsIso.inv_comp_eq,
    ← IsIso.eq_comp_inv] at e₁
  simp_rw [eqToHom_map (Opens.map _), eqToHom_map (IsOpenMap.functor _), ← Functor.map_inv,
    ← Functor.map_comp] at e₁
  rw [e₁]
  congr 1
#align algebraic_geometry.Scheme.restrict_functor_map_app AlgebraicGeometry.Scheme.restrictFunctor_map_app

/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps!]
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).openEmbedding_obj_top).symm.op : _))
    (by
      intro U V i
      dsimp [-Scheme.restrictFunctor_map_left]
      rw [X.restrictFunctor_map_app, ← Functor.map_comp, ← Functor.map_comp]
      congr 1)
#align algebraic_geometry.Scheme.restrict_functor_Γ AlgebraicGeometry.Scheme.restrictFunctorΓ

/-- `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V ∣_ U` -/
noncomputable
def Scheme.restrictRestrictComm (X : Scheme.{u}) (U V : Opens X.carrier) :
    X ∣_ᵤ U ∣_ᵤ ιOpens U ⁻¹ᵁ V ≅ X ∣_ᵤ V ∣_ᵤ ιOpens V ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (ιOpens _ ≫ ιOpens U) (ιOpens _ ≫ ιOpens V) ?_
  simp only [Scheme.restrict_carrier, Scheme.ofRestrict_val_base, Scheme.comp_coeBase,
    TopCat.coe_comp, Opens.coe_inclusion, Set.range_comp, Opens.map]
  rw [Subtype.range_val, Subtype.range_val]
  dsimp
  rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range,
    Subtype.range_val, Subtype.range_val, Set.inter_comm]

/-- If `V` is an open subset of `U`, then `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V`. -/
noncomputable
def Scheme.restrictRestrict (X : Scheme.{u}) (U : Opens X.carrier) (V : Opens (X ∣_ᵤ U).carrier) :
    X ∣_ᵤ U ∣_ᵤ V ≅ X ∣_ᵤ U.openEmbedding.isOpenMap.functor.obj V := by
  refine IsOpenImmersion.isoOfRangeEq (ιOpens _ ≫ ιOpens U) (ιOpens _) ?_
  simp only [Scheme.restrict_carrier, Scheme.ofRestrict_val_base, Scheme.comp_coeBase,
    TopCat.coe_comp, Opens.coe_inclusion, Set.range_comp, Opens.map]
  rw [Subtype.range_val, Subtype.range_val]
  rfl

@[simp, reassoc]
lemma Scheme.restrictRestrict_hom_restrict (X : Scheme.{u}) (U : Opens X.carrier)
    (V : Opens (X ∣_ᵤ U).carrier) :
    (X.restrictRestrict U V).hom ≫ ιOpens _ = ιOpens V ≫ ιOpens U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[simp, reassoc]
lemma Scheme.restrictRestrict_inv_restrict_restrict (X : Scheme.{u}) (U : Opens X.carrier)
    (V : Opens (X ∣_ᵤ U).carrier) :
    (X.restrictRestrict U V).inv ≫ ιOpens V ≫ ιOpens U = ιOpens _ :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- If `U = V`, then `X ∣_ U` is isomorphic to `X ∣_ V`. -/
noncomputable
def Scheme.restrictIsoOfEq (X : Scheme.{u}) {U V : Opens X.carrier} (e : U = V) :
    X ∣_ᵤ U ≅ X ∣_ᵤ V := by
  exact IsOpenImmersion.isoOfRangeEq (ιOpens U) (ιOpens V) (by rw [e])

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev Scheme.restrictMapIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : Opens Y) : X ∣_ᵤ f ⁻¹ᵁ U ≅ Y ∣_ᵤ U := by
  apply IsOpenImmersion.isoOfRangeEq (f := X.ofRestrict _ ≫ f)
    (H := PresheafedSpace.IsOpenImmersion.comp (hf := inferInstance) (hg := inferInstance))
    (Y.ofRestrict _) _
  dsimp [restrict]
  rw [Set.range_comp, Subtype.range_val, Subtype.range_coe]
  refine @Set.image_preimage_eq _ _ f.1.base U.1 ?_
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.Scheme.restrict_map_iso AlgebraicGeometry.Scheme.restrictMapIso

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    pullback f (Scheme.ιOpens U) ≅ X ∣_ᵤ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq pullback.fst (X.ofRestrict _) ?_
  rw [IsOpenImmersion.range_pullback_fst_of_right]
  dsimp [Opens.coe_inclusion, Scheme.restrict]
  rw [Subtype.range_val, Subtype.range_coe]
  rfl
#align algebraic_geometry.pullback_restrict_iso_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst = X.ofRestrict _ := by
  delta pullbackRestrictIsoRestrict; simp
#align algebraic_geometry.pullback_restrict_iso_restrict_inv_fst AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    (pullbackRestrictIsoRestrict f U).hom ≫ Scheme.ιOpens (f ⁻¹ᵁ U) = pullback.fst := by
  delta pullbackRestrictIsoRestrict; simp
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_restrict

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) : X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd
#align algebraic_geometry.morphism_restrict AlgebraicGeometry.morphismRestrict

/-- the notation for restricting a morphism of scheme to an open subset of the target scheme -/
infixl:85 " ∣_ " => morphismRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Opens Y) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd :=
  Iso.hom_inv_id_assoc _ _
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_morphism_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict

@[simp, reassoc]
theorem morphismRestrict_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    (f ∣_ U) ≫ Scheme.ιOpens U = Scheme.ιOpens (f ⁻¹ᵁ U) ≫ f := by
  delta morphismRestrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_ι AlgebraicGeometry.morphismRestrict_ι

theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    IsPullback (f ∣_ U) (Scheme.ιOpens (f ⁻¹ᵁ U)) (Scheme.ιOpens U) f := by
  delta morphismRestrict
  rw [← Category.id_comp f]
  refine
    (IsPullback.of_horiz_isIso ⟨?_⟩).paste_horiz
      (IsPullback.of_hasPullback f (Y.ofRestrict U.openEmbedding)).flip
  -- Porting note: changed `rw` to `erw`
  erw [pullbackRestrictIsoRestrict_inv_fst]; rw [Category.comp_id]
#align algebraic_geometry.is_pullback_morphism_restrict AlgebraicGeometry.isPullback_morphismRestrict

theorem morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U := by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono pullback.fst]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst, ←
    pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_comp AlgebraicGeometry.morphismRestrict_comp

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Opens Y) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

theorem morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) (x) :
    @Coe.coe U Y (⟨fun x => x.1⟩) ((f ∣_ U).1.base x) = f.1.base x.1 :=
  congr_arg (fun f => PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.val f) x)
    (morphismRestrict_ι f U)
#align algebraic_geometry.morphism_restrict_base_coe AlgebraicGeometry.morphismRestrict_base_coe

theorem morphismRestrict_val_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    ⇑(f ∣_ U).1.base = U.1.restrictPreimage f.1.base :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)
#align algebraic_geometry.morphism_restrict_val_base AlgebraicGeometry.morphismRestrict_val_base

theorem image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) (V : Opens U) :
    (f ⁻¹ᵁ U).openEmbedding.isOpenMap.functor.obj ((f ∣_ U) ⁻¹ᵁ V) =
      f ⁻¹ᵁ (U.openEmbedding.isOpenMap.functor.obj V) := by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).1.base _ ∈ V, rfl⟩
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    -- Porting note: this rewrite was not necessary
    rw [SetLike.mem_coe]
    convert hx'
    -- Porting note: `ext1` is not compiling
    refine Subtype.ext ?_
    exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx' : _ ∈ V.1, rfl : x = _⟩
    refine ⟨⟨_, hx⟩, (?_ : (f ∣_ U).1.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    -- Porting note: `ext1` is compiling
    refine Subtype.ext ?_
    exact morphismRestrict_base_coe f U ⟨x, hx⟩
#align algebraic_geometry.image_morphism_restrict_preimage AlgebraicGeometry.image_morphismRestrict_preimage

theorem morphismRestrict_c_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) (V : Opens U) :
    (f ∣_ U).1.c.app (op V) =
      f.1.c.app (op (U.openEmbedding.isOpenMap.functor.obj V)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  have :=
    Scheme.congr_app (morphismRestrict_ι f U) (op (U.openEmbedding.isOpenMap.functor.obj V))
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this
  have e : (Opens.map U.inclusion).obj (U.openEmbedding.isOpenMap.functor.obj V) = V := by
    ext1; exact Set.preimage_image_eq _ Subtype.coe_injective
  have : _ ≫ X.presheaf.map _ = _ :=
    (((f ∣_ U).1.c.naturality (eqToHom e).op).symm.trans ?_).trans this
  · rw [← IsIso.eq_comp_inv, ← Functor.map_inv, Category.assoc] at this
    rw [this]
    congr 1
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    congr 1
  · change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _
    congr 1
#align algebraic_geometry.morphism_restrict_c_app AlgebraicGeometry.morphismRestrict_c_app

theorem Γ_map_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.presheaf.map (eqToHom <| U.openEmbedding_obj_top.symm).op ≫
        f.1.c.app (op U) ≫ X.presheaf.map (eqToHom <| (f ⁻¹ᵁ U).openEmbedding_obj_top).op := by
  rw [Scheme.Γ_map_op, morphismRestrict_c_app f U ⊤, f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.Γ_map_morphism_restrict AlgebraicGeometry.Γ_map_morphismRestrict

/-- Restricting a morphism onto the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange
    {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ Scheme.Hom.opensRange g) ≅ Arrow.mk (pullback.snd : pullback f g ⟶ _) := by
  let V : Opens Y := Scheme.Hom.opensRange g
  let e :=
    IsOpenImmersion.isoOfRangeEq g (Y.ofRestrict V.openEmbedding) Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f (Y.ofRestrict V.openEmbedding) :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom_fac])
  symm
  refine Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e ?_
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g, Arrow.mk_hom, Arrow.mk_hom,
    Category.assoc, Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac,
    ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_restrict_assoc, pullback.lift_fst_assoc, Category.comp_id]
#align algebraic_geometry.morphism_restrict_opens_range AlgebraicGeometry.morphismRestrictOpensRange

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Opens Y} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)
#align algebraic_geometry.morphism_restrict_eq AlgebraicGeometry.morphismRestrictEq

/-- Restricting a morphism twice is isomorphic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) (V : Opens (Y ∣_ᵤ U)) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.openEmbedding.isOpenMap.functor.obj V) := by
  refine Arrow.isoMk' _ _ (Scheme.restrictRestrict _ _ _ ≪≫ Scheme.restrictIsoOfEq _ ?_)
    (Scheme.restrictRestrict _ _ _) ?_
  · ext x
    simp only [IsOpenMap.functor_obj_coe, Opens.coe_inclusion,
      Opens.map_coe, Set.mem_image, Set.mem_preimage, SetLike.mem_coe, morphismRestrict_val_base]
    constructor
    · rintro ⟨⟨a, h₁⟩, h₂, rfl⟩
      exact ⟨_, h₂, rfl⟩
    · rintro ⟨⟨a, h₁⟩, h₂, rfl : a = _⟩
      exact ⟨⟨x, h₁⟩, h₂, rfl⟩
  · rw [← cancel_mono (Scheme.ιOpens _), Iso.trans_hom, Category.assoc, Category.assoc,
      Category.assoc, morphismRestrict_ι, Scheme.restrictIsoOfEq,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
      Scheme.restrictRestrict_hom_restrict_assoc,
      Scheme.restrictRestrict_hom_restrict,
      morphismRestrict_ι_assoc, morphismRestrict_ι]
#align algebraic_geometry.morphism_restrict_restrict AlgebraicGeometry.morphismRestrictRestrict

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction.  -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y)
    (r : Y.presheaf.obj (op U)) :
    Arrow.mk
        (f ∣_ U ∣_
          (Y ∣_ᵤ U).basicOpen (Y.presheaf.map (eqToHom U.openEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  have e := Scheme.preimage_basicOpen (Y.ofRestrict U.openEmbedding) r
  erw [Scheme.ofRestrict_val_c_app, Opens.adjunction_counit_app_self, eqToHom_op] at e
  rw [← (Y.restrict U.openEmbedding).basicOpen_res_eq _ (eqToHom U.inclusion_map_eq_top).op]
  erw [← comp_apply]
  erw [← Y.presheaf.map_comp]
  rw [eqToHom_op, eqToHom_op, eqToHom_map, eqToHom_trans]
  erw [← e]
  ext1
  dsimp [Opens.map_coe, Scheme.restrict]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left, Subtype.range_val]
  exact Y.basicOpen_le r
#align algebraic_geometry.morphism_restrict_restrict_basic_open AlgebraicGeometry.morphismRestrictRestrictBasicOpen

/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) (x) :
    Arrow.mk (PresheafedSpace.stalkMap (f ∣_ U).1 x) ≅
      Arrow.mk (PresheafedSpace.stalkMap f.1 x.1) := by
  fapply Arrow.isoMk'
  · refine Y.restrictStalkIso U.openEmbedding ((f ∣_ U).1.1 x) ≪≫ TopCat.Presheaf.stalkCongr _ ?_
    apply Inseparable.of_eq
    exact morphismRestrict_base_coe f U x
  · exact X.restrictStalkIso (Opens.openEmbedding _) _
  · apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    change ↑(f ⁻¹ᵁ U) at x
    simp only [Scheme.restrict_presheaf_obj, unop_op, Opens.coe_inclusion, Iso.trans_hom,
      TopCat.Presheaf.stalkCongr_hom, Category.assoc, Scheme.restrict_toPresheafedSpace]
    rw [PresheafedSpace.restrictStalkIso_hom_eq_germ_assoc,
      TopCat.Presheaf.germ_stalkSpecializes'_assoc,
      PresheafedSpace.stalkMap_germ'_assoc, PresheafedSpace.stalkMap_germ', morphismRestrict_c_app,
      PresheafedSpace.restrictStalkIso_hom_eq_germ, Category.assoc, TopCat.Presheaf.germ_res]
    rfl

#align algebraic_geometry.morphism_restrict_stalk_map AlgebraicGeometry.morphismRestrictStalkMap

instance {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphismRestrict
  exact PresheafedSpace.IsOpenImmersion.comp _ _

end MorphismRestrict

end AlgebraicGeometry

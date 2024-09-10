/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Restriction of Schemes and Morphisms

## Main definition
- `AlgebraicGeometry.Scheme.restrict`: The restriction of a scheme along an open embedding.
  The map `X.restrict f ⟶ X` is `AlgebraicGeometry.Scheme.ofRestrict`.
  `U : X.Opens` has a coercion to `Scheme` and `U.ι` is a shorthand
  for `X.restrict U.open_embedding : U ⟶ X`.
- `AlgebraicGeometry.morphism_restrict`: The restriction of `X ⟶ Y` to `X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U`.

-/

-- Explicit universe annotations were used in this file to improve performance #12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section

variable {X : Scheme.{u}} (U : X.Opens)

namespace Scheme.Opens

/-- Open subset of a scheme as a scheme. -/
@[coe]
def toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} :=
  X.restrict U.openEmbedding

instance : CoeOut X.Opens Scheme := ⟨toScheme⟩

/-- The restriction of a scheme to an open subset. -/
@[simps! val_base_apply]
def ι : ↑U ⟶ X := X.ofRestrict _

instance : IsOpenImmersion U.ι := inferInstanceAs (IsOpenImmersion (X.ofRestrict _))

lemma toScheme_carrier : (U : Type u) = (U : Set X) := rfl

lemma toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ''ᵁ V) := rfl

@[simp]
lemma toScheme_presheaf_map {V W} (i : V ⟶ W) :
    U.toScheme.presheaf.map i = X.presheaf.map (U.ι.opensFunctor.map i.unop).op := rfl

@[simp]
lemma ι_app (V) : U.ι.app V = X.presheaf.map
    (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ V) (Set.image_preimage_subset _ _)).op :=
  rfl

@[simp]
lemma ι_appLE (V W e) :
    U.ι.appLE V W e =
      X.presheaf.map (homOfLE (x := U.ι ''ᵁ W) (Set.image_subset_iff.mpr ‹_›)).op := by
  simp only [Hom.appLE, ι_app, Functor.op_obj, Opens.carrier_eq_coe, toScheme_presheaf_map,
    Quiver.Hom.unop_op, Hom.opensFunctor_map_homOfLE, Opens.coe_inclusion, ← Functor.map_comp]
  rfl

@[simp]
lemma ι_appIso (V) : U.ι.appIso V = Iso.refl _ :=
  X.ofRestrict_appIso _ _

@[simp]
lemma opensRange_ι : U.ι.opensRange = U :=
  Opens.ext Subtype.range_val

@[simp]
lemma range_ι : Set.range U.ι.val.base = U :=
  Subtype.range_val

lemma ι_image_top : U.ι ''ᵁ ⊤ = U :=
  U.openEmbedding_obj_top

@[simp]
lemma ι_preimage_self : U.ι ⁻¹ᵁ U = ⊤ :=
  Opens.inclusion_map_eq_top _

instance ι_appLE_isIso :
    IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  simp only [ι, ofRestrict_appLE]
  show IsIso (X.presheaf.map (eqToIso U.ι_image_top).hom.op)
  infer_instance

lemma ι_app_self : U.ι.app U = X.presheaf.map (eqToHom (X := U.ι ''ᵁ _) (by simp)).op := rfl

lemma eq_presheaf_map_eqToHom {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W) :
    X.presheaf.map (eqToHom e).op =
      U.toScheme.presheaf.map (eqToHom <| U.openEmbedding.functor_obj_injective e).op := rfl

@[simp]
lemma nonempty_iff : Nonempty U.toScheme ↔ (U : Set X).Nonempty := by
  simp only [toScheme_carrier, SetLike.coe_sort_coe, nonempty_subtype]
  rfl

attribute [-simp] eqToHom_op in
/-- The global sections of the restriction is isomorphic to the sections on the open set. -/
@[simps!]
def topIso : Γ(U, ⊤) ≅ Γ(X, U) :=
  X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- The stalks of an open subscheme are isomorphic to the stalks of the original scheme. -/
def stalkIso {X : Scheme.{u}} (U : X.Opens) (x : U) :
    U.toScheme.presheaf.stalk x ≅ X.presheaf.stalk x.1 :=
  X.restrictStalkIso (Opens.openEmbedding _) _

@[reassoc (attr := simp)]
lemma germ_stalkIso_hom {X : Scheme.{u}} (U : X.Opens)
    {V : U.toScheme.Opens} (x : V) :
      U.toScheme.presheaf.germ x ≫ (U.stalkIso x.1).hom =
        X.presheaf.germ ⟨x.1.1, show x.1.1 ∈ U.ι ''ᵁ V from ⟨x.1, x.2, rfl⟩⟩ :=
    PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.openEmbedding _ _ _

@[reassoc (attr := simp)]
lemma germ_stalkIso_hom' {X : Scheme.{u}} (U : X.Opens)
    {V : TopologicalSpace.Opens U} (x : U) (hx : x ∈ V) :
      U.toScheme.presheaf.germ ⟨x, hx⟩ ≫ (U.stalkIso x).hom =
        X.presheaf.germ ⟨x.1, show x.1 ∈ U.ι ''ᵁ V from ⟨x, hx, rfl⟩⟩ :=
    PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.openEmbedding _ _ _

@[simp, reassoc]
lemma germ_stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x : U)
    (hx : x ∈ V) : X.presheaf.germ ⟨x.val, show x.val ∈ U.ι ''ᵁ V from ⟨x, hx, rfl⟩⟩ ≫
      (U.stalkIso x).inv = U.toScheme.presheaf.germ ⟨x, hx⟩ :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace U.openEmbedding V x hx

end Scheme.Opens

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! J obj map]
def Scheme.openCoverOfISupEqTop {s : Type*} (X : Scheme.{u}) (U : s → X.Opens)
    (hU : ⨆ i, U i = ⊤) : X.OpenCover where
  J := s
  obj i := U i
  map i := (U i).ι
  f x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : X.Opens) by trivial
    (Opens.mem_iSup.mp this).choose
  covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : X.Opens) by trivial
    exact (Opens.mem_iSup.mp this).choose_spec

@[deprecated (since := "2024-07-24")]
noncomputable alias Scheme.openCoverOfSuprEqTop := Scheme.openCoverOfISupEqTop

/-- The open sets of an open subscheme corresponds to the open sets containing in the subset. -/
@[simps!]
def opensRestrict :
    Scheme.Opens U ≃ { V : X.Opens // V ≤ U } :=
  (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))

instance ΓRestrictAlgebra {X : Scheme.{u}} (U : X.Opens) :
    Algebra (Γ(X, ⊤)) Γ(U, ⊤) :=
  (U.ι.app ⊤).toAlgebra

lemma Scheme.map_basicOpen' (r : Γ(U, ⊤)) :
    U.ι ''ᵁ (U.toScheme.basicOpen r) = X.basicOpen
      (X.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op r) := by
  refine (Scheme.image_basicOpen (X.ofRestrict U.openEmbedding) r).trans ?_
  erw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.openEmbedding_obj_top).op]
  rw [← comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
    op_id, CategoryTheory.Functor.map_id]
  congr
  exact PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ _ _

lemma Scheme.Opens.ι_image_basicOpen (r : Γ(U, ⊤)) :
    U.ι ''ᵁ (U.toScheme.basicOpen r) = X.basicOpen r := by
  rw [Scheme.map_basicOpen', Scheme.basicOpen_res_eq]

lemma Scheme.map_basicOpen_map (r : Γ(X, U)) :
    U.ι ''ᵁ (U.toScheme.basicOpen <| U.topIso.inv r) = X.basicOpen r := by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [Scheme.map_basicOpen', Scheme.basicOpen_res_eq, Scheme.Opens.topIso_inv,
    Scheme.basicOpen_res_eq X]

-- Porting note: `simps` can't synthesize `obj_left, obj_hom, mapLeft`
variable (X) in
/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
-- @[simps obj_left obj_hom mapLeft]
def Scheme.restrictFunctor : X.Opens ⥤ Over X where
  obj U := Over.mk U.ι
  map {U V} i :=
    Over.homMk
      (IsOpenImmersion.lift V.ι U.ι <| by simpa using i.le)
      (IsOpenImmersion.lift_fac _ _ _)
  map_id U := by
    ext1
    dsimp only [Over.homMk_left, Over.id_left]
    rw [← cancel_mono U.ι, Category.id_comp,
      IsOpenImmersion.lift_fac]
  map_comp {U V W} i j := by
    ext1
    dsimp only [Over.homMk_left, Over.comp_left]
    rw [← cancel_mono W.ι, Category.assoc]
    iterate 3 rw [IsOpenImmersion.lift_fac]

@[simp] lemma Scheme.restrictFunctor_obj_left (U : X.Opens) :
  (X.restrictFunctor.obj U).left = U := rfl

@[simp] lemma Scheme.restrictFunctor_obj_hom (U : X.Opens) :
  (X.restrictFunctor.obj U).hom = U.ι := rfl

@[simp] lemma Scheme.restrictFunctor_map_left {U V : X.Opens} (i : U ⟶ V) :
  (X.restrictFunctor.map i).left = IsOpenImmersion.lift (V.ι) U.ι (by simpa using i.le) := rfl

-- Porting note: the `by ...` used to be automatically done by unification magic
@[reassoc]
theorem Scheme.restrictFunctor_map_ofRestrict {U V : X.Opens} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1 ≫ V.ι = U.ι :=
  IsOpenImmersion.lift_fac _ _ (by simpa using i.le)

theorem Scheme.restrictFunctor_map_base {U V : X.Opens} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1.val.base = (Opens.toTopCat _).map i := by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact (congr_arg (fun f : X.restrict U.openEmbedding ⟶ X => f.val.base a)
        (X.restrictFunctor_map_ofRestrict i))

theorem Scheme.restrictFunctor_map_app_aux {U V : X.Opens} (i : U ⟶ V) (W : Opens V) :
    U.ι ''ᵁ ((X.restrictFunctor.map i).1 ⁻¹ᵁ W) ≤ V.ι ''ᵁ W := by
  simp only [← SetLike.coe_subset_coe, IsOpenMap.functor_obj_coe, Set.image_subset_iff,
    Scheme.restrictFunctor_map_base, Opens.map_coe, Opens.inclusion_apply]
  rintro _ h
  exact ⟨_, h, rfl⟩

theorem Scheme.restrictFunctor_map_app {U V : X.Opens} (i : U ⟶ V) (W : Opens V) :
    (X.restrictFunctor.map i).1.app W =
      X.presheaf.map (homOfLE <| X.restrictFunctor_map_app_aux i W).op := by
  have e₁ := Scheme.congr_app (X.restrictFunctor_map_ofRestrict i) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.restrictFunctor.map i).1.naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv, ← Functor.map_inv, ← Functor.map_comp] at e₃
  rw [e₃, ← Functor.map_comp]
  congr 1

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

/-- `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V ∣_ U` -/
noncomputable
def Scheme.restrictRestrictComm (X : Scheme.{u}) (U V : X.Opens) :
    (U.ι ⁻¹ᵁ V).toScheme ≅ V.ι ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _ ≫ V.ι) <| by
    simp [Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X), Set.range_comp]

/-- If `V` is an open subset of `U`, then `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V`. -/
noncomputable
def Scheme.restrictRestrict (X : Scheme.{u}) (U : X.Opens) (V : U.toScheme.Opens) :
    V.toScheme ≅ U.ι ''ᵁ V :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _) (by simp [Set.range_comp])

@[simp, reassoc]
lemma Scheme.restrictRestrict_hom_restrict (X : Scheme.{u}) (U : X.Opens)
    (V : U.toScheme.Opens) :
    (X.restrictRestrict U V).hom ≫ Opens.ι _ = V.ι ≫ U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[simp, reassoc]
lemma Scheme.restrictRestrict_inv_restrict_restrict (X : Scheme.{u}) (U : X.Opens)
    (V : U.toScheme.Opens) :
    (X.restrictRestrict U V).inv ≫ V.ι ≫ U.ι = Opens.ι _ :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- If `U = V`, then `X ∣_ U` is isomorphic to `X ∣_ V`. -/
noncomputable
def Scheme.restrictIsoOfEq (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (U : Scheme.{u}) ≅ V :=
  IsOpenImmersion.isoOfRangeEq U.ι (V.ι) (by rw [e])

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev Scheme.restrictMapIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ U := by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp, Opens.range_ι, Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f.val.base U.1 f.homeomorph.surjective

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f (U.ι) ≅ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullback_fst_of_right]

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst f _ = (f ⁻¹ᵁ U).ι := by
  delta pullbackRestrictIsoRestrict; simp

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι = pullback.fst f _ := by
  delta pullbackRestrictIsoRestrict; simp

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ⟶ U :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

/-- the notation for restricting a morphism of scheme to an open subset of the target scheme -/
infixl:85 " ∣_ " => morphismRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd _ _ :=
  Iso.hom_inv_id_assoc _ _

@[simp, reassoc]
theorem morphismRestrict_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  delta morphismRestrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := by
  delta morphismRestrict
  rw [← Category.id_comp f]
  refine
    (IsPullback.of_horiz_isIso ⟨?_⟩).paste_horiz
      (IsPullback.of_hasPullback f (Y.ofRestrict U.openEmbedding)).flip
  -- Porting note: changed `rw` to `erw`
  erw [pullbackRestrictIsoRestrict_inv_fst]; rw [Category.comp_id]

@[simp]
lemma morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _ := by
  rw [← cancel_mono U.ι, morphismRestrict_ι, Category.comp_id, Category.id_comp]
  rfl

theorem morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U := by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (pullback.fst _ _)]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst, ←
    pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

theorem morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    @Coe.coe U Y (⟨fun x => x.1⟩) ((f ∣_ U).val.base x) = f.val.base x.1 :=
  congr_arg (fun f => PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.val f) x)
    (morphismRestrict_ι f U)

theorem morphismRestrict_val_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    ⇑(f ∣_ U).val.base = U.1.restrictPreimage f.val.base :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)

theorem image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι ''ᵁ V) := by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).val.base _ ∈ V, rfl⟩
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    -- Porting note: this rewrite was not necessary
    rw [SetLike.mem_coe]
    convert hx'
    -- Porting note: `ext1` is not compiling
    refine Subtype.ext ?_
    exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx' : _ ∈ V.1, rfl : x = _⟩
    refine ⟨⟨_, hx⟩, (?_ : (f ∣_ U).val.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    -- Porting note: `ext1` is compiling
    refine Subtype.ext ?_
    exact morphismRestrict_base_coe f U ⟨x, hx⟩

lemma eqToHom_eq_homOfLE {C} [Preorder C] {X Y : C} (e : X = Y) : eqToHom e = homOfLE e.le := rfl

open Scheme in
theorem morphismRestrict_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    (f ∣_ U).app V = f.app (U.ι ''ᵁ V) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  have := Scheme.congr_app (morphismRestrict_ι f U) (U.ι ''ᵁ V)
  simp only [Scheme.preimage_comp, Opens.toScheme_presheaf_obj, Hom.app_eq_appLE, comp_appLE,
    Opens.ι_appLE, eqToHom_op, Opens.toScheme_presheaf_map, eqToHom_unop] at this
  have e : U.ι ⁻¹ᵁ (U.ι ''ᵁ V) = V :=
    Opens.ext (Set.preimage_image_eq _ Subtype.coe_injective)
  have e' : (f ∣_ U) ⁻¹ᵁ V = (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U.ι ''ᵁ V := by rw [e]
  simp only [Opens.toScheme_presheaf_obj, Hom.app_eq_appLE, eqToHom_op, Hom.appLE_map]
  rw [← (f ∣_ U).appLE_map' _ e', ← (f ∣_ U).map_appLE' _ e]
  simp only [Opens.toScheme_presheaf_obj, eqToHom_eq_homOfLE, Opens.toScheme_presheaf_map,
    Quiver.Hom.unop_op, Hom.opensFunctor_map_homOfLE]
  rw [this, Hom.appLE_map, Hom.appLE_map, Hom.appLE_map]

@[simp]
theorem morphismRestrict_app' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ∣_ U).app V = f.appLE _ _ (image_morphismRestrict_preimage f U V).le :=
  morphismRestrict_app f U V

@[simp]
theorem morphismRestrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e) :
    (f ∣_ U).appLE V W e = f.appLE (U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W)
      ((Set.image_subset _ e).trans (image_morphismRestrict_preimage f U V).le) := by
  rw [Scheme.Hom.appLE, morphismRestrict_app', Scheme.Opens.toScheme_presheaf_map,
    Scheme.Hom.appLE_map]

theorem Γ_map_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.presheaf.map (eqToHom U.openEmbedding_obj_top.symm).op ≫
        f.app U ≫ X.presheaf.map (eqToHom (f ⁻¹ᵁ U).openEmbedding_obj_top).op := by
  rw [Scheme.Γ_map_op, morphismRestrict_app f U ⊤, f.naturality_assoc, ← X.presheaf.map_comp]
  rfl

/-- Restricting a morphism onto the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange
    {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g) := by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom_fac])
  symm
  refine Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e ?_
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g, Arrow.mk_hom, Arrow.mk_hom,
    Category.assoc, Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac,
    ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_restrict_assoc, pullback.lift_fst_assoc, Category.comp_id]

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)

/-- Restricting a morphism twice is isomorphic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ''ᵁ V) := by
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
  · rw [← cancel_mono (Scheme.Opens.ι _), Iso.trans_hom, Category.assoc, Category.assoc,
      Category.assoc, morphismRestrict_ι, Scheme.restrictIsoOfEq,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
      Scheme.restrictRestrict_hom_restrict_assoc,
      Scheme.restrictRestrict_hom_restrict,
      morphismRestrict_ι_assoc, morphismRestrict_ι]

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction. -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    Arrow.mk (f ∣_ U ∣_
          U.toScheme.basicOpen (Y.presheaf.map (eqToHom U.openEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  have e := Scheme.preimage_basicOpen U.ι r
  rw [Scheme.Opens.ι_app] at e
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom U.inclusion_map_eq_top).op]
  erw [← comp_apply]
  erw [← Y.presheaf.map_comp]
  rw [eqToHom_op, eqToHom_op, eqToHom_map, eqToHom_trans]
  erw [← e]
  ext1
  dsimp [Opens.map_coe]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left, Scheme.Opens.range_ι]
  exact Y.basicOpen_le r

/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) := Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U).1.base x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
  ((f ⁻¹ᵁ U).stalkIso x) <| by
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    change ↑(f ⁻¹ᵁ U) at x
    simp [Scheme.stalkMap_germ'_assoc, Scheme.Hom.appLE]

instance {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphismRestrict
  exact PresheafedSpace.IsOpenImmersion.comp _ _

end MorphismRestrict

/-- The restriction of an open cover to an open subset. -/
@[simps! J obj map]
noncomputable
def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : X.OpenCover) (U : Opens X) :
    U.toScheme.OpenCover := by
  refine copy (𝒰.pullbackCover U.ι) 𝒰.J _ (𝒰.map · ∣_ U) (Equiv.refl _)
    (fun i ↦ IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · erw [IsOpenImmersion.range_pullback_snd_of_left U.ι (𝒰.map i)]
    rw [Opens.opensRange_ι]
    exact Subtype.range_val
  · intro i
    rw [← cancel_mono U.ι]
    simp only [morphismRestrict_ι, pullbackCover_J, Equiv.refl_apply, pullbackCover_obj,
      pullbackCover_map, Category.assoc, pullback.condition]
    erw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]

end AlgebraicGeometry
